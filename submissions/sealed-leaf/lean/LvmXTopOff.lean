/- `LvmXTopOff` (GOLF2 off-path move, group 21 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmXNtt4, LvmXDecIR4, LvmXDecCost, LvmXDec1Cost, LvmXTop,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmXNtt4
import LvmXDecIR4
import LvmXDecCost
import LvmXDec1Cost
import LvmXTop
import LvmNodeSoundCircOff
import LvmXCopyOff
import LvmXDecUdOff
import LvmXInterp4Off
import LvmXOutSegOff
import LvmXSComputesOff

-- ===== from `LvmXNtt4` =====

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb
attribute [local irreducible] entryK storeM runPrims

theorem fpairBody_nw {r : ℕ} (hr : r = rA0 ∨ r = rP2 ∨ r = rTr ∨ r = rLv ∨ r = rC1 ∨ r = rN1 ∨
    r = rC3 ∨ r = rN3 ∨ r = rKf ∨ r = rTbf) : ¬ Writes fpairBody r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide only [fpairBody, pairPs, farithIR, alphaIR, alphaBody, addK, Writes, Prim.dst, rQ,
    uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, rA0,
    rP2, rTr, rLv, rC1, rN1, rC3, rN3, rKf, rTbf, mulK_writes_iff, or_false]

/-- **One forward butterfly**: the pair's low and high elements become `u + α w` and
`u + α w + w`, `α = Σ_{i<15} [bit_i(base)] T(i)`; nothing else on the heap changes; `q += 1`. -/
theorem fpairBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {A ta l q : ℕ} {T : ℕ → BF64}
    (hl : l < 64) (hA : regs ≤ A) (hq : q < 2 ^ 64) (hhi : A + hiP l q < 2 ^ 64)
    (hsz : A + hiP l q < s.M.size) (hta : regs ≤ ta) (hta2 : ta + 15 < 2 ^ 64)
    (hQ : rd s.M rQ = toWord q) (hP2 : rd s.M rP2 = toWord (2 ^ l)) (hA0 : rd s.M rA0 = toWord A)
    (hTr : rd s.M rTr = toWord ta) (hT : ∀ i < 15, rdK s.M (ta + i) = T i) :
    rdK (semXIR I fpairBody s).M (A + loP l q) = rdK s.M (A + loP l q) +
      (∑ i ∈ range 15, if (baseP l q).testBit i then T i else 0) * rdK s.M (A + hiP l q) ∧
    rdK (semXIR I fpairBody s).M (A + hiP l q) = rdK s.M (A + loP l q) +
      (∑ i ∈ range 15, if (baseP l q).testBit i then T i else 0) * rdK s.M (A + hiP l q) +
        rdK s.M (A + hiP l q) ∧
    (∀ x, regs ≤ x → x ≠ A + loP l q → x ≠ A + hiP l q →
      rd (semXIR I fpairBody s).M x = rd s.M x) ∧
    rd (semXIR I fpairBody s).M rQ = toWord (q + 1) := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hlh := loP_lt_hiP l q
  have hP : 2 ^ l < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hl
  have hbase : baseP l q < 2 ^ 64 := by
    have : baseP l q ≤ loP l q := by simp [loP]
    omega
  -- the addresses
  have w1 : WF (.blk pairPs) := by
    simp +decide only [pairPs, WF, Prim.dst, uT1, uX, uT2, rBs, rAL, rAH]
  obtain ⟨p1, p2, p3⟩ := pairPs_sem I s hM (A := A) hq hP hQ hP2 hA0
  have hM1 := inv_sem I w1 hM
  have z1 := size_sem I (.blk pairPs) s
  have hH1 := hframe I (.blk pairPs) s (by simp +decide only [pairPs, Lo, Prim.dst, regs, uT1, uX,
    uT2, rBs, rAL, rAH])
  have q1 : rd (semXIR I (.blk pairPs) s).M rQ = toWord q := by
    rw [frame I _ s w1 hM _ (by decide) (by simp +decide only [pairPs, Writes, Prim.dst, uT1, uX,
      uT2, rBs, rAL, rAH, rQ]), hQ]
  have t1 : rd (semXIR I (.blk pairPs) s).M rTr = toWord ta := by
    rw [frame I _ s w1 hM _ (by decide) (by simp +decide only [pairPs, Writes, Prim.dst, uT1, uX,
      uT2, rBs, rAL, rAH, rTr]), hTr]
  rw [fpairBody, semXIR_seq]
  generalize semXIR I (.blk pairPs) s = s1 at p1 p2 p3 hM1 hH1 q1 t1 z1
  have hT1 : ∀ i < 15, rdK s1.M (ta + i) = T i := fun i hi => by
    rw [← hT i hi]; exact rdK_eq (hH1 _ (by simp only [regs]; omega))
  -- `α`
  have a2 := alphaIR_sem I s1 hM1 hbase (by simp only [regs]; omega) hta2 p1 t1 hT1
  have hM2 := inv_sem I wf_alphaIR hM1
  have z2 := size_sem I alphaIR s1
  have hH2 := hframeK I alphaIR s1 loK_alphaIR
  have nwA : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I alphaIR s1).M r = rd s1.M r :=
    fun r hr => frame I _ s1 wf_alphaIR hM1 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide only [alphaIR, alphaBody, Writes, Prim.dst, rBit, uT1, rTa, fG, fAl, uI, rN2,
        rC2, cTmp, rAL, rAH, rQ, or_false])
  rw [semXIR_seq]
  generalize semXIR I alphaIR s1 = s2 at a2 hM2 hH2 nwA z2
  have l2 : rd s2.M rAL = toWord (A + loP l q) := (nwA _ (.inl rfl)).trans p2
  have h2 : rd s2.M rAH = toWord (A + hiP l q) := (nwA _ (.inr (.inl rfl))).trans p3
  have q2 : rd s2.M rQ = toWord q := (nwA _ (.inr (.inr rfl))).trans q1
  have hY : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => (hH2 x hx).trans (hH1 x hx)
  -- the arithmetic
  obtain ⟨b1, b2⟩ := farith_sem I s2 hM2 (a := A + loP l q) (b := A + hiP l q)
    (by omega) (by simp only [regs]; omega) (by omega) l2 h2
  have hM3 := inv_sem I wf_farithIR hM2
  have z3 := size_sem I farithIR s2
  have hH3 := hframe I farithIR s2 lo_farithIR
  have nwB : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I farithIR s2).M r = rd s2.M r :=
    fun r hr => frame I _ s2 wf_farithIR hM2 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide only [farithIR, addK, Writes, Prim.dst, fU, fW, fH, fT, fN, rAL, rAH, rQ,
        mulK_writes_iff, or_false])
  have eU : rdK s2.M (A + loP l q) = rdK s.M (A + loP l q) :=
    rdK_eq (hY _ (by simp only [regs]; omega))
  have eW : rdK s2.M (A + hiP l q) = rdK s.M (A + hiP l q) :=
    rdK_eq (hY _ (by simp only [regs]; omega))
  rw [eU, eW, a2] at b1
  rw [eU, eW, a2] at b2
  rw [semXIR_seq]
  generalize semXIR I farithIR s2 = s3 at b1 b2 hM3 hH3 nwB z3
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

/-- **A forward level** `l < ℓ` on the row of `2^ℓ` elements at `A`, with the table row
`wRow ptK 15 l` at `ta`: every element becomes `fwdLevel`'s; the heap outside the row is kept. -/
theorem flevelIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {A ta ℓ l : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ 15) (hl : l < ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (hta : regs ≤ ta) (hta2 : ta + 15 < 2 ^ 64)
    (hdisj : ta + 15 ≤ A ∨ A + 2 ^ ℓ ≤ ta)
    (hLv : rd s.M rLv = toWord l) (hA0 : rd s.M rA0 = toWord A) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < 15, rdK s.M (ta + i) = (wRow ptK nLog l).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    (∀ i < 2 ^ ℓ, rdK (semXIR I (flevelIR ℓ) s).M (A + i) = fwdLevel ptK nLog l Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd (semXIR I (flevelIR ℓ) s).M x = rd s.M x) ∧
    (semXIR I (flevelIR ℓ) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hP1 : 2 ^ (ℓ - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hPl : l * 1 < 64 := by omega
  have w0 : WF (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))]) := by
    simp +decide only [WF, Prim.dst, rQ, rP2, rN1, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s
  have hH0 := hframe I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s (by simp +decide only [Lo, Prim.dst, regs, rQ, rP2, rN1,
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
  rw [flevelIR, semXIR_seq]
  generalize semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s = s0 at hM0 z0 hH0 r0
  obtain ⟨q0, p0, n0, a0, t0⟩ := r0
  rw [loopK_eq I fpairBody s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hP1]
  have hE : ∀ i, i ≠ rC1 → i ≠ cTmp → rd (entryK rC1 rN1 (toWord (2 ^ (ℓ - 1))) s0.M) i =
      rd s0.M i := fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC1) (n := rN1) (K := toWord (2 ^ (ℓ - 1))) hM0 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rQ = toWord j ∧ rd s'.M rP2 = toWord (2 ^ l) ∧ rd s'.M rA0 = toWord A ∧
    rd s'.M rTr = toWord ta ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdK s'.M (A + i) = if pairOf l i < j then fwdLevel ptK nLog l Y i else Y i
  have nwP : ∀ r, (r = rA0 ∨ r = rP2 ∨ r = rTr) → ∀ s', Inv s'.M →
      rd (decS rC1 (semXIR I fpairBody s')).M r = rd s'.M r := fun r hr s' hs' => by
    rw [rd_decS (by rcases hr with rfl | rfl | rfl <;> decide)]
    exact frame I _ s' wf_fpairBody hs' _ (by rcases hr with rfl | rfl | rfl <;> decide)
      (fpairBody_nw (by rcases hr with rfl | rfl | rfl <;> simp))
  have step : ∀ j s', j < 2 ^ (ℓ - 1) → P j s' →
      P (j + 1) (decS rC1 (semXIR I fpairBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    have hhi := hiP_lt hl hj
    have hlh := loP_lt_hiP l j
    have hT' : ∀ i < 15, rdK s'.M (ta + i) = (wRow ptK nLog l).getD i 0 := fun i hi => by
      rw [← hT i hi]
      exact rdK_eq (i7 _ (by simp only [regs]; omega) (by omega))
    obtain ⟨e1, e2, e3, e4⟩ := fpairBody_sem I s' i1 (A := A)
      (T := fun i => (wRow ptK nLog l).getD i 0)
      (by omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
      (by simp only [regs]; omega) hta2 i3 i4 i5 i6 hT'
    have hd : ∀ x, x ≠ rC1 → rd (decS rC1 (semXIR I fpairBody s')).M x =
        rd (semXIR I fpairBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hlo' := i8 _ (by omega : loP l j < 2 ^ ℓ)
    have hhi' := i8 _ hhi
    rw [pairOf_loP, if_neg (lt_irrefl j)] at hlo'
    rw [pairOf_hiP, if_neg (lt_irrefl j)] at hhi'
    refine ⟨inv_decS (inv_sem I wf_fpairBody i1) (by decide), by rw [size_decS, size_sem, i2], ?_,
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
        · rw [e1, hlo', hhi', fwdLevel_lo]; rfl
        · rw [e2, hlo', hhi', fwdLevel_hi]; rfl
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
  have := iterL_ind (f := semXIR I fpairBody) (c := rC1) (m := 2 ^ (ℓ - 1)) P step (2 ^ (ℓ - 1))
    0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  obtain ⟨-, z, -, -, -, -, f7, f8⟩ := this
  refine ⟨fun i hi => ?_, f7, z⟩
  rw [f8 i hi, if_pos (pairOf_lt hl hi)]

theorem flevelIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rKf ∨ r = rTbf ∨ r = rC3 ∨ r = rN3) (ℓ : ℕ) :
    ¬ Writes (flevelIR ℓ) r := by
  intro h
  simp only [flevelIR, Writes] at h
  rcases h with ⟨p, hp, he⟩ | h | h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [Prim.dst, rQ, rP2, rN1, rA0, rKf, rTbf, rC3, rN3] at he
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [rC1, rA0, rKf, rTbf, rC3, rN3] at h
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [cTmp, rA0, rKf, rTbf, rC3, rN3] at h
  · exact fpairBody_nw (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) h

theorem fPre_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ j tb : ℕ} (hj : j < ℓ)
    (hℓ : ℓ < 2 ^ 64) (hK : rd s.M rKf = toWord (ℓ - j)) (hTb : rd s.M rTbf = toWord tb) :
    rd (semXIR I (.blk fPre) s).M rLv = toWord (ℓ - 1 - j) ∧
    rd (semXIR I (.blk fPre) s).M rTr = toWord (tb + 15 * (ℓ - 1 - j)) ∧
    ∀ x, x ≠ rLv → x ≠ uT1 → x ≠ rTr → rd (semXIR I (.blk fPre) s).M x = rd s.M x := by
  have hs := hM.1
  simp only [regs] at hs
  have e1 : rd s.M cOne = toWord 1 := hM.2 0 (by decide)
  refine ⟨?_, ?_, fun x h1 h2 h3 => rd_runPrims_of_not_writes (by
    simp [fPre, Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩) _⟩
  · simp only [semXIR, runPrims, fPre, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hK, e1, sub_toWord (by omega) (by omega)]
    congr 1; omega
  · simp only [semXIR, runPrims, fPre, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hK, e1, sub_toWord (by omega) (by omega), hTb, show (15 : Word) = toWord 15 from rfl,
      mul_toWord, add_toWord]
    congr 1; rw [show ℓ - j - 1 = ℓ - 1 - j by omega]; ring

/-- **The forward NTT** (`fwdRun`) on the machine: from the row `Y` of `2^ℓ` elements at `A`
(`rA0 = A`) and the basis table at `tb` (row `v` at `tb + 15 v`), `fwdIR ℓ tb` leaves
`fwdRun ptK 15 ℓ Y` in the row and keeps the heap outside it. -/
theorem fwdIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ nLog) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64)
    (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < nLog, ∀ i < nLog, rdK s.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    (∀ i < 2 ^ ℓ, rdK (semXIR I (fwdIR ℓ tb) s).M (A + i) = fwdRun ptK nLog ℓ Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd (semXIR I (fwdIR ℓ tb) s).M x = rd s.M x) ∧
    Inv (semXIR I (fwdIR ℓ tb) s).M := by
  have hs := hM.1
  have hN : nLog = 15 := rfl
  simp only [regs] at hs hA htb
  have hℓ64 : ℓ < 2 ^ 64 := by omega
  have w0 : WF (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)]) := by
    simp +decide only [WF, Prim.dst, rKf, rTbf, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb),
    .const rN3 (toWord ℓ)]) s
  have hH0 := hframe I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb),
    .const rN3 (toWord ℓ)]) s
    (by simp +decide only [Lo, Prim.dst, regs, rKf, rTbf, rN3, List.mem_cons, List.mem_nil_iff,
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
    simp (disch := first | decide | (simp only [size_set, rKf, rTbf, rN3]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · exact hA0
  rw [fwdIR, semXIR_seq]
  generalize semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb),
    .const rN3 (toWord ℓ)]) s = s0 at hM0 z0 hH0 r0
  obtain ⟨k0, t0, n0, a0⟩ := r0
  rw [loopK_eq I (fStep ℓ) s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hℓ64]
  have hE : ∀ i, i ≠ rC3 → i ≠ cTmp → rd (entryK rC3 rN3 (toWord ℓ) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC3) (n := rN3) (K := toWord ℓ) hM0 (by decide)
  have wpre : WF (.blk fPre) := by simp +decide only [fPre, WF, Prim.dst, rLv, uT1, rTr]
  have wl : WF (flevelIR ℓ) := (wf_fwdIR ℓ tb).2.2.2.2.2.1
  have wlb : WF (.blk [.op .sub rKf rKf cOne]) := by simp +decide only [WF, Prim.dst, rKf]
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rKf = toWord (ℓ - j) ∧ rd s'.M rTbf = toWord tb ∧ rd s'.M rA0 = toWord A ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdK s'.M (A + i) = fwdTop ℓ j Y i
  have step : ∀ j s', j < ℓ → P j s' → P (j + 1) (decS rC3 (semXIR I (fStep ℓ) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨p1, p2, p3⟩ := fPre_sem I s' i1 hj hℓ64 (tb := tb) i3 i4
    have hM1 := inv_sem I wpre i1
    have hH1 := hframe I (.blk fPre) s' (by simp +decide only [fPre, Lo, Prim.dst, regs, rLv, uT1,
      rTr])
    have z1 := size_sem I (.blk fPre) s'
    rw [fStep, semXIR_seq, semXIR_seq]
    generalize semXIR I (.blk fPre) s' = s1 at p1 p2 p3 hM1 hH1 z1
    have hT : ∀ i < 15, rdK s1.M (tb + 15 * (ℓ - 1 - j) + i) =
        (wRow ptK nLog (ℓ - 1 - j)).getD i 0 := fun i hi => by
      rw [← hW (ℓ - 1 - j) (by omega) i (by omega)]
      exact rdK_eq ((hH1 _ (by simp only [regs]; omega)).trans
          (i6 _ (by simp only [regs]; omega) (by omega)))
    have hY1 : ∀ i < 2 ^ ℓ, rdK s1.M (A + i) = fwdTop ℓ j Y i := fun i hi => by
      rw [← i7 i hi]
      exact rdK_eq (hH1 _ (by simp only [regs]; omega))
    have a1 : rd s1.M rA0 = toWord A := (p3 _ (by decide) (by decide) (by decide)).trans i5
    obtain ⟨e1, e2, e3⟩ := flevelIR_sem I s1 hM1 (Y := fwdTop ℓ j Y) (l := ℓ - 1 - j) (by omega)
      (by omega) (by simp only [regs]; omega) hA2 (by omega) (by simp only [regs]; omega)
      (by omega) (by omega) p1 a1 p2 hT hY1
    have hM2 := inv_sem I wl hM1
    have nw : ∀ r, (r = rA0 ∨ r = rKf ∨ r = rTbf) →
        rd (semXIR I (flevelIR ℓ) s1).M r = rd s1.M r :=
      fun r hr => frame I _ s1 wl hM1 _ (by rcases hr with rfl | rfl | rfl <;> decide)
        (flevelIR_nw (by rcases hr with rfl | rfl | rfl <;> simp) ℓ)
    generalize semXIR I (flevelIR ℓ) s1 = s2 at e1 e2 e3 hM2 nw
    have hs2 := hM2.1
    simp only [regs] at hs2
    have hd : ∀ x, x ≠ rC3 → rd (decS rC3 (semXIR I (.blk [.op .sub rKf rKf cOne]) s2)).M x =
        rd (semXIR I (.blk [.op .sub rKf rKf cOne]) s2).M x := fun x hx => rd_decS (Ne.symm hx) _
    have hb : ∀ x, x ≠ rKf → rd (semXIR I (.blk [.op .sub rKf rKf cOne]) s2).M x = rd s2.M x :=
      fun x h1 => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm h1) _
    refine ⟨inv_decS (inv_sem I wlb hM2) (by decide), by rw [size_decS, size_sem, e3, z1, i2], ?_,
      ?_, ?_, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, rKf]; omega)) only
        [rd_set_self]
      rw [nw _ (.inr (.inl rfl)), p3 _ (by decide) (by decide) (by decide), i3,
        show rd s2.M cOne = toWord 1 from hM2.2 0 (by decide), sub_toWord (by omega) (by omega),
        show ℓ - j - 1 = ℓ - (j + 1) by omega]
    · rw [hd _ (by decide), hb _ (by decide), nw _ (.inr (.inr rfl)),
        p3 _ (by decide) (by decide) (by decide), i4]
    · rw [hd _ (by decide), hb _ (by decide), nw _ (.inl rfl), a1]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC3]; omega), hb _ (by simp only [rKf]; omega),
        e2 x (by simp only [regs]; omega) hx2, hH1 x (by simp only [regs]; omega),
        i6 x (by simp only [regs]; omega) hx2]
    · rw [rdK_eq ((hd _ (by simp only [rC3]; omega)).trans (hb _ (by simp only [rKf]; omega))),
        e1 i hi]
      rfl
  have hP0 : P 0 ⟨entryK rC3 rN3 (toWord ℓ) s0.M, s0.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), k0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only
      rw [hE _ (by simp only [rC3, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
    · dsimp only
      rw [show fwdTop ℓ 0 Y i = Y i from rfl, ← hY i hi]
      exact rdK_eq ((hE _ (by simp only [rC3]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
  have := iterL_ind (f := semXIR I (fStep ℓ)) (c := rC3) (m := ℓ) P step ℓ 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  refine ⟨fun i hi => ?_, this.2.2.2.2.2.1, this.1⟩
  rw [this.2.2.2.2.2.2 i hi, fwdRun_top ℓ Y ℓ le_rfl, Nat.sub_self]
  rfl

/-- **`Enc` on the machine**: on a message `c` of `2^m` coefficients zero-padded to the row of
`2^ℓ` elements (`m ≤ ℓ ≤ 15`), `fwdIR ℓ tb` leaves `Enc(c)` at `ptK j`, i.e. `encN ptK c j`, at
every position `j < 2^ℓ`. -/
theorem fwdIR_enc (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ m : ℕ}
    (hℓ : ℓ ≤ nLog) (hmℓ : m ≤ ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64)
    (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < nLog, ∀ i < nLog, rdK s.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0)
    (c : Fin (2 ^ m) → BF64)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = if h : i < 2 ^ m then c ⟨i, h⟩ else 0) :
    ∀ j < 2 ^ ℓ, rdK (semXIR I (fwdIR ℓ tb) s).M (A + j) = encN ptK c j := by
  intro j hj
  rw [(fwdIR_sem I s hM hℓ hA hA2 hsz htb htb2 hdisj hA0 hW
    (Y := fun i => if h : i < 2 ^ m then c ⟨i, h⟩ else 0) hY).1 j hj]
  exact fwdRun_enc ptK_xor ptK_injOn15 hmℓ hℓ c _ (fun _ => rfl) hj

end Lvm.X
end

-- ===== from `LvmXDecIR4` =====

section
section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb

/-- The table program writes neither the row pointer nor the forward NTT's registers. -/
theorem wtabIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rKf ∨ r = rTbf) (tb : ℕ) :
    ¬ Writes (wtabIR tb) r := by
  have hr12 : 12 ≤ r ∧ r ≠ fH ∧ r ≠ fN ∧ r ≠ fAl := by
    rcases hr with rfl | rfl | rfl <;> decide
  have n1 : ¬ Writes (mulK fH fU fW) r := (mulK_writes_iff (by have := hr12.1; omega) hr12.2.1).1
  have n2 : ¬ Writes (mulK fN fH fAl) r :=
    (mulK_writes_iff (by have := hr12.1; omega) hr12.2.2.1).1
  have n3 : ¬ Writes (invK fAl fH) r := (invK_writes_iff hr12.1 hr12.2.2.2).1
  simp only [wtabIR, row0IR, row0Body, rowIR, rowBody, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, n1, n2, n3]
  rcases hr with rfl | rfl | rfl <;>
  simp [rA0, rKf, rTbf, rTr, uI, rTa, rN2, rC2, fG, rLv, rN3, rC3, uT1, fU, fW, rAH, cTmp]

/-- **The table, then the inverse NTT**: the row ends holding the novel-basis coefficients of its
values. -/
theorem wtab_bflyIR_coeffs (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ nLog) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64) (hsz : A + 2 ^ ℓ ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64) (hszt : tb + 225 ≤ s.M.size)
    (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    ∀ i < 2 ^ ℓ, rdK (semXIR I (.seq (wtabIR tb) (bflyIR ℓ tb)) s).M (A + i) =
      coeffsAt ptK nLog ℓ 0 Y i := by
  have hA' : 256 ≤ A := hA
  obtain ⟨t1, t2, t3, t4⟩ := wtabIR_sem I s hM htb htb2 hszt
  rw [semXIR_seq]
  refine bflyIR_coeffs I _ t3 hℓ hA hA2 (by rw [t4]; exact hsz) htb htb2 hdisj ?_ t1 ?_
  · rw [frame I _ s (wf_wtabIR tb) hM _ (by decide) (wtabIR_nw (.inl rfl) tb), hA0]
  · intro i hi
    rw [← hY i hi]
    exact rdK_eq (t2 _ (by simp only [regs]; omega) (by omega))

/-- **The table, then the forward NTT**: on a zero-padded message the row ends holding `Enc`. -/
theorem wtab_fwdIR_enc (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ m : ℕ}
    (hℓ : ℓ ≤ nLog) (hmℓ : m ≤ ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64)
    (hszt : tb + 225 ≤ s.M.size) (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb)
    (hA0 : rd s.M rA0 = toWord A) (c : Fin (2 ^ m) → BF64)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = if h : i < 2 ^ m then c ⟨i, h⟩ else 0) :
    ∀ j < 2 ^ ℓ, rdK (semXIR I (.seq (wtabIR tb) (fwdIR ℓ tb)) s).M (A + j) = encN ptK c j := by
  have hA' : 256 ≤ A := hA
  obtain ⟨t1, t2, t3, t4⟩ := wtabIR_sem I s hM htb htb2 hszt
  rw [semXIR_seq]
  refine fwdIR_enc I _ t3 hℓ hmℓ hA hA2 (by rw [t4]; exact hsz) htb htb2 hdisj ?_ t1 c ?_
  · rw [frame I _ s (wf_wtabIR tb) hM _ (by decide) (wtabIR_nw (.inl rfl) tb), hA0]
  · intro i hi
    rw [← hY i hi]
    exact rdK_eq (t2 _ (by simp only [regs]; omega) (by omega))

/-- **The machine decodes a row** (`Lvm.Nb.decode_row`): if the row at `A` holds the interpolated
values `interpF ptK J u` on `ptK [0, 2^ℓ)` and `u` agrees with `Enc(c)` on `J` (`|J| = 2^ℓ`,
`J ⊆ [0, 2^15)`), the inverse NTT leaves the message `c` in the row. -/
theorem bflyIR_decode (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ}
    (hℓ : ℓ ≤ nLog) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64) (hsz : A + 2 ^ ℓ ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64) (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb)
    (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < nLog, ∀ i < nLog, rdK s.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0)
    {J : Finset ℕ} (hJN : ∀ i ∈ J, i < 2 ^ nLog) (hJc : J.card = 2 ^ ℓ) (c : Fin (2 ^ ℓ) → BF64)
    (u : ℕ → BF64) (hu : ∀ i ∈ J, u i = encN ptK c i)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = interpF ptK J u i) (i : Fin (2 ^ ℓ)) :
    rdK (semXIR I (bflyIR ℓ tb) s).M (A + i) = c i := by
  rw [(bflyIR_sem I s hM hℓ hA hA2 hsz htb htb2 hdisj hA0 hW hY).1 i i.2, bflyRun_coeffs]
  exact congrFun (decode_row ptK_xor ptK_injOn15 hℓ
    (fun a ha b hb h => ptK_injOn15 (hJN a ha) (hJN b hb) h) hJc c u hu) i

open CompPoly.Extension BF64 in
/-- **`C_rec`'s decoder word on the machine** (`LvmXDec.decWord`): a row holding the interpolated
values `interpF ptK (selJ wd α f₁) (rowW wd l)` on `ptK [0, 2^13)` is turned by `bflyIR 13 tb`
into the words `decWord wd α f₁ (l·2^13 + v)`, `v < 2^13`. -/
theorem bflyIR_decWord (I : Array Word) (s : St) (hM : Inv s.M) {A tb : ℕ}
    (hA : regs ≤ A) (hA2 : A + 2 ^ 13 < 2 ^ 64) (hsz : A + 2 ^ 13 ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64) (hdisj : tb + 225 ≤ A ∨ A + 2 ^ 13 ≤ tb)
    (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < nLog, ∀ i < nLog, rdK s.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0)
    (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) (l : ℕ)
    (hY : ∀ i < 2 ^ 13, rdK s.M (A + i) = interpF ptK (selJ wd α f₁).toFinset (rowW wd l) i) :
    ∀ v < 2 ^ 13, rdK (semXIR I (bflyIR 13 tb) s).M (A + v) =
      decWord wd α f₁ (l * 2 ^ 13 + v) := by
  intro v hv
  rw [bflyIR_coeffs I s hM (by decide) hA hA2 hsz htb htb2 hdisj hA0 hW hY v hv, decWord,
    show (l * 2 ^ 13 + v) / 2 ^ 13 = l by omega, show (l * 2 ^ 13 + v) % 2 ^ 13 = v by omega]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

/-- The decoder's memory layout. -/
structure DecLay (dB wB aB fB sz : ℕ) : Prop where
  r : regs ≤ dB
  t : dB + 2 ^ 21 < 2 ^ 60
  z : dB + 2 ^ 21 ≤ sz
  rW : regs ≤ wB
  tW : wB + 2 ^ 21 < 2 ^ 60
  dW : wB + 2 ^ 21 ≤ dB ∨ dB + 2 ^ 21 ≤ wB
  rA : regs ≤ aB
  tA : aB + 18 < 2 ^ 60
  dA : aB + 18 ≤ dB ∨ dB + 2 ^ 21 ≤ aB
  rF : regs ≤ fB
  tF : fB + 3 * 2 ^ 13 < 2 ^ 60
  dF : fB + 3 * 2 ^ 13 ≤ dB ∨ dB + 2 ^ 21 ≤ fB

/-- The table hypothesis of the NTTs. -/
def TabOk (M : Mem) (tb : ℕ) : Prop :=
  ∀ v < nLog, ∀ i < nLog, rdK M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0

theorem tabOk_congr {M M' : Mem} {tb : ℕ} (h : TabOk M tb)
    (hf : ∀ x, tb ≤ x → x < tb + 225 → rd M' x = rd M x) : TabOk M' tb := fun v hv i hi => by
  have : 15 * v + i < 225 := by simp only [nLog] at hv hi; omega
  simp only [rdK]; rw [hf _ (by omega) (by omega)]; exact h v hv i hi

/-- **One coordinate of `Enc₀(f₁)`.** -/
theorem encC_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB c : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hc : c < 3) (hT : TabOk s.M (tbB dB)) :
    (∀ j < 2 ^ 15, rdK (semXIR I (encC dB fB c) s).M (encB dB + c * 2 ^ 15 + j) =
      encN ptK (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < encB dB + c * 2 ^ 15 ∨ encB dB + c * 2 ^ 15 + 2 ^ 15 ≤ x) →
      rd (semXIR I (encC dB fB c) s).M x = rd s.M x) ∧
    Inv (semXIR I (encC dB fB c) s).M := by
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  set A := encB dB + c * 2 ^ 15 with hA
  have hAd : dB + 2 ^ 16 ≤ A ∧ A + 2 ^ 15 ≤ dB + 2 ^ 18 := by
    simp only [hA, encB]; constructor <;> omega
  rw [encC, semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpIR_sem I s hM (n := 2 ^ 13) (src := fB + c) (str := 3) (dst := A)
    (by norm_num) (by omega) (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
    (fun i hi => by omega) (fun i hi => by simp only [regs]; omega)
  have z1 := size_sem I (mcpIR (2 ^ 13) (fB + c) 3 A) s
  generalize semXIR I (mcpIR (2 ^ 13) (fB + c) 3 A) s = s1 at m1 m2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨n1, n2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 ^ 15 - 2 ^ 13) (dst := A + 2 ^ 13)
    (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (zeroIR (2 ^ 15 - 2 ^ 13) (A + 2 ^ 13)) s1
  generalize semXIR I (zeroIR (2 ^ 15 - 2 ^ 13) (A + 2 ^ 13)) s1 = s2 at n1 n2 hM2 z2
  rw [semXIR_seq]
  have a3 : rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M rA0 = toWord A := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rA0]; omega)]
  have k3 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M x = rd s2.M x :=
    fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, rA0]; simp only [regs] at hx; omega)
  have hM3 := inv_sem I (P := .blk [.const rA0 (toWord A)]) (by simp +decide [WF, Prim.dst, rA0]) hM2
  have z3 := size_sem I (.blk [.const rA0 (toWord A)]) s2
  generalize semXIR I (.blk [.const rA0 (toWord A)]) s2 = s3 at a3 k3 hM3 z3
  -- the heap of `s3`
  have h3 : ∀ x, regs ≤ x → (x < A ∨ A + 2 ^ 15 ≤ x) → rd s3.M x = rd s.M x := fun x hx hx2 => by
    rw [k3 x hx, n2 x hx (by omega), m2 x hx (by omega)]
  have hT3 : TabOk s3.M (tbB dB) := tabOk_congr hT fun x h1 h2 => h3 x (by simp only [regs, tbB] at *; omega)
    (by simp only [tbB] at *; omega)
  have hY : ∀ i < 2 ^ 15, rdK s3.M (A + i) =
      if h : i < 2 ^ 13 then (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) ⟨i, h⟩ else 0 := by
    intro i hi
    simp only [rdK]
    rw [k3 _ (by simp only [regs]; omega)]
    by_cases h : i < 2 ^ 13
    · rw [dif_pos h, n2 _ (by simp only [regs]; omega) (by omega), m1 i h]
      congr 2; ring
    · rw [dif_neg h, show A + i = A + 2 ^ 13 + (i - 2 ^ 13) by omega, n1 _ (by omega)]; rfl
  have hfe := fwdIR_enc I s3 hM3 (A := A) (tb := tbB dB) (ℓ := 15) (m := 13) (by decide) (by norm_num)
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega) a3 hT3
    (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) hY
  obtain ⟨-, f2, f3⟩ := fwdIR_sem I s3 hM3 (A := A) (tb := tbB dB) (ℓ := 15) (Y := fun i => rdK s3.M (A + i))
    (by decide) (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega) a3 hT3 (fun i _ => rfl)
  exact ⟨hfe, fun x hx hx2 => (f2 x hx hx2).trans (h3 x hx hx2), f3⟩

/-- **`Enc₀(f₁)`'s three coordinates** at `encB + c·2^15 + j`. -/
theorem encIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hT : TabOk s.M (tbB dB)) :
    (∀ c < 3, ∀ j < 2 ^ 15, rdK (semXIR I (encIR dB fB) s).M (encB dB + c * 2 ^ 15 + j) =
      encN ptK (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < encB dB ∨ encB dB + 3 * 2 ^ 15 ≤ x) →
      rd (semXIR I (encIR dB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (encIR dB fB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  simp only [regs] at r rF
  rw [encIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := encC_sem I s hM hL (c := 0) (by norm_num) hT
  have z1 := size_sem I (encC dB fB 0) s
  generalize semXIR I (encC dB fB 0) s = s1 at a1 a2 hM1 z1
  have hL1 : DecLay dB wB aB fB s1.M.size := by rw [z1]; exact hL
  have hF1 : ∀ x, regs ≤ x → (x < encB dB ∨ encB dB + 2 ^ 15 ≤ x) → rd s1.M x = rd s.M x :=
    fun x hx hx2 => a2 x hx (by simpa using hx2)
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 =>
    hF1 x (by simp only [regs, tbB] at *; omega) (by simp only [tbB, encB] at *; omega)
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := encC_sem I s1 hM1 hL1 (c := 1) (by norm_num) hT1
  have z2 := size_sem I (encC dB fB 1) s1
  generalize semXIR I (encC dB fB 1) s1 = s2 at b1 b2 hM2 z2
  have hL2 : DecLay dB wB aB fB s2.M.size := by rw [z2]; exact hL1
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 =>
    b2 x (by simp only [regs, tbB] at *; omega) (by simp only [tbB, encB] at *; omega)
  obtain ⟨c1, c2, hM3⟩ := encC_sem I s2 hM2 hL2 (c := 2) (by norm_num) hT2
  have hfB : ∀ x c, x < 2 ^ 13 → c < 3 → regs ≤ fB + 3 * x + c ∧
      (fB + 3 * x + c < encB dB ∨ encB dB + 3 * 2 ^ 15 ≤ fB + 3 * x + c) := fun x c hx hc => by
    simp only [regs, encB] at *; omega
  have e1 : ∀ x : Fin (2 ^ 13), ∀ c < 3, rdK s1.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [a2 _ h1 (by omega)]
  have e2 : ∀ x : Fin (2 ^ 13), ∀ c < 3, rdK s2.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [b2 _ h1 (by omega)]; exact e1 x c hc
  refine ⟨fun c hc j hj => ?_, fun x hx hx2 => ?_, hM3⟩
  · interval_cases c
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, encB] at *; omega) (by simp only [encB] at *; omega),
        b2 _ (by simp only [regs, encB] at *; omega) (by simp only [encB] at *; omega)]
      exact a1 j hj
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, encB] at *; omega) (by simp only [encB] at *; omega)]
      rw [show wK (rd s2.M (encB dB + 1 * 2 ^ 15 + j)) = rdK s2.M (encB dB + 1 * 2 ^ 15 + j) from rfl,
        b1 j hj]
      congr 1; funext x; exact e1 x 1 (by norm_num)
    · rw [c1 j hj]
      congr 1; funext x; exact e2 x 2 (by norm_num)
  · rw [c2 x hx (by omega), b2 x hx (by omega), a2 x hx (by omega)]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

/-- **The inverse NTT of the 64 rows** at `oB`. -/
theorem bflyAll_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hT : TabOk s.M (tbB dB)) (Y : ℕ → ℕ → BF64)
    (hY : ∀ t < 64, ∀ i < 2 ^ 13, rdK s.M (oB dB + t * 2 ^ 13 + i) = Y t i) :
    (∀ t < 64, ∀ i < 2 ^ 13, rdK (semXIR I (bflyAll dB) s).M (oB dB + t * 2 ^ 13 + i) =
      coeffsAt ptK nLog 13 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < oB dB ∨ oB dB + 2 ^ 19 ≤ x) → rd (semXIR I (bflyAll dB) s).M x = rd s.M x) ∧
    Inv (semXIR I (bflyAll dB) s).M := by
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL
  have hs := hM.1
  simp only [regs] at r hs
  rw [bflyAll, semXIR_seq]
  have w0 : WF (.blk [.const zT 0, .const zN 64]) := by simp +decide [WF, Prim.dst, zT, zN]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const zT 0, .const zN 64]) s
  have r0 : rd (semXIR I (.blk [.const zT 0, .const zN 64]) s).M zT = toWord 0 ∧
      rd (semXIR I (.blk [.const zT 0, .const zN 64]) s).M zN = toWord 64 := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zT, zN]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const zT 0, .const zN 64]) s).M x = rd s.M x :=
    fun x hx => rd_blk_of_not_dst I _ s (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, zT, zN] <;> simp only [regs] at hx <;> omega)
  generalize semXIR I (.blk [.const zT 0, .const zN 64]) s = s0 at hM0 z0 r0 k0
  obtain ⟨t0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M zT = toWord j ∧
    (∀ t < j, ∀ i < 2 ^ 13, rdK s'.M (oB dB + t * 2 ^ 13 + i) = coeffsAt ptK nLog 13 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < oB dB ∨ oB dB + j * 2 ^ 13 ≤ x) → rd s'.M x = rd s.M x)
  have hoB : oB dB = dB + 2 ^ 19 := rfl
  have hE : ∀ i, i ≠ zC → i ≠ cTmp → rd (entryK zC zN (toWord 64) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK zC zN (toWord 64) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun t ht => absurd ht (by omega), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), t0]
    · simp only [regs] at hx
      rw [hE _ (by simp only [zC]; omega) (by simp only [cTmp]; omega), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 64 → P j s' → P (j + 1) (decS zC (semXIR I (bflyRow dB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    rw [bflyRow, semXIR_seq]
    set A := oB dB + j * 2 ^ 13 with hA
    have hs' := i1.1
    simp only [regs] at hs'
    have a1 : rd (semXIR I (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
        .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s').M rA0 = toWord A := by
      rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, zK, rA0, zT]; omega)) only [rd_set_self, rd_set_ne]
      rw [i3, mul_toWord, add_toWord, hA, Nat.add_comm]
    have a2 : ∀ x, x ≠ zK → x ≠ rA0 → rd (semXIR I (.blk [.const zK (toWord (2 ^ 13)),
        .op .mul rA0 zT zK, .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s').M x = rd s'.M x :=
      fun x h1 h2 => rd_blk_of_not_dst I _ s' (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Prim.dst]
        exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h1, Ne.symm h2⟩)
    have hM1 := inv_sem I (P := .blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
      .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) (by simp +decide [WF, Prim.dst, zK, rA0]) i1
    have z1 := size_sem I (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
      .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s'
    generalize semXIR I (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
      .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s' = s1 at a1 a2 hM1 z1
    rw [semXIR_seq]
    have hAv : A = dB + 2 ^ 19 + j * 2 ^ 13 := by simp only [hA, oB]
    have hx1 : ∀ x, regs ≤ x → x ≠ zK ∧ x ≠ rA0 := fun x hx => by
      simp only [regs, zK, rA0] at *; omega
    have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s'.M x := fun x hx => a2 x (hx1 x hx).1 (hx1 x hx).2
    have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x hx1' hx2' => by
      simp only [tbB] at hx1' hx2'
      rw [h1 x (by simp only [regs]; omega)]
      exact i5 x (by simp only [regs]; omega) (by omega)
    have hY1 : ∀ i < 2 ^ 13, rdK s1.M (A + i) = Y j i := fun i hi => by
      simp only [rdK]
      rw [h1 _ (by simp only [regs]; omega), hAv,
        show dB + 2 ^ 19 + j * 2 ^ 13 + i = oB dB + j * 2 ^ 13 + i by rw [hoB],
        i5 _ (by simp only [regs, hoB] at *; omega) (Or.inr (by omega))]
      exact hY j hj i hi
    have hjb : j * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ 19 := by omega
    obtain ⟨-, b2, hM2⟩ := bflyIR_sem I s1 hM1 (A := A) (tb := tbB dB) (ℓ := 13) (Y := Y j) (by decide)
      (by simp only [regs, hA, oB]; omega) (by simp only [hA, oB]; omega)
      (by simp only [hA, oB]; omega) (by simp only [regs, tbB]; omega) (by simp only [tbB]; omega)
      (by simp only [tbB, hA, oB]; omega) a1 hT1 hY1
    have b1 := bflyIR_coeffs I s1 hM1 (A := A) (tb := tbB dB) (ℓ := 13) (Y := Y j) (by decide)
      (by simp only [regs, hA, oB]; omega) (by simp only [hA, oB]; omega)
      (by simp only [hA, oB]; omega) (by simp only [regs, tbB]; omega) (by simp only [tbB]; omega)
      (by simp only [tbB, hA, oB]; omega) a1 hT1 hY1
    have q2 : rd (semXIR I (bflyIR 13 (tbB dB)) s1).M zT = toWord j := by
      rw [frame I _ s1 (by simp +decide [bflyIR, lvlStep, levelIR, pairBody, pairPs, alphaIR,
        alphaBody, arithIR, addK, mulK, mulKC, redC, WF, Writes, Prim.dst, rLv, rTr, rN3, rC3, rQ,
        rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI, rTa, rN2, rC2, fAl, fG, fU, fW,
        fH, fT, fN, cTmp, regs]) hM1 zT (by decide) (bflyIR_nw_hi 13 _ (by decide)),
        a2 _ (by decide) (by decide), i3]
    have z2 := size_sem I (bflyIR 13 (tbB dB)) s1
    generalize semXIR I (bflyIR 13 (tbB dB)) s1 = s2 at b1 b2 hM2 q2 z2
    have hd : ∀ x, x ≠ zC → rd (decS zC (semXIR I (.blk [.op .add zT zT cOne]) s2)).M x =
        rd (semXIR I (.blk [.op .add zT zT cOne]) s2).M x := fun x hx => rd_decS (Ne.symm hx) _
    have c2 : ∀ x, x ≠ zT → rd (semXIR I (.blk [.op .add zT zT cOne]) s2).M x = rd s2.M x :=
      fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact Ne.symm hx)
    have hM3 := inv_sem I (P := .blk [.op .add zT zT cOne]) (by simp +decide [WF, Prim.dst, zT]) hM2
    have hx3 : ∀ x, regs ≤ x → x ≠ zC ∧ x ≠ zT := fun x hx => by
      simp only [regs, zC, zT] at *; omega
    refine ⟨inv_decS hM3 (by decide), by rw [size_decS, size_sem, z2, z1, i2], ?_,
      fun t ht i hi => ?_, fun x hx hx2 => ?_⟩
    · have hs2 := hM2.1
      simp only [regs] at hs2
      rw [hd _ (by decide), sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [zT]; omega), q2, show rd s2.M cOne = 1 from hM2.2 0 (by decide),
        add_one_toWord]
    · have hxr : regs ≤ oB dB + t * 2 ^ 13 + i := by simp only [regs, oB] at *; omega
      simp only [rdK]
      rw [hd _ (hx3 _ hxr).1, c2 _ (hx3 _ hxr).2]
      by_cases htj : t = j
      · subst htj; exact b1 i hi
      · have ht' : t < j := by omega
        have : t * 2 ^ 13 + 2 ^ 13 ≤ j * 2 ^ 13 := by nlinarith
        rw [b2 _ hxr (by left; omega), h1 _ hxr]
        exact i4 t ht' i hi
    · have e : (j + 1) * 2 ^ 13 = j * 2 ^ 13 + 2 ^ 13 := by ring
      rw [e] at hx2
      have hx4 : x < A ∨ A + 2 ^ 13 ≤ x := by
        rcases hx2 with h | h
        · exact Or.inl (Nat.lt_of_lt_of_le h (Nat.le_add_right (oB dB) (j * 2 ^ 13)))
        · rw [← Nat.add_assoc] at h; exact Or.inr h
      have hx5 : x < oB dB ∨ oB dB + j * 2 ^ 13 ≤ x := by
        rcases hx2 with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans (by rw [← Nat.add_assoc]; exact Nat.le_add_right _ _) h)
      rw [hd _ (hx3 x hx).1, c2 _ (hx3 x hx).2, b2 x hx hx4, h1 x hx, i5 x hx hx5]
  have hfin := loopK_run I (bflyRow dB) P s0 hM0 (c := zC) (n := zN) (K := 64) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, fun x hx hx2 => hfin.2.2.2.2 x hx
    (by rw [show 64 * 2 ^ 13 = 2 ^ 19 by norm_num]; exact hx2), hfin.1⟩

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

theorem decWord_split (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) {l v : ℕ} (hv : v < 2 ^ 13) :
    decWord wd α f₁ (l * 2 ^ 13 + v) =
      coeffsAt ptK nLog 13 0 (interpF ptK (selJ wd α f₁).toFinset (rowW wd l)) v := by
  rw [decWord]
  have h1 : (l * 2 ^ 13 + v) / 2 ^ 13 = l := by omega
  have h2 : (l * 2 ^ 13 + v) % 2 ^ 13 = v := by omega
  rw [h1, h2]

/-- **The decoding proper**: on a list of `≥ 2^13` agreeing positions at `agB`, the message of
`decodeRec` at `mB`. -/
theorem decTail_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hT : TabOk s.M (tbB dB)) (wd : ℕ → ℕ → BF64)
    (α f₁ : ℕ → Ext3) (hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hlen : 2 ^ 13 ≤ (agreeL wd α f₁).length)
    (hJ : ∀ t < 2 ^ 13, rd s.M (agB dB + t) = toWord ((agreeL wd α f₁).getD t 0)) :
    (∀ i < 2 ^ 19, rdK (semXIR I (decTail dB wB) s).M (mB dB + i) = decWord wd α f₁ i) ∧
    (∀ x, regs ≤ x → (x < dB + 2 ^ 13 ∨ dB + 2 ^ 21 ≤ x) →
      rd (semXIR I (decTail dB wB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decTail dB wB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  simp only [regs] at r rW
  set Jl := selJ wd α f₁ with hJl
  have hJlen : Jl.length = 2 ^ 13 := by
    rw [hJl, selJ, List.length_take, Nat.min_eq_left hlen]
  have hJnd : Jl.Nodup := (nodup_agreeL wd α f₁).sublist (List.take_sublist _ _)
  have hJlt : ∀ j ∈ Jl, j < 2 ^ 15 := fun j hj => (mem_agreeL.1 (List.mem_of_mem_take hj)).1
  have hBL : BaryLay (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB) s.M.size := by
    refine ⟨by norm_num, le_rfl, ?_, ?_, ?_, ?_, rW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [regs, agB, wbB, ebB, oB]) <;> omega
  rw [decTail, semXIR_seq]
  obtain ⟨b1, b2, hM1⟩ := baryIR_lvm I s hM (Jl := Jl) hJlen hJnd hJlt hBL (fun t ht => by
    rw [hJ t ht, hJl, selJ, getD_take_lt ht])
  have z1 := size_sem I (baryIR (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB)) s
  generalize semXIR I (baryIR (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB)) s = s1
    at b1 b2 hM1 z1
  have hL1 : DecLay dB wB aB fB s1.M.size := by rw [z1]; exact hL
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact b2 x (by simp only [regs]; omega) (by simp only [wbB]; omega) (by simp only [ebB]; omega)
      (by simp only [oB]; omega)
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := bflyAll_sem I s1 hM1 hL1 hT1 (fun t i => rdK s1.M (oB dB + t * 2 ^ 13 + i))
    (fun _ _ _ _ => rfl)
  have z2 := size_sem I (bflyAll dB) s1
  generalize semXIR I (bflyAll dB) s1 = s2 at c1 c2 hM2 z2
  obtain ⟨d1, d2, hM3⟩ := rowsIR_sem I s2 hM2 (oB := oB dB) (mB := mB dB)
    (by simp only [regs, oB]; omega) (by simp only [oB]; omega) (by simp only [regs, mB]; omega)
    (by simp only [mB]; omega) (by rw [z2, z1]; simp only [mB]; omega)
    (by simp only [oB, mB]; omega)
  refine ⟨fun i hi => ?_, fun x hx hx2 => ?_, hM3⟩
  · -- the message word
    have hl : i / 2 ^ 13 < 64 := by omega
    have hv : i % 2 ^ 13 < 2 ^ 13 := Nat.mod_lt _ (by norm_num)
    have hi' : mB dB + i = mB dB + i / 2 ^ 13 * 2 ^ 13 + i % 2 ^ 13 := by
      have := Nat.div_add_mod' i (2 ^ 13); omega
    set l := i / 2 ^ 13
    set v := i % 2 ^ 13
    have ht : 63 - l < 64 := by omega
    simp only [rdK]
    rw [hi', d1 l hl v hv]
    rw [show wK (rd s2.M (oB dB + (63 - l) * 2 ^ 13 + v)) = rdK s2.M (oB dB + (63 - l) * 2 ^ 13 + v)
      from rfl, c1 (63 - l) ht v hv, show i = l * 2 ^ 13 + v by omega, decWord_split wd α f₁ hv]
    refine coeffsAt_congr ptK nLog 13 0 _ _ (fun j hj => ?_) v hv
    rw [show oB dB + (63 - l) * 2 ^ 13 + j = oB dB + 2 ^ 13 * (63 - l) + j by ring, b1 j hj _ ht]
    refine interpF_congr ptK _ (fun q hq => ?_) j
    have hq' := hJlt q (List.mem_toFinset.1 hq)
    rw [hW q hq' _ ht, rowW]
  · simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega) (by simp only [mB]; omega),
      c2 x (by simp only [regs]; omega) (by simp only [oB]; omega),
      b2 x (by simp only [regs]; omega) (by simp only [wbB]; omega) (by simp only [ebB]; omega)
        (by simp only [oB]; omega)]

end Lvm.X
end
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

/-- **The flag**: `rOk = okB`'s cell `= [2^13 ≤ cnt]`. -/
theorem okIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB n : ℕ} (hdB : regs ≤ dB)
    (hdB2 : okB dB < 2 ^ 64) (hdBs : okB dB < s.M.size) (hn : n < 2 ^ 64)
    (hC : rd s.M gCnt = toWord n) :
    rd (semXIR I (okIR dB) s).M rOk = bW (decide (2 ^ 13 ≤ n)) ∧
    rd (semXIR I (okIR dB) s).M (okB dB) = bW (decide (2 ^ 13 ≤ n)) ∧
    (∀ x, regs ≤ x → x ≠ okB dB → rd (semXIR I (okIR dB) s).M x = rd s.M x) ∧
    Inv (semXIR I (okIR dB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdB
  rw [okIR, semXIR_seq]
  set ps : List Prim := [.const zK (toWord (2 ^ 13)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (okB dB))] with hps
  have hM1 := inv_sem I (P := .blk ps) (by simp +decide [hps, WF, Prim.dst, zK, rOk]) hM
  have v1 : rd (semXIR I (.blk ps) s).M rOk = bW (decide (2 ^ 13 ≤ n)) ∧
      rd (semXIR I (.blk ps) s).M zK = toWord (okB dB) := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zK, rOk]; omega)) only [rd_set_self, rd_set_ne]
    rw [hC, ltW_toWord hn (by norm_num), show rd s.M cOne = 1 from hM.2 0 (by decide), eval_xor,
      bW_xor_one]
    congr 1
    rw [← decide_not]
    simp only [Nat.not_lt]
  have k1 : ∀ x, regs ≤ x → rd (semXIR I (.blk ps) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, zK, rOk] <;> omega
  have z1 := size_sem I (.blk ps) s
  generalize semXIR I (.blk ps) s = s1 at hM1 v1 k1 z1
  obtain ⟨st1, st2, hM2⟩ := store_sem I s1 hM1 (p := zK) (v := rOk) (x := okB dB) (by decide)
    (by decide) v1.2 (by simp only [regs, okB]; omega) hdB2 (by omega)
  refine ⟨?_, by rw [st1, v1.1], fun x hx hx2 => by
    rw [st2 x hx2 (by simp only [regs, cTmp] at *; omega), k1 x hx], hM2⟩
  rw [st2 _ (by simp only [rOk, okB]; omega) (by decide), v1.1]

/-- **The decoder computes `decodeRec`.** -/
theorem decIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hA : ∀ i < 6, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 13, rdE s.M (fB + 3 * v) = f₁ v) :
    rd (semXIR I (decIR dB wB aB fB) s).M (okB dB) =
      bW (decide (2 ^ 13 ≤ (agreeL wd α f₁).length)) ∧
    (∀ out, decodeRec wd α f₁ = some out →
      ∀ i < 2 ^ 19, rdK (semXIR I (decIR dB wB aB fB) s).M (mB dB + i) = out.getD i 0) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 21 ≤ x) →
      rd (semXIR I (decIR dB wB aB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decIR dB wB aB fB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  -- 1. the basis table
  rw [decIR, semXIR_seq]
  obtain ⟨w1, w2, hM1, z1⟩ := wtabIR_sem I s hM (tb := tbB dB) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega)
  generalize semXIR I (wtabIR (tbB dB)) s = s1 at w1 w2 hM1 z1
  have hT1 : TabOk s1.M (tbB dB) := w1
  -- 2. the `eq` table
  rw [semXIR_seq]
  obtain ⟨q1, q2, hM2⟩ := eqtIR_eqA I s1 hM1 (aB := aB) (qB := qB dB) (by simp only [regs]; omega)
    (by omega) (by simp only [regs, qB]; omega) (by simp only [qB]; omega)
    (by rw [z1]; simp only [qB]; omega) (by simp only [qB]; omega)
  have z2 := size_sem I (eqtIR 6 aB (qB dB)) s1
  generalize semXIR I (eqtIR 6 aB (qB dB)) s1 = s2 at q1 q2 hM2 z2
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact q2 x (by simp only [regs]; omega) (by simp only [qB]; omega)
  have hQ2 : ∀ l < 64, rdE s2.M (qB dB + 3 * l) = eqA α l := fun l hl => by
    rw [q1 l hl]
    refine eqA_congr (fun i hi => ?_) l
    rw [← hA i hi]
    exact rdE_congr fun k hk => w2 _ (by simp only [regs]; omega) (by simp only [tbB]; omega)
  -- the inputs outside the workspace are kept by every phase
  have hL2 : DecLay dB wB aB fB s2.M.size := by rw [z2, z1]; exact hL
  -- 3. `Enc₀(f₁)`
  rw [semXIR_seq]
  obtain ⟨e1, e2, hM3⟩ := encIR_sem I s2 hM2 hL2 hT2
  have z3 := size_sem I (encIR dB fB) s2
  generalize semXIR I (encIR dB fB) s2 = s3 at e1 e2 hM3 z3
  have hout : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 21 ≤ x) → rd s2.M x = rd s.M x := fun x hx hx2 => by
    rw [q2 x hx (by simp only [qB]; omega), w2 x hx (by simp only [tbB]; omega)]
  have hfB : ∀ v < 2 ^ 13, ∀ c < 3, rdK s2.M (fB + 3 * v + c) = rdK s.M (fB + 3 * v + c) :=
    fun v hv c hc => by simp only [rdK]; rw [hout _ (by simp only [regs]; omega) (by omega)]
  have hW3 : ∀ q < 2 ^ 15, ∀ t < 64, rdK s3.M (wB + 64 * q + t) = wd q t := fun q hq t ht => by
    rw [← hW q hq t ht]; simp only [rdK]
    rw [e2 _ (by simp only [regs]; omega) (by simp only [encB]; omega),
      hout _ (by simp only [regs]; omega) (by omega)]
  have hQ3 : ∀ l < 64, rdE s3.M (qB dB + 3 * l) = eqA α l := fun l hl => by
    rw [← hQ2 l hl]
    exact rdE_congr fun k hk => e2 _ (by simp only [regs, qB]; omega) (by simp only [qB, encB]; omega)
  have hE3 : ∀ q < 2 ^ 15, enc0 f₁ q = mkE (rdK s3.M (encB dB + q)) (rdK s3.M (encB dB + 2 ^ 15 + q))
      (rdK s3.M (encB dB + 2 * 2 ^ 15 + q)) := fun q hq => by
    rw [enc0_coords f₁ (fun c v => rdK s.M (fB + 3 * v + c)) (fun v hv => by rw [← hF v hv]; rfl) q]
    have hc : ∀ c < 3, encN ptK (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) q =
        rdK s3.M (encB dB + c * 2 ^ 15 + q) := fun c hc => by
      rw [e1 c hc q hq]
      exact congrArg (fun g => encN ptK g q) (funext fun x => (hfB x x.isLt c hc).symm)
    rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), Nat.zero_mul, Nat.add_zero,
      Nat.one_mul]
  have hAg : agreeM s3.M wB (qB dB) (encB dB) (2 ^ 15) = agreeL wd α f₁ :=
    agreeM_eq_agreeL wd α f₁ hW3 hQ3 hE3
  -- 4. the agreement scan
  rw [semXIR_seq]
  obtain ⟨g1, g2, g3, hM4⟩ := agreeIR_sem I s3 hM3 (wB := wB) (qB := qB dB) (eB := encB dB)
    (agB := agB dB) (by simp only [regs]; omega) (by omega) (by simp only [regs, qB]; omega)
    (by simp only [qB]; omega) (by simp only [regs, encB]; omega) (by simp only [encB]; omega)
    (by simp only [regs, agB]; omega) (by simp only [agB]; omega)
    (by rw [z3, z2, z1]; simp only [agB]; omega)
    ⟨by simp only [agB]; omega, by simp only [agB, qB]; omega, by simp only [agB, encB]; omega⟩
  rw [hAg] at g1 g2
  have z4 := size_sem I (agreeIR wB (qB dB) (encB dB) (agB dB)) s3
  generalize semXIR I (agreeIR wB (qB dB) (encB dB) (agB dB)) s3 = s4 at g1 g2 g3 hM4 z4
  have hlen64 : (agreeL wd α f₁).length < 2 ^ 64 := by
    have : (agreeL wd α f₁).length ≤ 2 ^ 15 := by
      rw [agreeL]; exact (List.length_filter_le _ _).trans (by simp)
    omega
  -- 5. the flag
  rw [semXIR_seq]
  obtain ⟨o1, o2, o3, hM5⟩ := okIR_sem I s4 hM4 (dB := dB) (n := (agreeL wd α f₁).length)
    (by simp only [regs]; omega) (by simp only [okB]; omega)
    (by rw [z4, z3, z2, z1]; simp only [okB]; omega) hlen64 g1
  have z5 := size_sem I (okIR dB) s4
  generalize semXIR I (okIR dB) s4 = s5 at o1 o2 o3 hM5 z5
  -- the heap of `s5`
  have hT5 : TabOk s5.M (tbB dB) := tabOk_congr hT2 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    rw [o3 x (by simp only [regs]; omega) (by simp only [okB]; omega),
      g3 x (by simp only [regs]; omega) (by simp only [agB]; omega),
      e2 x (by simp only [regs]; omega) (by simp only [encB]; omega)]
  have h5 : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 21 ≤ x) → rd s5.M x = rd s.M x := fun x hx hx2 => by
    rw [o3 x hx (by simp only [okB]; omega), g3 x hx (by simp only [agB]; omega),
      e2 x hx (by simp only [encB]; omega), hout x hx hx2]
  -- 6. the branch
  rw [semXIR_ite, o1]
  by_cases hk : 2 ^ 13 ≤ (agreeL wd α f₁).length
  · rw [decide_eq_true hk, if_neg bW_true_ne]
    have hL5 : DecLay dB wB aB fB s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hL
    have hW5 : ∀ q < 2 ^ 15, ∀ t < 64, rdK s5.M (wB + 64 * q + t) = wd q t := fun q hq t ht => by
      rw [← hW q hq t ht]; simp only [rdK]; rw [h5 _ (by simp only [regs]; omega) (by omega)]
    have hJ5 : ∀ t < 2 ^ 13, rd s5.M (agB dB + t) = toWord ((agreeL wd α f₁).getD t 0) := fun t ht => by
      rw [o3 _ (by simp only [regs, agB]; omega) (by simp only [agB, okB]; omega), g2 t (by omega)]
    obtain ⟨d1, d2, hM6⟩ := decTail_sem I s5 hM5 hL5 hT5 wd α f₁ hW5 hk hJ5
    refine ⟨?_, fun out hout' i hi => ?_, fun x hx hx2 => ?_, hM6⟩
    · rw [d2 _ (by simp only [regs, okB]; omega) (by simp only [okB]; omega), o2, decide_eq_true hk]
    · rw [decodeRec, if_pos hk, Option.some.injEq] at hout'
      rw [← hout', d1 i hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getElem_range]
    · rw [d2 x hx (by omega), h5 x hx hx2]
  · rw [decide_eq_false hk, if_pos bW_false_eq]
    have e6 : semXIR I (.blk []) s5 = s5 := by cases s5; rfl
    rw [e6]
    refine ⟨by rw [o2, decide_eq_false hk], fun out hout' => ?_, h5, hM5⟩
    rw [decodeRec, if_neg hk] at hout'
    exact absurd hout' (by simp)

end Lvm.X
end

-- ===== from `LvmXDecCost` =====

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

/-- **The column reads and the decoder, with the memory, are below `2^38`.** -/
theorem decode_fixed_le (bX pL capW wB dB aB fB t : ℕ) :
    memX + cost (readIR bX pL capW wB) t + cost (decIR dB wB aB fB) t ≤ 2 ^ 38 := by
  rw [(cost_readIR bX pL capW wB t).2, cost_decIR, memX]; norm_num

/-- The declared `fuel_base = 2^46` covers them with a factor `2^8`. -/
theorem decode_fuel_margin (bX pL capW wB dB aB fB t : ℕ) :
    2 ^ 8 * (memX + cost (readIR bX pL capW wB) t + cost (decIR dB wB aB fB) t) ≤ fuelBase := by
  have := decode_fixed_le bX pL capW wB dB aB fB t
  rw [fuelBase]; omega

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

theorem hasOut_decIR (dB wB aB fB : ℕ) : hasOut (decIR dB wB aB fB) = false := rfl

theorem hasOut_readIR (bX pL capW wB : ℕ) : hasOut (readIR bX pL capW wB) = false := rfl

/-- **`decIR` writes no output.** -/
theorem decIR_o (I : Array Word) (s : St) (dB wB aB fB : ℕ) :
    (semXIR I (decIR dB wB aB fB) s).o = s.o := sem_o I _ s (hasOut_decIR dB wB aB fB)

/-- **`readIR` writes no output.** -/
theorem readIR_o (I : Array Word) (s : St) (bX pL capW wB : ℕ) :
    (semXIR I (readIR bX pL capW wB) s).o = s.o := sem_o I _ s (hasOut_readIR bX pL capW wB)

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

/-- **`decodeRec_correct` is not vacuous**: the zero word with `α = 0`, `f₁ = 0` meets its
hypotheses (every position is close, `f₁` is the fold, no position is lucky) and decodes to the
zero message. -/
theorem decodeRec_correct_zero :
    decodeRec (fun _ _ => 0) (fun _ => 0) (fun _ => 0) = some ((List.range (2 ^ 19)).map fun _ => 0) := by
  have hcw : ∀ l q, cwRec (fun _ => (0 : BF64)) l q = 0 := fun l q => by simp [cwRec]
  refine decodeRec_correct _ _ _ (fun _ => 0) ?_ ?_ ?_
  · have : closeSet (fun _ _ => (0 : BF64)) (fun _ => 0) = range (2 ^ 15) := by
      ext q; simp [closeSet, rowW, hcw]
    rw [this, card_range]; norm_num
  · intro v _; simp
  · intro q _ _ l _; simp [rowW, hcw]

/-- **A layout exists** below `memX = 2^25`: the workspace at `2^22`, the word at `2^20`, `α` and
`f₁` at `2^19`. -/
theorem decLay_example (sz : ℕ) (hsz : 2 ^ 25 ≤ sz) :
    DecLay (2 ^ 22) (2 ^ 20) (2 ^ 19) (2 ^ 19 + 64) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [regs]) <;> omega

end Lvm.X
end

-- ===== from `LvmXDec1Cost` =====

section
section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb
attribute [local irreducible] entryK storeM

/-- **The level-1 decoder's memory layout**: the workspace `[d1B, d1B + 2^16)` inside the memory;
the word (`w1B`, read over `48·2^15` words by the interpolation's layout `BaryLay`), `α₁` (`a1B`,
12 words) and `f₂` (`f2B`, `3·2^9` words) outside it; the output (`oB`, `3·2^13` words) inside the
memory and outside the workspace; every address below `2^60`. -/
structure Dec1Lay (dB wB aB fB oB sz : ℕ) : Prop where
  r : regs ≤ dB
  t : dB + 2 ^ 16 < 2 ^ 60
  z : dB + 2 ^ 16 ≤ sz
  rW : regs ≤ wB
  tW : wB + 48 * 2 ^ 15 < 2 ^ 60
  dW : wB + 48 * 2 ^ 15 ≤ dB ∨ dB + 2 ^ 16 ≤ wB
  rA : regs ≤ aB
  tA : aB + 12 < 2 ^ 60
  dA : aB + 12 ≤ dB ∨ dB + 2 ^ 16 ≤ aB
  rF : regs ≤ fB
  tF : fB + 3 * 2 ^ 9 < 2 ^ 60
  dF : fB + 3 * 2 ^ 9 ≤ dB ∨ dB + 2 ^ 16 ≤ fB
  rO : regs ≤ oB
  tO : oB + 3 * 2 ^ 13 < 2 ^ 60
  zO : oB + 3 * 2 ^ 13 ≤ sz
  dO : oB + 3 * 2 ^ 13 ≤ dB ∨ dB + 2 ^ 16 ≤ oB

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb
attribute [local irreducible] entryK storeM

/-- **One coordinate of `Enc₁(f₂)`.** -/
theorem enc1C_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB c : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (hc : c < 3) (hT : TabOk s.M (tbB dB)) :
    (∀ j < 2 ^ 12, rdK (semXIR I (enc1C dB fB c) s).M (enc1B dB + c * 2 ^ 12 + j) =
      encN ptK (fun x : Fin (2 ^ 9) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < enc1B dB + c * 2 ^ 12 ∨ enc1B dB + c * 2 ^ 12 + 2 ^ 12 ≤ x) →
      rd (semXIR I (enc1C dB fB c) s).M x = rd s.M x) ∧
    Inv (semXIR I (enc1C dB fB c) s).M := by
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  set A := enc1B dB + c * 2 ^ 12 with hA
  have hAd : dB + 2 ^ 13 ≤ A ∧ A + 2 ^ 12 ≤ dB + 2 ^ 15 := by
    simp only [hA, enc1B]; constructor <;> omega
  rw [enc1C, semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpIR_sem I s hM (n := 2 ^ 9) (src := fB + c) (str := 3) (dst := A)
    (by norm_num) (by omega) (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
    (fun i hi => by omega) (fun i hi => by simp only [regs]; omega)
  have z1 := size_sem I (mcpIR (2 ^ 9) (fB + c) 3 A) s
  generalize semXIR I (mcpIR (2 ^ 9) (fB + c) 3 A) s = s1 at m1 m2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨n1, n2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 ^ 12 - 2 ^ 9) (dst := A + 2 ^ 9)
    (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (zeroIR (2 ^ 12 - 2 ^ 9) (A + 2 ^ 9)) s1
  generalize semXIR I (zeroIR (2 ^ 12 - 2 ^ 9) (A + 2 ^ 9)) s1 = s2 at n1 n2 hM2 z2
  rw [semXIR_seq]
  have a3 : rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M rA0 = toWord A := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rA0]; omega)]
  have k3 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M x = rd s2.M x :=
    fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, rA0]; simp only [regs] at hx; omega)
  have hM3 := inv_sem I (P := .blk [.const rA0 (toWord A)]) (by simp +decide [WF, Prim.dst, rA0]) hM2
  have z3 := size_sem I (.blk [.const rA0 (toWord A)]) s2
  generalize semXIR I (.blk [.const rA0 (toWord A)]) s2 = s3 at a3 k3 hM3 z3
  -- the heap of `s3`
  have h3 : ∀ x, regs ≤ x → (x < A ∨ A + 2 ^ 12 ≤ x) → rd s3.M x = rd s.M x := fun x hx hx2 => by
    rw [k3 x hx, n2 x hx (by omega), m2 x hx (by omega)]
  have hT3 : TabOk s3.M (tbB dB) := tabOk_congr hT fun x h1 h2 => h3 x (by simp only [regs, tbB] at *; omega)
    (by simp only [tbB] at *; omega)
  have hY : ∀ i < 2 ^ 12, rdK s3.M (A + i) =
      if h : i < 2 ^ 9 then (fun x : Fin (2 ^ 9) => rdK s.M (fB + 3 * x + c)) ⟨i, h⟩ else 0 := by
    intro i hi
    simp only [rdK]
    rw [k3 _ (by simp only [regs]; omega)]
    by_cases h : i < 2 ^ 9
    · rw [dif_pos h, n2 _ (by simp only [regs]; omega) (by omega), m1 i h]
      congr 2; ring
    · rw [dif_neg h, show A + i = A + 2 ^ 9 + (i - 2 ^ 9) by omega, n1 _ (by omega)]; rfl
  have hfe := fwdIR_enc I s3 hM3 (A := A) (tb := tbB dB) (ℓ := 12) (m := 9) (by decide) (by norm_num)
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega) a3 hT3
    (fun x : Fin (2 ^ 9) => rdK s.M (fB + 3 * x + c)) hY
  obtain ⟨-, f2, f3⟩ := fwdIR_sem I s3 hM3 (A := A) (tb := tbB dB) (ℓ := 12) (Y := fun i => rdK s3.M (A + i))
    (by decide) (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega) a3 hT3 (fun i _ => rfl)
  exact ⟨hfe, fun x hx hx2 => (f2 x hx hx2).trans (h3 x hx hx2), f3⟩

/-- **`Enc₁(f₂)`'s three coordinates** at `enc1B + c·2^12 + j`. -/
theorem enc1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (hT : TabOk s.M (tbB dB)) :
    (∀ c < 3, ∀ j < 2 ^ 12, rdK (semXIR I (enc1IR dB fB) s).M (enc1B dB + c * 2 ^ 12 + j) =
      encN ptK (fun x : Fin (2 ^ 9) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < enc1B dB ∨ enc1B dB + 3 * 2 ^ 12 ≤ x) →
      rd (semXIR I (enc1IR dB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (enc1IR dB fB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  simp only [regs] at r rF
  rw [enc1IR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := enc1C_sem I s hM hL (c := 0) (by norm_num) hT
  have z1 := size_sem I (enc1C dB fB 0) s
  generalize semXIR I (enc1C dB fB 0) s = s1 at a1 a2 hM1 z1
  have hL1 : Dec1Lay dB wB aB fB oB s1.M.size := by rw [z1]; exact hL
  have hF1 : ∀ x, regs ≤ x → (x < enc1B dB ∨ enc1B dB + 2 ^ 12 ≤ x) → rd s1.M x = rd s.M x :=
    fun x hx hx2 => a2 x hx (by simpa using hx2)
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 =>
    hF1 x (by simp only [regs, tbB] at *; omega) (by simp only [tbB, enc1B] at *; omega)
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := enc1C_sem I s1 hM1 hL1 (c := 1) (by norm_num) hT1
  have z2 := size_sem I (enc1C dB fB 1) s1
  generalize semXIR I (enc1C dB fB 1) s1 = s2 at b1 b2 hM2 z2
  have hL2 : Dec1Lay dB wB aB fB oB s2.M.size := by rw [z2]; exact hL1
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 =>
    b2 x (by simp only [regs, tbB] at *; omega) (by simp only [tbB, enc1B] at *; omega)
  obtain ⟨c1, c2, hM3⟩ := enc1C_sem I s2 hM2 hL2 (c := 2) (by norm_num) hT2
  have hfB : ∀ x c, x < 2 ^ 9 → c < 3 → regs ≤ fB + 3 * x + c ∧
      (fB + 3 * x + c < enc1B dB ∨ enc1B dB + 3 * 2 ^ 12 ≤ fB + 3 * x + c) := fun x c hx hc => by
    simp only [regs, enc1B] at *; omega
  have e1 : ∀ x : Fin (2 ^ 9), ∀ c < 3, rdK s1.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [a2 _ h1 (by omega)]
  have e2 : ∀ x : Fin (2 ^ 9), ∀ c < 3, rdK s2.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [b2 _ h1 (by omega)]; exact e1 x c hc
  refine ⟨fun c hc j hj => ?_, fun x hx hx2 => ?_, hM3⟩
  · interval_cases c
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, enc1B] at *; omega) (by simp only [enc1B] at *; omega),
        b2 _ (by simp only [regs, enc1B] at *; omega) (by simp only [enc1B] at *; omega)]
      exact a1 j hj
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, enc1B] at *; omega) (by simp only [enc1B] at *; omega)]
      rw [show wK (rd s2.M (enc1B dB + 1 * 2 ^ 12 + j)) = rdK s2.M (enc1B dB + 1 * 2 ^ 12 + j) from rfl,
        b1 j hj]
      congr 1; funext x; exact e1 x 1 (by norm_num)
    · rw [c1 j hj]
      congr 1; funext x; exact e2 x 2 (by norm_num)
  · rw [c2 x hx (by omega), b2 x hx (by omega), a2 x hx (by omega)]

/-- **The inverse NTT of the 48 lanes** at `ob1B`. -/
theorem bfly1All_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (hT : TabOk s.M (tbB dB)) (Y : ℕ → ℕ → BF64)
    (hY : ∀ t < 48, ∀ i < 2 ^ 9, rdK s.M (ob1B dB + t * 2 ^ 9 + i) = Y t i) :
    (∀ t < 48, ∀ i < 2 ^ 9, rdK (semXIR I (bfly1All dB) s).M (ob1B dB + t * 2 ^ 9 + i) =
      coeffsAt ptK nLog 9 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < ob1B dB ∨ ob1B dB + 48 * 2 ^ 9 ≤ x) →
      rd (semXIR I (bfly1All dB) s).M x = rd s.M x) ∧
    Inv (semXIR I (bfly1All dB) s).M := by
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL
  have hs := hM.1
  simp only [regs] at r hs
  rw [bfly1All, semXIR_seq]
  have w0 : WF (.blk [.const zT 0, .const zN 48]) := by simp +decide [WF, Prim.dst, zT, zN]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const zT 0, .const zN 48]) s
  have r0 : rd (semXIR I (.blk [.const zT 0, .const zN 48]) s).M zT = toWord 0 ∧
      rd (semXIR I (.blk [.const zT 0, .const zN 48]) s).M zN = toWord 48 := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zT, zN]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const zT 0, .const zN 48]) s).M x = rd s.M x :=
    fun x hx => rd_blk_of_not_dst I _ s (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, zT, zN] <;> simp only [regs] at hx <;> omega)
  generalize semXIR I (.blk [.const zT 0, .const zN 48]) s = s0 at hM0 z0 r0 k0
  obtain ⟨t0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M zT = toWord j ∧
    (∀ t < j, ∀ i < 2 ^ 9, rdK s'.M (ob1B dB + t * 2 ^ 9 + i) = coeffsAt ptK nLog 9 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < ob1B dB ∨ ob1B dB + j * 2 ^ 9 ≤ x) → rd s'.M x = rd s.M x)
  have hoB : ob1B dB = dB + 2 ^ 15 := rfl
  have hE : ∀ i, i ≠ zC → i ≠ cTmp → rd (entryK zC zN (toWord 48) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK zC zN (toWord 48) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun t ht => absurd ht (by omega), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), t0]
    · simp only [regs] at hx
      rw [hE _ (by simp only [zC]; omega) (by simp only [cTmp]; omega), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 48 → P j s' → P (j + 1) (decS zC (semXIR I (bfly1Row dB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    rw [bfly1Row, semXIR_seq]
    set A := ob1B dB + j * 2 ^ 9 with hA
    have hs' := i1.1
    simp only [regs] at hs'
    have a1 : rd (semXIR I (.blk [.const zK (toWord (2 ^ 9)), .op .mul rA0 zT zK,
        .const zK (toWord (ob1B dB)), .op .add rA0 rA0 zK]) s').M rA0 = toWord A := by
      rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, zK, rA0, zT]; omega)) only [rd_set_self, rd_set_ne]
      rw [i3, mul_toWord, add_toWord, hA, Nat.add_comm]
    have a2 : ∀ x, x ≠ zK → x ≠ rA0 → rd (semXIR I (.blk [.const zK (toWord (2 ^ 9)),
        .op .mul rA0 zT zK, .const zK (toWord (ob1B dB)), .op .add rA0 rA0 zK]) s').M x = rd s'.M x :=
      fun x h1 h2 => rd_blk_of_not_dst I _ s' (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Prim.dst]
        exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h1, Ne.symm h2⟩)
    have hM1 := inv_sem I (P := .blk [.const zK (toWord (2 ^ 9)), .op .mul rA0 zT zK,
      .const zK (toWord (ob1B dB)), .op .add rA0 rA0 zK]) (by simp +decide [WF, Prim.dst, zK, rA0]) i1
    have z1 := size_sem I (.blk [.const zK (toWord (2 ^ 9)), .op .mul rA0 zT zK,
      .const zK (toWord (ob1B dB)), .op .add rA0 rA0 zK]) s'
    generalize semXIR I (.blk [.const zK (toWord (2 ^ 9)), .op .mul rA0 zT zK,
      .const zK (toWord (ob1B dB)), .op .add rA0 rA0 zK]) s' = s1 at a1 a2 hM1 z1
    rw [semXIR_seq]
    have hAv : A = dB + 2 ^ 15 + j * 2 ^ 9 := by simp only [hA, ob1B]
    have hx1 : ∀ x, regs ≤ x → x ≠ zK ∧ x ≠ rA0 := fun x hx => by
      simp only [regs, zK, rA0] at *; omega
    have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s'.M x := fun x hx => a2 x (hx1 x hx).1 (hx1 x hx).2
    have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x hx1' hx2' => by
      simp only [tbB] at hx1' hx2'
      rw [h1 x (by simp only [regs]; omega)]
      exact i5 x (by simp only [regs]; omega) (by omega)
    have hY1 : ∀ i < 2 ^ 9, rdK s1.M (A + i) = Y j i := fun i hi => by
      simp only [rdK]
      rw [h1 _ (by simp only [regs]; omega), hAv,
        show dB + 2 ^ 15 + j * 2 ^ 9 + i = ob1B dB + j * 2 ^ 9 + i by rw [hoB],
        i5 _ (by simp only [regs, hoB] at *; omega) (Or.inr (by omega))]
      exact hY j hj i hi
    have hjb : j * 2 ^ 9 + 2 ^ 9 ≤ 48 * 2 ^ 9 := by omega
    obtain ⟨-, b2, hM2⟩ := bflyIR_sem I s1 hM1 (A := A) (tb := tbB dB) (ℓ := 9) (Y := Y j) (by decide)
      (by simp only [regs, hA, ob1B]; omega) (by simp only [hA, ob1B]; omega)
      (by simp only [hA, ob1B]; omega) (by simp only [regs, tbB]; omega) (by simp only [tbB]; omega)
      (by simp only [tbB, hA, ob1B]; omega) a1 hT1 hY1
    have b1 := bflyIR_coeffs I s1 hM1 (A := A) (tb := tbB dB) (ℓ := 9) (Y := Y j) (by decide)
      (by simp only [regs, hA, ob1B]; omega) (by simp only [hA, ob1B]; omega)
      (by simp only [hA, ob1B]; omega) (by simp only [regs, tbB]; omega) (by simp only [tbB]; omega)
      (by simp only [tbB, hA, ob1B]; omega) a1 hT1 hY1
    have q2 : rd (semXIR I (bflyIR 9 (tbB dB)) s1).M zT = toWord j := by
      rw [frame I _ s1 (by simp +decide [bflyIR, lvlStep, levelIR, pairBody, pairPs, alphaIR,
        alphaBody, arithIR, addK, mulK, mulKC, redC, WF, Writes, Prim.dst, rLv, rTr, rN3, rC3, rQ,
        rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI, rTa, rN2, rC2, fAl, fG, fU, fW,
        fH, fT, fN, cTmp, regs]) hM1 zT (by decide) (bflyIR_nw_hi 9 _ (by decide)),
        a2 _ (by decide) (by decide), i3]
    have z2 := size_sem I (bflyIR 9 (tbB dB)) s1
    generalize semXIR I (bflyIR 9 (tbB dB)) s1 = s2 at b1 b2 hM2 q2 z2
    have hd : ∀ x, x ≠ zC → rd (decS zC (semXIR I (.blk [.op .add zT zT cOne]) s2)).M x =
        rd (semXIR I (.blk [.op .add zT zT cOne]) s2).M x := fun x hx => rd_decS (Ne.symm hx) _
    have c2 : ∀ x, x ≠ zT → rd (semXIR I (.blk [.op .add zT zT cOne]) s2).M x = rd s2.M x :=
      fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact Ne.symm hx)
    have hM3 := inv_sem I (P := .blk [.op .add zT zT cOne]) (by simp +decide [WF, Prim.dst, zT]) hM2
    have hx3 : ∀ x, regs ≤ x → x ≠ zC ∧ x ≠ zT := fun x hx => by
      simp only [regs, zC, zT] at *; omega
    refine ⟨inv_decS hM3 (by decide), by rw [size_decS, size_sem, z2, z1, i2], ?_,
      fun t ht i hi => ?_, fun x hx hx2 => ?_⟩
    · have hs2 := hM2.1
      simp only [regs] at hs2
      rw [hd _ (by decide), sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [zT]; omega), q2, show rd s2.M cOne = 1 from hM2.2 0 (by decide),
        add_one_toWord]
    · have hxr : regs ≤ ob1B dB + t * 2 ^ 9 + i := by simp only [regs, ob1B] at *; omega
      simp only [rdK]
      rw [hd _ (hx3 _ hxr).1, c2 _ (hx3 _ hxr).2]
      by_cases htj : t = j
      · subst htj; exact b1 i hi
      · have ht' : t < j := by omega
        have : t * 2 ^ 9 + 2 ^ 9 ≤ j * 2 ^ 9 := by
          have h := Nat.mul_le_mul_right (2 ^ 9) (Nat.succ_le_of_lt ht'); rwa [Nat.succ_mul] at h
        rw [b2 _ hxr (by left; omega), h1 _ hxr]
        exact i4 t ht' i hi
    · have e : (j + 1) * 2 ^ 9 = j * 2 ^ 9 + 2 ^ 9 := by ring
      rw [e] at hx2
      have hx4 : x < A ∨ A + 2 ^ 9 ≤ x := by
        rcases hx2 with h | h
        · exact Or.inl (Nat.lt_of_lt_of_le h (Nat.le_add_right (ob1B dB) (j * 2 ^ 9)))
        · rw [← Nat.add_assoc] at h; exact Or.inr h
      have hx5 : x < ob1B dB ∨ ob1B dB + j * 2 ^ 9 ≤ x := by
        rcases hx2 with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans (by rw [← Nat.add_assoc]; exact Nat.le_add_right _ _) h)
      rw [hd _ (hx3 x hx).1, c2 _ (hx3 x hx).2, b2 x hx hx4, h1 x hx, i5 x hx hx5]
  have hfin := loopK_run I (bfly1Row dB) P s0 hM0 (c := zC) (n := zN) (K := 48) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, fun x hx hx2 => hfin.2.2.2.2 x hx hx2, hfin.1⟩

/-- **The flag**: `rOk` and `ok1B`'s cell `= [2^9 ≤ cnt]`. -/
theorem ok1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB n : ℕ} (hdB : regs ≤ dB)
    (hdB2 : ok1B dB < 2 ^ 64) (hdBs : ok1B dB < s.M.size) (hn : n < 2 ^ 64)
    (hC : rd s.M gCnt = toWord n) :
    rd (semXIR I (ok1IR dB) s).M rOk = bW (decide (2 ^ 9 ≤ n)) ∧
    rd (semXIR I (ok1IR dB) s).M (ok1B dB) = bW (decide (2 ^ 9 ≤ n)) ∧
    (∀ x, regs ≤ x → x ≠ ok1B dB → rd (semXIR I (ok1IR dB) s).M x = rd s.M x) ∧
    Inv (semXIR I (ok1IR dB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdB
  rw [ok1IR, semXIR_seq]
  set ps : List Prim := [.const zK (toWord (2 ^ 9)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (ok1B dB))] with hps
  have hM1 := inv_sem I (P := .blk ps) (by simp +decide [hps, WF, Prim.dst, zK, rOk]) hM
  have v1 : rd (semXIR I (.blk ps) s).M rOk = bW (decide (2 ^ 9 ≤ n)) ∧
      rd (semXIR I (.blk ps) s).M zK = toWord (ok1B dB) := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zK, rOk]; omega)) only [rd_set_self, rd_set_ne]
    rw [hC, ltW_toWord hn (by norm_num), show rd s.M cOne = 1 from hM.2 0 (by decide), eval_xor,
      bW_xor_one]
    congr 1
    rw [← decide_not]
    simp only [Nat.not_lt]
  have k1 : ∀ x, regs ≤ x → rd (semXIR I (.blk ps) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, zK, rOk] <;> omega
  have z1 := size_sem I (.blk ps) s
  generalize semXIR I (.blk ps) s = s1 at hM1 v1 k1 z1
  obtain ⟨st1, st2, hM2⟩ := store_sem I s1 hM1 (p := zK) (v := rOk) (x := ok1B dB) (by decide)
    (by decide) v1.2 (by simp only [regs, ok1B]; omega) hdB2 (by omega)
  refine ⟨?_, by rw [st1, v1.1], fun x hx hx2 => by
    rw [st2 x hx2 (by simp only [regs, cTmp] at *; omega), k1 x hx], hM2⟩
  rw [st2 _ (by simp only [rOk, ok1B]; omega) (by decide), v1.1]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb
attribute [local irreducible] entryK storeM

/-- **One transposed row** `v < 2^9`: `oB + 48 v + t := ob + v + 2^9 t` (`t < 48`), `yL := v + 1`. -/
theorem tr1Row_sem (I : Array Word) (s : St) (hM : Inv s.M) {ob oB v : ℕ} (hv : v < 2 ^ 9)
    (hob : regs ≤ ob) (hob2 : ob + 48 * 2 ^ 9 < 2 ^ 64) (hoB : regs ≤ oB)
    (hoB2 : oB + 48 * 2 ^ 9 < 2 ^ 64) (hoBs : oB + 48 * 2 ^ 9 ≤ s.M.size)
    (hdisj : ob + 48 * 2 ^ 9 ≤ oB ∨ oB + 48 * 2 ^ 9 ≤ ob) (hL : rd s.M yL = toWord v) :
    (∀ t < 48, rd (semXIR I (tr1Row ob oB) s).M (oB + 48 * v + t) = rd s.M (ob + v + 2 ^ 9 * t)) ∧
    rd (semXIR I (tr1Row ob oB) s).M yL = toWord (v + 1) ∧
    (∀ r, regs ≤ r → (r < oB + 48 * v ∨ oB + 48 * v + 48 ≤ r) →
      rd (semXIR I (tr1Row ob oB) s).M r = rd s.M r) ∧
    Inv (semXIR I (tr1Row ob oB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hob hoB
  rw [tr1Row, semXIR_seq]
  set ps : List Prim := [.const yK (toWord ob), .op .add ySr yL yK, .const yK 48, .op .mul yDs yL yK,
      .const yK (toWord oB), .op .add yDs yDs yK, .const yStr (toWord (2 ^ 9))] with hps
  have w0 : WF (.blk ps) := by simp +decide [hps, WF, Prim.dst, yK, ySr, yDs, yStr]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk ps) s
  have r0 : rd (semXIR I (.blk ps) s).M ySr = toWord (ob + v) ∧
      rd (semXIR I (.blk ps) s).M yDs = toWord (oB + 48 * v) ∧
      rd (semXIR I (.blk ps) s).M yStr = toWord (2 ^ 9) ∧ rd (semXIR I (.blk ps) s).M yL = toWord v := by
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
      simp only [Prim.dst, yK, ySr, yDs, yStr] <;> omega
  generalize semXIR I (.blk ps) s = s0 at hM0 z0 r0 k0
  obtain ⟨p1, p2, p3, p4⟩ := r0
  rw [semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := tr1Loop_sem I s0 hM0 (n := 48) (src := ob + v) (str := 2 ^ 9)
    (dst := oB + 48 * v) (by norm_num) (fun i hi => by omega) (by simp only [regs]; omega)
    (by omega) (by omega) (fun i hi => by omega) (fun i hi => by simp only [regs]; omega) p1 p2 p3
  have z1 := size_sem I (mcpLoop 48) s0
  have l1 : rd (semXIR I (mcpLoop 48) s0).M yL = toWord v := by
    rw [frame I _ s0 (by simp +decide [mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yV, yN,
      yC, cTmp, regs]) hM0 yL (by decide) (by simp +decide [mcpLoop, mcpBody, Writes, Prim.dst,
        ySr, yDs, yV, yN, yC, yL, cTmp]), p4]
  generalize semXIR I (mcpLoop 48) s0 = s1 at m1 m2 hM1 z1 l1
  have b2 : ∀ r, r ≠ yL → rd (semXIR I (.blk [.op .add yL yL cOne]) s1).M r = rd s1.M r :=
    fun r hr => rd_blk_of_not_dst I _ s1 (by simp [Prim.dst]; exact Ne.symm hr)
  have hx : ∀ x, regs ≤ x → x ≠ yL := fun x hx => by simp only [regs, yL] at *; omega
  refine ⟨fun t ht => ?_, ?_, fun r hr hr2 => ?_, inv_sem I (P := .blk [.op .add yL yL cOne])
    (by simp +decide [WF, Prim.dst, yL]) hM1⟩
  · rw [b2 _ (hx _ (by simp only [regs]; omega)), m1 t ht, k0 _ (by simp only [regs]; omega)]
  · have hs1 := hM1.1
    simp only [regs] at hs1
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [yL]; omega), l1, show rd s1.M cOne = 1 from hM1.2 0 (by decide),
      add_one_toWord]
  · rw [b2 _ (hx r hr), m2 r (keepC_of_regs hr) hr2, k0 r hr]

/-- **The transpose**: `M[oB + 48 v + t] = M[ob + 2^9 t + v]`; the heap outside
`[oB, oB + 48·2^9)` is kept. -/
theorem tr1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ob oB : ℕ}
    (hob : regs ≤ ob) (hob2 : ob + 48 * 2 ^ 9 < 2 ^ 64) (hoB : regs ≤ oB)
    (hoB2 : oB + 48 * 2 ^ 9 < 2 ^ 64) (hoBs : oB + 48 * 2 ^ 9 ≤ s.M.size)
    (hd : ob + 48 * 2 ^ 9 ≤ oB ∨ oB + 48 * 2 ^ 9 ≤ ob) :
    (∀ v < 2 ^ 9, ∀ t < 48, rd (semXIR I (tr1IR ob oB) s).M (oB + 48 * v + t) =
      rd s.M (ob + 2 ^ 9 * t + v)) ∧
    (∀ x, regs ≤ x → (x < oB ∨ oB + 48 * 2 ^ 9 ≤ x) → rd (semXIR I (tr1IR ob oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (tr1IR ob oB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hob hoB
  rw [tr1IR, semXIR_seq]
  have w0 : WF (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) := by
    simp +decide [WF, Prim.dst, yL, yN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) s
  have r0 : rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) s).M yL = toWord 0 ∧
      rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) s).M yN2 = toWord (2 ^ 9) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yL, yN2]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r →
      rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [regs] at hr
      refine rd_blk_of_not_dst I _ s ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, yL, yN2] <;> omega
  generalize semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) s = s0 at hM0 z0 r0 k0
  obtain ⟨l0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M yL = toWord j ∧
    (∀ v < j, ∀ t < 48, rd s'.M (oB + 48 * v + t) = rd s.M (ob + 2 ^ 9 * t + v)) ∧
    (∀ r, regs ≤ r → (r < oB ∨ oB + 48 * j ≤ r) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC2 → i ≠ cTmp → rd (entryK yC2 yN2 (toWord (2 ^ 9)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC2 yN2 (toWord (2 ^ 9)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun v hv => absurd hv (by omega), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), l0]
    · simp only [regs] at hr
      rw [hE _ (by simp only [yC2]; omega) (by simp only [cTmp]; omega), k0 r (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 2 ^ 9 → P j s' → P (j + 1) (decS yC2 (semXIR I (tr1Row ob oB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    obtain ⟨b1, b2, b3, hM'⟩ := tr1Row_sem I s' i1 (ob := ob) (oB := oB) hj
      (by simp only [regs]; omega) hob2 (by simp only [regs]; omega) hoB2 (by omega) hd i3
    have hd' : ∀ x, x ≠ yC2 → rd (decS yC2 (semXIR I (tr1Row ob oB) s')).M x =
        rd (semXIR I (tr1Row ob oB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hx : ∀ x, regs ≤ x → x ≠ yC2 := fun x hx => by simp only [regs, yC2] at *; omega
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], by rw [hd' _ (by decide), b2],
      fun v hv t ht => ?_, fun r hr hr2 => ?_⟩
    · rw [hd' _ (hx _ (by simp only [regs]; omega))]
      by_cases hvj : v = j
      · subst hvj
        rw [b1 t ht, i5 _ (by simp only [regs]; omega) (by omega), Nat.add_right_comm]
      · rw [b3 _ (by simp only [regs]; omega) (by omega), i4 v (by omega) t ht]
    · rw [hd' _ (hx r hr), b3 r hr (by omega), i5 r hr (by omega)]
  have hfin := loopK_run I (tr1Row ob oB) P s0 hM0 (c := yC2) (n := yN2) (K := 2 ^ 9) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2 r hr (by omega), hfin.1⟩

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

/-- **The decoding proper**: on a list of `≥ 2^9` agreeing positions at `ag1B`, the decoded
message at `oB`. -/
theorem dec1Tail_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (hT : TabOk s.M (tbB dB)) (wd : ℕ → ℕ → BF64)
    (α f₂ : ℕ → Ext3) (hW : ∀ q < 2 ^ 12, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hlen : 2 ^ 9 ≤ (agree1L wd α f₂).length)
    (hJ : ∀ t < 2 ^ 9, rd s.M (ag1B dB + t) = toWord ((agree1L wd α f₂).getD t 0)) :
    (∀ v < 2 ^ 13, rdE (semXIR I (dec1Tail dB wB oB) s).M (oB + 3 * v) = dec1At wd α f₂ v) ∧
    (∀ x, regs ≤ x → (x < dB + 2 ^ 10 ∨ dB + 2 ^ 16 ≤ x) → (x < oB ∨ oB + 3 * 2 ^ 13 ≤ x) →
      rd (semXIR I (dec1Tail dB wB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (dec1Tail dB wB oB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  simp only [regs] at r rW rO
  set Jl := sel1J wd α f₂ with hJl
  have hJlen : Jl.length = 2 ^ 9 := by
    rw [hJl, sel1J, List.length_take, Nat.min_eq_left hlen]
  have hJnd : Jl.Nodup := (nodup_agree1L wd α f₂).sublist (List.take_sublist _ _)
  have hJlt : ∀ j ∈ Jl, j < 2 ^ 12 := fun j hj => (mem_agree1L.1 (List.mem_of_mem_take hj)).1
  have hBL : BaryLay (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB) s.M.size := by
    refine ⟨by norm_num, le_rfl, ?_, ?_, ?_, ?_, rW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [regs, ag1B, wb1B, eb1B, ob1B]) <;> omega
  have hget : ∀ t < 2 ^ 9, Jl.getD t 0 < 2 ^ 15 := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    have := hJlt _ (List.getElem_mem (l := Jl) (n := t) (by omega)); omega
  rw [dec1Tail, semXIR_seq]
  obtain ⟨b1, b2, hM1⟩ := baryIR_sem I s hM (Jl := Jl) hBL hget (fun t ht => by
    rw [hJ t ht, hJl, sel1J, getD_take_lt ht])
  have z1 := size_sem I (baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB)) s
  generalize semXIR I (baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB)) s = s1
    at b1 b2 hM1 z1
  have hL1 : Dec1Lay dB wB aB fB oB s1.M.size := by rw [z1]; exact hL
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact b2 x (by simp only [regs]; omega) (by simp only [wb1B]; omega) (by simp only [eb1B]; omega)
      (by simp only [ob1B]; omega)
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := bfly1All_sem I s1 hM1 hL1 hT1
    (fun t i => rdK s1.M (ob1B dB + t * 2 ^ 9 + i)) (fun _ _ _ _ => rfl)
  have z2 := size_sem I (bfly1All dB) s1
  generalize semXIR I (bfly1All dB) s1 = s2 at c1 c2 hM2 z2
  obtain ⟨d1, d2, hM3⟩ := tr1IR_sem I s2 hM2 (ob := ob1B dB) (oB := oB)
    (by simp only [regs, ob1B]; omega) (by simp only [ob1B]; omega) (by simp only [regs]; omega)
    (by omega) (by rw [z2, z1]; omega) (by simp only [ob1B]; omega)
  generalize semXIR I (tr1IR (ob1B dB) oB) s2 = s3 at d1 d2 hM3
  refine ⟨fun v hv => ?_, fun x hx hx2 hx3 => ?_, hM3⟩
  · -- the decoded entry `v = u + 16 v'`
    have hval : ∀ c < 3, rdK s3.M (oB + 3 * v + c) = coef1 wd α f₂ (3 * (v % 16) + c) (v / 16) := by
      intro c hc
      have hu : v % 16 < 16 := Nat.mod_lt _ (by norm_num)
      have hv' : v / 16 < 2 ^ 9 := by omega
      have e : oB + 3 * v + c = oB + 48 * (v / 16) + (3 * (v % 16) + c) := by omega
      simp only [rdK]
      rw [e, d1 (v / 16) hv' (3 * (v % 16) + c) (by omega),
        show ob1B dB + 2 ^ 9 * (3 * (v % 16) + c) + v / 16 =
          ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + v / 16 by ring,
        show wK (rd s2.M (ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + v / 16)) =
          rdK s2.M (ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + v / 16) from rfl,
        c1 (3 * (v % 16) + c) (by omega) (v / 16) hv', coef1]
      refine coeffsAt_congr ptK nLog 9 0 _ _ (fun j hj => ?_) (v / 16) hv'
      rw [show ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + j = ob1B dB + 2 ^ 9 * (3 * (v % 16) + c) + j
        by ring, b1 j hj _ (by omega), show (2 : ℕ) ^ 9 = Jl.length from hJlen.symm,
        baryValK_eq hJnd (fun j hj => by have := hJlt j hj; omega) (by omega)]
      refine interpF_congr ptK _ (fun q hq => ?_) j
      have hq' := hJlt q (List.mem_toFinset.1 hq)
      rw [hW q hq' _ (by omega), lane1]
    have h0 := hval 0 (by norm_num)
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [rdE, h0, hval 1 (by norm_num), hval 2 (by norm_num), dec1At]
  · simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega) (by omega),
      c2 x (by simp only [regs]; omega) (by simp only [ob1B]; omega),
      b2 x (by simp only [regs]; omega) (by simp only [wb1B]; omega) (by simp only [eb1B]; omega)
        (by simp only [ob1B]; omega)]

/-- **The level-1 decoder computes `decodeRec1`.** -/
theorem dec1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 12, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hA : ∀ i < 4, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 9, rdE s.M (fB + 3 * v) = f₂ v) :
    rd (semXIR I (dec1IR dB wB aB fB oB) s).M (ok1B dB) =
      bW (decide (2 ^ 9 ≤ (agree1L wd α f₂).length)) ∧
    (∀ f₁, decodeRec1 wd α f₂ = some f₁ →
      ∀ v < 2 ^ 13, rdE (semXIR I (dec1IR dB wB aB fB oB) s).M (oB + 3 * v) = f₁ v) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 16 ≤ x) → (x < oB ∨ oB + 3 * 2 ^ 13 ≤ x) →
      rd (semXIR I (dec1IR dB wB aB fB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (dec1IR dB wB aB fB oB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  have hs := hM.1
  simp only [regs] at r rW rA rF rO hs
  -- 1. the basis table
  rw [dec1IR, semXIR_seq]
  obtain ⟨w1, w2, hM1, z1⟩ := wtabIR_sem I s hM (tb := tbB dB) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega)
  generalize semXIR I (wtabIR (tbB dB)) s = s1 at w1 w2 hM1 z1
  have hT1 : TabOk s1.M (tbB dB) := w1
  -- 2. the `eq` table
  rw [semXIR_seq]
  obtain ⟨q1, q2, hM2⟩ := eqtIR_sem I s1 hM1 (ℓ := 4) (aB := aB) (qB := q1B dB) (by norm_num)
    (by simp only [regs]; omega) (by omega) (by simp only [regs, q1B]; omega)
    (by simp only [q1B]; omega) (by rw [z1]; simp only [q1B]; omega) (by simp only [q1B]; omega)
  have z2 := size_sem I (eqtIR 4 aB (q1B dB)) s1
  generalize semXIR I (eqtIR 4 aB (q1B dB)) s1 = s2 at q1 q2 hM2 z2
  have q2' : ∀ x, regs ≤ x → (x < q1B dB ∨ q1B dB + 48 ≤ x) → rd s2.M x = rd s1.M x :=
    fun x hx hx2 => q2 x (.inr (lt_of_lt_of_le (by decide) hx)) (by omega)
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact q2' x (by simp only [regs]; omega) (by simp only [q1B]; omega)
  have hQ2 : ∀ u < 16, rdE s2.M (q1B dB + 3 * u) = eqA1 α u := fun u hu => by
    rw [q1 u hu]
    refine eqA1_congr (fun i hi => ?_) u
    rw [← hA i hi]
    exact rdE_congr fun k hk => w2 _ (by simp only [regs]; omega) (by simp only [tbB]; omega)
  have hL2 : Dec1Lay dB wB aB fB oB s2.M.size := by rw [z2, z1]; exact hL
  -- 3. `Enc₁(f₂)`
  rw [semXIR_seq]
  obtain ⟨e1, e2, hM3⟩ := enc1IR_sem I s2 hM2 hL2 hT2
  have z3 := size_sem I (enc1IR dB fB) s2
  generalize semXIR I (enc1IR dB fB) s2 = s3 at e1 e2 hM3 z3
  have hout : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 16 ≤ x) → rd s2.M x = rd s.M x := fun x hx hx2 => by
    rw [q2' x hx (by simp only [q1B]; omega), w2 x hx (by simp only [tbB]; omega)]
  have hfB : ∀ v < 2 ^ 9, ∀ c < 3, rdK s2.M (fB + 3 * v + c) = rdK s.M (fB + 3 * v + c) :=
    fun v hv c hc => by simp only [rdK]; rw [hout _ (by simp only [regs]; omega) (by omega)]
  have hW3 : ∀ q < 2 ^ 12, ∀ t < 48, rdK s3.M (wB + 48 * q + t) = wd q t := fun q hq t ht => by
    rw [← hW q hq t ht]; simp only [rdK]
    rw [e2 _ (by simp only [regs]; omega) (by simp only [enc1B]; omega),
      hout _ (by simp only [regs]; omega) (by omega)]
  have hQ3 : ∀ u < 16, rdE s3.M (q1B dB + 3 * u) = eqA1 α u := fun u hu => by
    rw [← hQ2 u hu]
    exact rdE_congr fun k hk => e2 _ (by simp only [regs, q1B]; omega)
      (by simp only [q1B, enc1B]; omega)
  have hE3 : ∀ q < 2 ^ 12, enc1 f₂ q = mkE (rdK s3.M (enc1B dB + q))
      (rdK s3.M (enc1B dB + 2 ^ 12 + q)) (rdK s3.M (enc1B dB + 2 * 2 ^ 12 + q)) := fun q hq => by
    have hc : ∀ c < 3, ∑ v ∈ range (2 ^ 9), rdK s.M (fB + 3 * v + c) * nbAt v q =
        rdK s3.M (enc1B dB + c * 2 ^ 12 + q) := fun c hc => by
      rw [e1 c hc q hq, sum_nbAt_eq_encN]
      exact congrArg (fun g => encN ptK g q) (funext fun x => (hfB x x.isLt c hc).symm)
    have hc0 := hc 0 (by norm_num)
    have hc1 := hc 1 (by norm_num)
    have hc2 := hc 2 (by norm_num)
    rw [Nat.zero_mul, Nat.add_zero] at hc0
    rw [Nat.one_mul] at hc1
    rw [enc1, ← hc0, ← hc1, ← hc2, ← mkE_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← mkE_mul_ofK, ← hF v (mem_range.1 hv)]
    rfl
  have hAg : agree1M s3.M wB (q1B dB) (enc1B dB) (2 ^ 12) = agree1L wd α f₂ :=
    agree1M_eq_agree1L wd α f₂ hW3 hQ3 hE3
  -- 4. the agreement scan
  rw [semXIR_seq]
  obtain ⟨g1, g2, g3, hM4⟩ := agree1IR_sem I s3 hM3 (wB := wB) (qB := q1B dB) (eB := enc1B dB)
    (agB := ag1B dB) (by simp only [regs]; omega) (by omega) (by simp only [regs, q1B]; omega)
    (by simp only [q1B]; omega) (by simp only [regs, enc1B]; omega) (by simp only [enc1B]; omega)
    (by simp only [regs, ag1B]; omega) (by simp only [ag1B]; omega)
    (by rw [z3, z2, z1]; simp only [ag1B]; omega)
    ⟨by simp only [ag1B]; omega, by simp only [ag1B, q1B]; omega, by simp only [ag1B, enc1B]; omega⟩
  rw [hAg] at g1 g2
  have z4 := size_sem I (agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)) s3
  generalize semXIR I (agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)) s3 = s4 at g1 g2 g3 hM4 z4
  have hlen64 : (agree1L wd α f₂).length < 2 ^ 64 := by
    have : (agree1L wd α f₂).length ≤ 2 ^ 12 := by
      rw [agree1L]; exact (List.length_filter_le _ _).trans (by simp)
    omega
  -- 5. the flag
  rw [semXIR_seq]
  obtain ⟨o1, o2, o3, hM5⟩ := ok1IR_sem I s4 hM4 (dB := dB) (n := (agree1L wd α f₂).length)
    (by simp only [regs]; omega) (by simp only [ok1B]; omega)
    (by rw [z4, z3, z2, z1]; simp only [ok1B]; omega) hlen64 g1
  have z5 := size_sem I (ok1IR dB) s4
  generalize semXIR I (ok1IR dB) s4 = s5 at o1 o2 o3 hM5 z5
  -- the heap of `s5`
  have hT5 : TabOk s5.M (tbB dB) := tabOk_congr hT2 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    rw [o3 x (by simp only [regs]; omega) (by simp only [ok1B]; omega),
      g3 x (by simp only [regs]; omega) (by simp only [ag1B]; omega),
      e2 x (by simp only [regs]; omega) (by simp only [enc1B]; omega)]
  have h5 : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 16 ≤ x) → rd s5.M x = rd s.M x := fun x hx hx2 => by
    rw [o3 x hx (by simp only [ok1B]; omega), g3 x hx (by simp only [ag1B]; omega),
      e2 x hx (by simp only [enc1B]; omega), hout x hx hx2]
  -- 6. the branch
  rw [semXIR_ite, o1]
  by_cases hk : 2 ^ 9 ≤ (agree1L wd α f₂).length
  · rw [decide_eq_true hk, if_neg bW_true_ne]
    have hL5 : Dec1Lay dB wB aB fB oB s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hL
    have hW5 : ∀ q < 2 ^ 12, ∀ t < 48, rdK s5.M (wB + 48 * q + t) = wd q t := fun q hq t ht => by
      rw [← hW q hq t ht]; simp only [rdK]; rw [h5 _ (by simp only [regs]; omega) (by omega)]
    have hJ5 : ∀ t < 2 ^ 9, rd s5.M (ag1B dB + t) = toWord ((agree1L wd α f₂).getD t 0) :=
      fun t ht => by
        rw [o3 _ (by simp only [regs, ag1B]; omega) (by simp only [ag1B, ok1B]; omega), g2 t (by omega)]
    obtain ⟨d1, d2, hM6⟩ := dec1Tail_sem I s5 hM5 hL5 hT5 wd α f₂ hW5 hk hJ5
    refine ⟨?_, fun f₁ hout' v hv => ?_, fun x hx hx2 hx3 => ?_, hM6⟩
    · rw [d2 _ (by simp only [regs, ok1B]; omega) (by simp only [ok1B]; omega)
        (by simp only [ok1B]; omega), o2, decide_eq_true hk]
    · rw [decodeRec1, if_pos hk, Option.some.injEq] at hout'
      rw [← hout', d1 v hv]
      exact (if_pos hv).symm
    · rw [d2 x hx (by omega) hx3, h5 x hx hx2]
  · rw [decide_eq_false hk, if_pos bW_false_eq]
    have e6 : semXIR I (.blk []) s5 = s5 := by cases s5; rfl
    rw [e6]
    refine ⟨by rw [o2, decide_eq_false hk], fun f₁ hout' => ?_, fun x hx hx2 _ => h5 x hx hx2, hM5⟩
    rw [decodeRec1, if_neg hk] at hout'
    exact absurd hout' (by simp)

end Lvm.X
end
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

theorem hasOut_dec1IR (dB wB aB fB oB : ℕ) : hasOut (dec1IR dB wB aB fB oB) = false := rfl

/-- **`dec1IR` writes no output.** -/
theorem dec1IR_o (I : Array Word) (s : St) (dB wB aB fB oB : ℕ) :
    (semXIR I (dec1IR dB wB aB fB oB) s).o = s.o := sem_o I _ s (hasOut_dec1IR dB wB aB fB oB)

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

/-- **A layout** below `2^24` (see the module header). -/
theorem dec1Lay_example (sz : ℕ) (hsz : 2 ^ 25 ≤ sz) :
    Dec1Lay (2 ^ 23 + 2 ^ 21) (2 ^ 23) (2 ^ 19 + 24) (2 ^ 23 + 2 ^ 22) (2 ^ 19 + 64) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [regs]) <;> omega

end Lvm.X
end

-- ===== from `LvmXTop` =====

section
section
namespace Lvm.X
open RecursionFast Lvm

/-- **The node output's words.** -/
def outWords (π : Proof) (w : ℕ → Word) : List Word :=
  toWord 1 :: wsAt (pw π) 6 4 ++ packBytes (leafStmt (hdD π 15) (pw π 14).toNat).toList ++
    (toWord (piSize pX) :: pWords (laneOf w)) ++ trWords (laneOf w) ++ wsAt (sigCol w) 0 597 ++
    (toWord 48 :: toWord 0 :: wsAt (pw π) 10 4 ++ [pw π 14]) ++ [toWord 0] ++
    wsAt (fun j => pw π (19 + j)) 0 597

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Lvm

theorem signed_left (w : ℕ → Word) :
    signedWords ⟨reassembleL (readTraceL (laneOf w)), readTraceL (laneOf w), sigOfF (sigCol w)⟩ =
      (toWord (piSize pX) :: pWords (laneOf w)) ++ trWords (laneOf w) ++ wsAt (sigCol w) 0 597 := by
  have hl : (reassembleL (readTraceL (laneOf w))).data.toList.length = piSize pX := by
    rw [Array.length_toList]; exact size_reassembleL _
  rw [signedWords, bytesWords, hl, packBytes_reassembleL, logWords_readTraceL, sigWords_sigOfF]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Lvm

theorem witWords_Xwit (π : Proof) (w : ℕ → Word) : witWords (Xwit π w) = outWords π w := by
  rw [Xwit, witWords, signed_left, signed_right, hdD, packBytes_digW (length_wsAt _ _ _), outWords]
  simp only [List.cons_append, List.append_assoc]

theorem fits_Xwit (π : Proof) (w : ℕ → Word) : (Xwit π w).Fits := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [size_reassembleL, piSize_eq]; norm_num
  · rw [length_readTraceL, qS_P20.1]; norm_num
  · intro e he
    simp only [readTraceL, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨x, hx, rfl⟩
    · simp [q0Ent, wordBytes_length]
    · obtain ⟨-, h2⟩ := walk_lt 6 lensL x (hx)
      have h3 := lanes_T
      have h4 : streamLanes pX = 75593 := sizes_P20.2.2.2.2.2.2.1
      simp only [entAt, bArr_size, wordsBytes_length, length_wsAt]
      omega
  · exact (sigCol w 0).isLt
  · simp [sigOfF]
  · simp [sigOfF]
  · rw [WitnessSending.size_encode_leaf]; norm_num
  · simp
  · simp
  · exact (pw π 19).isLt
  · simp [sigOfF]
  · simp [sigOfF]

/-- **The node output denotes the node witness.** -/
theorem decodeWit_outWords (π : Proof) (w : ℕ → Word) : decodeWit (outWords π w) = some (Xwit π w) := by
  rw [← witWords_Xwit, decodeWit_witWords _ (fits_Xwit π w)]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Lvm

theorem sgB_eq : sgB = 2 ^ 24 + 2 ^ 16 := rfl

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Lvm

/-- π's packed words on the tape. -/
theorem tape_pw (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) {j : ℕ}
    (hj : j < 41542) : (extractorInput c π L).toArray.getD (5 + j) 0 = pw π j := by
  have hp : π.size = 332336 := hs.trans piSize_eq
  rw [getD_toArray, tape_getD_proof c π L (by rw [hp]; omega), pw, List.getD_eq_getElem]

theorem wsAt_tape (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) {a n : ℕ}
    (h : a + n ≤ 41542) :
    (List.range n).map (fun j => (extractorInput c π L).toArray.getD (5 + a + j) 0) = wsAt (pw π) a n :=
  List.map_congr_left fun j hj => by
    rw [Nat.add_assoc, tape_pw c π L hs (by simp at hj; (clear * - h hj; omega))]

/-- **The node output**: from a state whose heap holds the decoded message `w` at `mB`, on the tape
of an `S` proof, `outIR mB` appends `outWords π w`. -/
theorem outIR_sem (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) (s : St)
    (hM : Inv s.M) {mB : ℕ} (hmB : regs ≤ mB) (hmB2 : mB + 2 ^ 19 ≤ sgB) (hsz : sgB + nCp ≤ s.M.size)
    (w : ℕ → Word) (hw : ∀ i < 2 ^ 19, rd s.M (mB + i) = w i) :
    (semXIR (extractorInput c π L).toArray (outIR mB) s).o.toList = s.o.toList ++ outWords π w := by
  set I := (extractorInput c π L).toArray with hI
  have hs0 := hM.1
  simp only [regs] at hs0 hmB
  -- 1. the tag
  have hwf1 := wf_emitIR (toWord 1)
  obtain ⟨o1, f1⟩ := emitIR_sem I s hM (toWord 1)
  have hM1 := inv_sem I hwf1 hM
  have z1 := size_sem I (emitIR (toWord 1)) s
  rw [outIR, semXIR_seq]
  generalize semXIR I (emitIR (toWord 1)) s = s1 at o1 f1 hM1 z1
  -- 2. `c_L`
  obtain ⟨o2, f2, hM2, z2⟩ := tcpIR_sem I s1 hM1 (a := 11) (n := 4) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (tcpIR 11 4) s1 = s2 at o2 f2 hM2 z2
  -- 3. `leafStmt h n`
  obtain ⟨o3, f3⟩ := leafStmtIR_sem I s2 hM2 (hW := 20) (nW := 19) (hdD π 15) (pw π 14).toNat
    (fun i hi => by
      rw [hdD, packBytes_digW (length_wsAt _ _ _), wsAt, List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_map, List.getElem_range, show 20 + i = 5 + (15 + i) by (clear * -; omega),
        tape_pw c π L hs (by (clear * - hi; omega))])
    (by rw [show 19 = 5 + 14 from rfl, tape_pw c π L hs (by (clear * -; omega)), toWord_toNat'])
    (pw π 14).isLt (by norm_num) (by norm_num)
  have hM3 := inv_sem I (wf_leafStmtIR 20 19) hM2
  have z3 := size_sem I (leafStmtIR 20 19) s2
  rw [semXIR_seq]
  generalize semXIR I (leafStmtIR 20 19) s2 = s3 at o3 f3 hM3 z3
  -- 4. `|π'|`
  obtain ⟨o4, f4⟩ := emitIR_sem I s3 hM3 (toWord (piSize pX))
  have hM4 := inv_sem I (wf_emitIR (toWord (piSize pX))) hM3
  have z4 := size_sem I (emitIR (toWord (piSize pX))) s3
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord (piSize pX))) s3 = s4 at o4 f4 hM4 z4
  -- the heap so far
  have h4 : ∀ y, regs ≤ y → rd s4.M y = rd s.M y := fun y hy => by
    simp only [regs] at hy
    rw [f4 y (by simp only [eW]; (clear * - hy; omega)), f3 y (by simp only [regs]; omega),
      f2 y (by simp only [eW]; (clear * - hy; omega)) (by simp only [eP]; (clear * - hy; omega)) (by simp only [eN]; (clear * - hy; omega))
        (by simp only [eC]; (clear * - hy; omega)) (by simp only [cTmp]; (clear * - hy; omega)), f1 y (by simp only [eW]; (clear * - hy; omega))]
  have zz4 : s4.M.size = s.M.size := by rw [z4, z3, z2, z1]
  -- 5. the stream copy
  obtain ⟨c1, c2, hM5, z5, o5⟩ := copyIR_sem I s4 hM4 (mB := mB) (by simp only [regs]; omega) hmB2
    (by rw [zz4]; exact hsz)
  rw [semXIR_seq]
  generalize semXIR I (copyIR mB) s4 = s5 at c1 c2 hM5 z5 o5
  -- the stream's lanes and the signature column in the heap
  have hlane : ∀ u < nCp, rd s5.M (sgB + u) = laneOf w u := fun u hu => by
    rw [c1 u hu, h4 _ (by simp only [regs]; (clear * - hmB; omega)), hw _ (crecIdx_lt hu)]; rfl
  have hsig : ∀ j < 597, rd s5.M (sigB mB + j) = sigCol w j := fun j hj => by
    rw [c2 _ (by simp only [regs, sigB]; (clear * - hmB hj; omega)) (.inl (by simp only [sigB]; (clear * - hmB2 hj; omega))), sigB,
      Nat.add_assoc, h4 _ (by simp only [regs]; (clear * - hmB hj; omega)), hw _ (by (clear * - hj; omega))]; rfl
  -- 6–8. the proof's and the trace's segments
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := setR_sem I s5 hM5 sgB
  rw [semXIR_seq]
  generalize semXIR I (setR sgB) s5 = s6 at r1 r2 r3 r4 r5 r6 r7
  have hc6 : Ctx s5.M sgB false s6 := ⟨r1, r2, r3, r4, by rw [r5]; simp⟩
  have hA := hA_apC (R := sgB) (by simp only [regs, sgB]; norm_num) (by simp only [sgB]; norm_num)
  obtain ⟨g1, g2, g3⟩ := seg_step I hA pSegL segs_ok.2.2.1 segs_ok.2.2.2 s6 hc6 r6
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 pSegL) s6 = s7 at g1 g2 g3
  obtain ⟨k1, k2, k3⟩ := seg_step I hA trSegL segs_ok.1 segs_ok.2.1 s7 g2 g3
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 trSegL) s7 = s8 at k1 k2 k3
  -- the source is the stream below `T`
  have hT : streamLanes pX = 75593 := sizes_P20.2.2.2.2.2.2.1
  have hsrc : ∀ v < streamLanes pX, src s5.M apC sgB v = laneOf w v := fun v hv => by
    rw [src_apC _ (by simp only [sgB]; (clear * - hT hv; omega)), hlane v (by simp only [nCp]; (clear * - hT hv; omega))]
  have eP : segOut (src s5.M apC sgB) false 0 pSegL = pWords (laneOf w) := by
    rw [segOut_pSegL, ← packBytes_reassembleL, readTraceL_congr hsrc, packBytes_reassembleL]
  have eT : segOut (src s5.M apC sgB) false 0 trSegL = trWords (laneOf w) := by
    rw [segOut_trSegL, ← logWords_readTraceL, readTraceL_congr hsrc, logWords_readTraceL]
  -- 9–10. the signature column
  have hM8 := k2.inv
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := setR_sem I s8 hM8 (sigB mB)
  rw [semXIR_seq]
  generalize semXIR I (setR (sigB mB)) s8 = s9 at u1 u2 u3 u4 u5 u6 u7
  have hc9 : Ctx s5.M (sigB mB) false s9 :=
    ⟨u1, by rw [u2, k2.size], fun y hy => by rw [u3 y hy, k2.heap y hy], u4, by rw [u5]; simp⟩
  have hA' := hA_apC (R := sigB mB) (by simp only [regs, sigB]; (clear * - hmB; omega)) (by simp only [sigB, sgB] at hmB2 ⊢; (clear * - hmB hmB2; omega))
  obtain ⟨v1, v2, v3⟩ := seg_step I hA' (.cp 0 597) (by decide) (by decide) s9 hc9 u6
  rw [semXIR_seq]
  generalize semXIR I (segIR apC 0 (.cp 0 597)) s9 = s10 at v1 v2 v3
  have eS : segOut (src s5.M apC (sigB mB)) false 0 (.cp 0 597) = wsAt (sigCol w) 0 597 := by
    simp only [segOut, wsAt, Nat.zero_add]
    exact List.map_congr_left fun j hj => by
      rw [src_apC _ (by simp only [sigB, sgB] at hmB2 ⊢; simp at hj; (clear * - hmB hmB2 hj; omega)), hsig j (by simpa using hj)]
  -- 11–15. the right child
  have hM10 := v2.inv
  obtain ⟨p1, -⟩ := emitIR_sem I s10 hM10 (toWord 48)
  have hM11 := inv_sem I (wf_emitIR (toWord 48)) hM10
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 48)) s10 = s11 at p1 hM11
  obtain ⟨p2, -⟩ := emitIR_sem I s11 hM11 (toWord 0)
  have hM12 := inv_sem I (wf_emitIR (toWord 0)) hM11
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 0)) s11 = s12 at p2 hM12
  obtain ⟨p3, -, hM13, -⟩ := tcpIR_sem I s12 hM12 (a := 15) (n := 5) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (tcpIR 15 5) s12 = s13 at p3 hM13
  obtain ⟨p4, -⟩ := emitIR_sem I s13 hM13 (toWord 0)
  have hM14 := inv_sem I (wf_emitIR (toWord 0)) hM13
  rw [semXIR_seq]
  generalize semXIR I (emitIR (toWord 0)) s13 = s14 at p4 hM14
  obtain ⟨p5, -, -, -⟩ := tcpIR_sem I s14 hM14 (a := 24) (n := 597) (by norm_num)
  -- the words
  rw [p5, p4, p3, p2, p1, v1, u7, k1, g1, r7, o5, o4, o3, o2, o1, eP, eT, eS]
  have t1 := wsAt_tape c π L hs (a := 6) (n := 4) (by norm_num)
  have t2 := wsAt_tape c π L hs (a := 10) (n := 5) (by norm_num)
  have t3 := wsAt_tape c π L hs (a := 19) (n := 597) (by norm_num)
  simp only [show (5 + 6 : ℕ) = 11 from rfl, show (5 + 10 : ℕ) = 15 from rfl,
    show (5 + 19 : ℕ) = 24 from rfl] at t1 t2 t3
  rw [t1, t2, t3, outWords, show (5 : ℕ) = 4 + 1 from rfl, wsAt_add]
  have e19 : wsAt (pw π) 19 597 = wsAt (fun j => pw π (19 + j)) 0 597 := by
    simp only [wsAt, Nat.zero_add]
  rw [e19]
  simp [wsAt, List.append_assoc]

end Lvm.X
end
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem layoutX : pLX = 41547 ∧ capWX = 1777 ∧ cap1WX = 17701 ∧ capRec1Off pX % 8 = 0 ∧
    alphaPos pX 0 = 1244 ∧ f2WX = 17719 ∧ f2Off pX % 8 = 0 ∧ alpha1Pos pX 0 = 1247 := by
  obtain ⟨-, -, h3, h4, h5, -, -, h8, h9, -⟩ := layout_P20
  -- `cap1WX` and `f2WX` in one kernel evaluation: their equation lemmas (`rw [cap1WX]`) made the kernel evaluate
  -- `capRec1Off pX` and `f2Off pX` once each (its `Nat` reduction unfolds `HAdd`/`HDiv` before the constant)
  have hw : cap1WX = 17701 ∧ f2WX = 17719 := by decide +kernel
  refine ⟨?_, ?_, hw.1, ?_, h3, hw.2, ?_, h8⟩
  · rw [pLX, piSize_eq]; rfl
  · rw [capWX, h5]
  · rw [h4]
  · rw [h9]

end Lvm.X
end
