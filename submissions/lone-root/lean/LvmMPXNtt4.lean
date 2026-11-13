-- New for lvm2 roll 11 (M′, R11-X): the forward NTT's semantics at any table dimension `N`. Adapted from
-- `LvmXNtt4.lean` (`fpairBody_nw`, `fpairBody_sem`, `flevelIR_sem`, `flevelIR_nw`, `fPre_sem`, `fwdIR_sem`,
-- `fwdIR_enc`) with the literal `15` replaced by `N`; `lo_farithIR`, `farith_sem` are reused.
import LvmMPXNtt3
import LvmXNtt4

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
    rw [fwdRun_topN N ℓ Y j (by omega), show ℓ - j = (ℓ - (j + 1)) + 1 by omega, fwdRun, fwdTopN,
      show ℓ - (j + 1) = ℓ - 1 - j by omega]

theorem wf_fpairNBody (N : ℕ) : WF (fpairNBody N) := by
  simp +decide [fpairNBody, pairPs, farithIR, alphaNIR, alphaBody, addK, WF, Writes, Prim.dst,
    rQ, uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp,
    regs, mulK_wf_iff, mulK_writes_iff]

theorem fpairNBody_nw {r : ℕ} (hr : r = rA0 ∨ r = rP2 ∨ r = rTr ∨ r = rLv ∨ r = rC1 ∨ r = rN1 ∨
    r = rC3 ∨ r = rN3 ∨ r = rKf ∨ r = rTbf) : ¬ Writes (fpairNBody N) r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide [fpairNBody, pairPs, farithIR, alphaNIR, alphaBody, addK, Writes, Prim.dst, rQ,
    uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, rA0,
    rP2, rTr, rLv, rC1, rN1, rC3, rN3, rKf, rTbf, mulK_writes_iff, or_false]

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
  rw [fpairNBody, semXIR_seq]
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
  obtain ⟨b1, b2⟩ := farith_sem I s2 hM2 (a := A + loP l q) (b := A + hiP l q)
    (by omega) (by simp only [regs]; omega) (by omega) l2 h2
  have hM3 := inv_sem I wf_farithIR hM2
  have z3 := size_sem I farithIR s2
  have hH3 := hframe I farithIR s2 lo_farithIR
  have nwB : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I farithIR s2).M r = rd s2.M r :=
    fun r hr => frame I _ s2 wf_farithIR hM2 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide [farithIR, addK, Writes, Prim.dst, fU, fW, fH, fT, fN, rAL, rAH, rQ,
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
      exact rdK_eq (i7 _ (by simp only [regs]; omega) (by omega))
    obtain ⟨e1, e2, e3, e4⟩ := fpairNBody_sem (hN := hN) I s' i1 (A := A)
      (T := fun i => (wRow ptK N l).getD i 0)
      (by omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
      (by simp only [regs]; omega) hta2 i3 i4 i5 i6 hT'
    have hd : ∀ x, x ≠ rC1 → rd (decS rC1 (semXIR I (fpairNBody N) s')).M x =
        rd (semXIR I (fpairNBody N) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hlo' := i8 _ (by omega : loP l j < 2 ^ ℓ)
    have hhi' := i8 _ hhi
    rw [pairOf_loP, if_neg (lt_irrefl j)] at hlo'
    rw [pairOf_hiP, if_neg (lt_irrefl j)] at hhi'
    refine ⟨inv_decS (inv_sem I (wf_fpairNBody N) i1) (by decide), by rw [size_decS, size_sem, i2], ?_,
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
  have := iterL_ind (f := semXIR I (fpairNBody N)) (c := rC1) (m := 2 ^ (ℓ - 1)) P step (2 ^ (ℓ - 1))
    0 _ (by omega) hP0
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
  refine ⟨?_, ?_, fun x h1 h2 h3 => rd_runPrims_of_not_writes (by
    simp [fPreN, Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩) _⟩
  · simp only [semXIR, runPrims, fPreN, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hK, e1, sub_toWord (by omega) (by omega)]
    congr 1; omega
  · simp only [semXIR, runPrims, fPreN, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hK, e1, sub_toWord (by omega) (by omega), hTb, 
      mul_toWord, add_toWord]
    congr 1; rw [show ℓ - j - 1 = ℓ - 1 - j by omega]; ring

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
  have hℓ64 : ℓ < 2 ^ 64 := by omega
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
    simp (disch := first | decide | (simp only [size_set, rKf, rTbf, rN3]; omega)) only
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
      exact Nat.mul_le_mul_left N (by omega)
    have hT : ∀ i < N, rdK s1.M (tb + N * (ℓ - 1 - j) + i) =
        (wRow ptK N (ℓ - 1 - j)).getD i 0 := fun i hi => by
      rw [← hW (ℓ - 1 - j) (by omega) i (by omega)]
      exact rdK_eq ((hH1 _ (by simp only [regs]; omega)).trans
          (i6 _ (by simp only [regs]; omega) (by omega)))
    have hY1 : ∀ i < 2 ^ ℓ, rdK s1.M (A + i) = fwdTopN N ℓ j Y i := fun i hi => by
      rw [← i7 i hi]
      exact rdK_eq (hH1 _ (by simp only [regs]; omega))
    have a1 : rd s1.M rA0 = toWord A := (p3 _ (by decide) (by decide) (by decide)).trans i5
    obtain ⟨e1, e2, e3⟩ := flevelNIR_sem (hN := hN) I s1 hM1 (Y := fwdTopN N ℓ j Y) (l := ℓ - 1 - j) (by omega)
      (by omega) (by simp only [regs]; omega) hA2 (by omega) (by simp only [regs]; omega)
      (by omega) (by omega) p1 a1 p2 hT hY1
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
      rw [show fwdTopN N ℓ 0 Y i = Y i from rfl, ← hY i hi]
      exact rdK_eq ((hE _ (by simp only [rC3]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
  have := iterL_ind (f := semXIR I ((fStepN N ℓ))) (c := rC3) (m := ℓ) P step ℓ 0 _ (by omega) hP0
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
