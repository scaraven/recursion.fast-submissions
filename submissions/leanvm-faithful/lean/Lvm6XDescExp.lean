-- lvm6 X8a (F-X7b-3, IDX): level 0's `K → E2` expansion. A level-0 row is 46 `K` words, word `t` = slot `45 − t`
-- (FORMAT6 §5); W1 reads lane `s` of the 64-lane row `replicate 18 0 ++ row` at `63 − s` (IDX: the same word for
-- `s < 46`, `getD_pad_shift`). The program `expIR` writes the position-major `E2` word `foldIR` reads: lane `s` of
-- position `p` at `buf + 2 (64 p + s)` is `(row_p[45 − s], 0)` for `s < 46` and `0` for the 18 padding lanes. New.
import Lvm6XDescSbL

/-!
# Level 0's expansion

* **`getD_pad_shift`** (IDX): `(replicate 18 z ++ r).getD (63 − s) z = r.getD (45 − s) z` for `s < 46`.
* **`expIR h base buf`**: zero `[buf, buf + 128·2^h)`, then for `p < 2^h`, `s < 46`: `M[buf + 128 p + 2 s] :=
  M[base + 46 p + 45 − s]` (two nested `loopK`, the source read backwards). **`expIR_sem`**: the values, the frame,
  `Inv`; **`cost_expIR`** `= 37 + 1955·2^h`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

attribute [local irreducible] entryK storeM

/-- **IDX's shift lemma**: W1's padded row read at `63 − s` is X2's row read at `45 − s`, for `s < 46`. -/
theorem getD_pad_shift {α : Type} (r : List α) (z : α) {s : ℕ} (hs : s < 46) :
    (List.replicate 18 z ++ r).getD (63 - s) z = r.getD (45 - s) z := by
  rw [show 63 - s = 18 + (45 - s) by omega, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp

/-! ## The program -/

/-- The source pointer. -/ def xS : ℕ := 190
/-- The destination pointer. -/ def xD : ℕ := 191
/-- A word. -/ def xV : ℕ := 192
/-- `2`. -/ def x2 : ℕ := 193
/-- `92`. -/ def x92 : ℕ := 194
/-- `36`. -/ def x36 : ℕ := 195
/-- The position loop's counter. -/ def xC1 : ℕ := 196
/-- Its count. -/ def xN1 : ℕ := 197
/-- The slot loop's counter. -/ def xC2 : ℕ := 198
/-- Its count. -/ def xN2 : ℕ := 199

/-- One slot: `M[xD] := M[xS]`, `xS −= 1`, `xD += 2`. -/
def expIn : XIR := .seq (sIR [.ld xV xS]) (.seq (.store xD xV) (sIR [.op .sub xS xS cOne, .op .add xD xD x2]))

/-- One position: 46 slots, then the pointers to the next position (`xS += 92`, `xD += 36`). -/
def expOut : XIR := .seq (sIR [.cst xN2 (toWord 46)])
  (.seq (.loopK xC2 xN2 (toWord 46) expIn) (sIR [.op .add xS xS x92, .op .add xD xD x36]))

/-- The prologue. -/
def expPre (h base buf : ℕ) : List SOp := [.cst xS (toWord (base + 45)), .cst xD (toWord buf), .cst x2 (toWord 2),
  .cst x92 (toWord 92), .cst x36 (toWord 36), .cst xN1 (toWord (2 ^ h))]

/-- **Level 0's expansion**: `2^h` positions of 46 `K` words at `base` to `E2` lanes at `buf` (64 lanes each). -/
def expIR (h base buf : ℕ) : XIR :=
  .seq (zeroIR (128 * 2 ^ h) buf) (.seq (sIR (expPre h base buf)) (.loopK xC1 xN1 (toWord (2 ^ h)) expOut))

theorem cost_expIR (h base buf t : ℕ) (hh : 128 * 2 ^ h < 2 ^ 64) :
    cost (expIR h base buf) t = 37 + 1955 * 2 ^ h := by
  have h1 : 2 ^ h < 2 ^ 64 := by omega
  simp only [expIR, expOut, expIn, expPre, cost, cost_sIR, sCost, cost_zeroIR _ _ t hh, toNat_toWord h1,
    toNat_toWord (show 46 < 2 ^ 64 by norm_num)]
  ring

theorem ok_expPre (h base buf : ℕ) : ∀ o ∈ expPre h base buf, o.Ok := by
  simp +decide [expPre, SOp.Ok, regs, xS, xD, x2, x92, x36, xN1]

theorem wf_expIR (h base buf : ℕ) : WF (expIR h base buf) := by
  refine ⟨wf_zeroIR .., wf_sIR _ (ok_expPre h base buf), ⟨by decide, by decide, by decide⟩, by decide, ?_, ?_⟩
  · simp +decide [expOut, expIn, Writes, writes_sIR_iff, SOp.Wr, SOp.dst, SOp.isMul, xN2, xS, xD, xV, xC1, xC2,
      cTmp]
  · refine ⟨wf_sIR _ (by simp +decide [SOp.Ok, regs, xN2]), ⟨⟨by decide, by decide, by decide⟩, by decide, ?_, ?_⟩,
      wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, xS, x92, xD, x36])⟩
    · simp +decide [expIn, Writes, writes_sIR_iff, SOp.Wr, SOp.dst, SOp.isMul, xS, xD, xV, xC2, cTmp]
    · exact ⟨wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, xV, xS]), by simp only [WF]; decide,
        wf_sIR _ (by simp +decide [SOp.Ok, Trk, regs, xS, xD, x2, cOne])⟩

/-! ## The slot loop -/

theorem expA_run (H f : ℕ → Word) {A : ℕ} (hS : f xS = toWord A) (hA : A < 2 ^ 64) (hAr : regs ≤ A) :
    sLd H [.ld xV xS] f ∧ sRun H [.ld xV xS] f xV = H A := by
  replace hS : f 190 = toWord A := hS
  simp only [regs] at hAr
  refine ⟨?_, ?_⟩ <;> simp [sLd, sRun, SOp.LdOk, SOp.step, xV, xS, hS, toNat_toWord hA, regs] <;> omega

theorem expB_run (H f : ℕ → Word) {A D : ℕ} (hS : f xS = toWord A) (hD : f xD = toWord D) (h2 : f x2 = toWord 2)
    (h1 : f cOne = 1) (hA : A < 2 ^ 64) (hA1 : 1 ≤ A) :
    sLd H [.op .sub xS xS cOne, .op .add xD xD x2] f ∧
      sRun H [.op .sub xS xS cOne, .op .add xD xD x2] f xS = toWord (A - 1) ∧
      sRun H [.op .sub xS xS cOne, .op .add xD xD x2] f xD = toWord (D + 2) := by
  replace hS : f 190 = toWord A := hS
  replace hD : f 191 = toWord D := hD
  replace h2 : f 193 = toWord 2 := h2
  replace h1 : f 0 = 1 := h1
  refine ⟨by simp [sLd, SOp.LdOk], ?_, ?_⟩
  · simp only [↓reduceIte, Nat.reduceEqDiff, sRun, SOp.step, Function.update_apply, xS, xD, x2, cOne, hS, hD, h2, h1]
    exact sub_toWord hA hA1
  · simp only [↓reduceIte, Nat.reduceEqDiff, sRun, SOp.step, Function.update_apply, xS, xD, x2, cOne, hS, hD, h2, h1,
      add_toWord]

/-- **The slot loop**: `M[D + 2 s] := M[A − s]` for `s < 46`; `xS = A − 46`, `xD = D + 92`. -/
theorem expInner_sem (I : Array Word) (s : St) (hM : Inv s.M) {A D : ℕ} (hS : rd s.M xS = toWord A)
    (hD : rd s.M xD = toWord D) (h2 : rd s.M x2 = toWord 2) (hN : rd s.M xN2 = toWord 46) (hA : A < 2 ^ 64)
    (hAr : regs + 45 ≤ A) (hDr : regs ≤ D) (hD2 : D + 92 < 2 ^ 64) (hDs : D + 92 ≤ s.M.size)
    (hdis : A < D ∨ D + 92 + 45 ≤ A) :
    let s' := semXIR I (.loopK xC2 xN2 (toWord 46) expIn) s
    Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M xS = toWord (A - 46) ∧ rd s'.M xD = toWord (D + 92) ∧
      rd s'.M x92 = rd s.M x92 ∧ rd s'.M x36 = rd s.M x36 ∧ rd s'.M x2 = rd s.M x2 ∧
      (∀ k < 46, rd s'.M (D + 2 * k) = rd s.M (A - k)) ∧
      ∀ x, regs ≤ x → (x < D ∨ D + 92 ≤ x ∨ (x - D) % 2 = 1) → rd s'.M x = rd s.M x := by
  intro s'
  simp only [regs] at hAr hDr
  let P : ℕ → St → Prop := fun k t ↦ Inv t.M ∧ t.M.size = s.M.size ∧ rd t.M xS = toWord (A - k) ∧
    rd t.M xD = toWord (D + 2 * k) ∧ rd t.M x92 = rd s.M x92 ∧ rd t.M x36 = rd s.M x36 ∧ rd t.M x2 = rd s.M x2 ∧
    (∀ k' < k, rd t.M (D + 2 * k') = rd s.M (A - k')) ∧
    ∀ x, regs ≤ x → (x < D ∨ D + 2 * k ≤ x ∨ (x - D) % 2 = 1) → rd t.M x = rd s.M x
  have hE0 : ∀ i, i ≠ xC2 → i ≠ cTmp → rd (entryK xC2 xN2 (toWord 46) s.M) i = rd s.M i :=
    fun i h1 h2 ↦ entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK xC2 xN2 (toWord 46) s.M, s.o⟩ := by
    refine ⟨inv_entryK hM (by decide), by simp only [size_entryK], ?_, ?_, ?_, ?_, ?_,
      fun k hk ↦ absurd hk (Nat.not_lt_zero _), fun x hx _ ↦ ?_⟩ <;> dsimp only
    · rw [hE0 _ (by decide) (by decide), hS, Nat.sub_zero]
    · rw [hE0 _ (by decide) (by decide), hD, Nat.mul_zero, Nat.add_zero]
    · rw [hE0 _ (by decide) (by decide)]
    · rw [hE0 _ (by decide) (by decide)]
    · rw [hE0 _ (by decide) (by decide)]
    · simp only [regs] at hx
      rw [hE0 _ (by simp only [xC2]; omega) (by simp only [cTmp]; omega)]
  have hstep : ∀ k t, k < 46 → P k t → P (k + 1) (decS xC2 (semXIR I expIn t)) := by
    rintro k t hk ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩
    have ht := i1.1
    simp only [regs] at ht
    obtain ⟨pa0, pa1⟩ := expA_run (rd t.M) (rd t.M) (A := A - k) i3 (by omega) (by simp only [regs]; omega)
    rw [expIn, semXIR_seq]
    obtain ⟨a1, a2, a3, -⟩ := sIR_sem I (rd t.M) [.ld xV xS] t (rd t.M) i1 (by simp +decide [SOp.Ok, Trk, regs, xV, xS])
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) pa0
    have z1 := size_sIR I [.ld xV xS] t
    generalize semXIR I (sIR [.ld xV xS]) t = t1 at a1 a2 a3 z1
    have nA : ∀ r, Trk r → r ≠ xV → rd t1.M r = rd t.M r := fun r hr h ↦ by
      rw [a1 r hr, sRun_frame _ _ _ _ (by simp [SOp.dst]; omega)]
    rw [semXIR_seq]
    obtain ⟨c1, c2, hM2⟩ := store_sem I t1 a3 (p := xD) (v := xV) (x := D + 2 * k) (by decide) (by decide)
      ((nA _ (trkB (by decide) (by decide)) (by decide)).trans i4) (by simp only [regs]; omega) (by omega)
      (by rw [z1, i2]; omega)
    have z2 := size_sem I (.store xD xV) t1
    generalize semXIR I (.store xD xV) t1 = t2 at c1 c2 hM2 z2
    have r2 : ∀ r, Trk r → r ≠ xV → rd t2.M r = rd t.M r := fun r hr h ↦ by
      have := hr.1
      simp only [regs] at this
      rw [c2 r (by omega) (by rcases hr.2 with h' | h' <;> simp only [cTmp] <;> omega), nA r hr h]
    obtain ⟨pb0, pb1, pb2⟩ := expB_run (rd t2.M) (rd t2.M) (A := A - k) (D := D + 2 * k)
      ((r2 _ (trkB (by decide) (by decide)) (by decide)).trans i3)
      ((r2 _ (trkB (by decide) (by decide)) (by decide)).trans i4)
      (((r2 _ (trkB (by decide) (by decide)) (by decide)).trans i7).trans h2)
      (hM2.2 0 (by decide)) (by omega) (by omega)
    obtain ⟨e1, e2, e3, -⟩ := sIR_sem I (rd t2.M) [.op .sub xS xS cOne, .op .add xD xD x2] t2 (rd t2.M) hM2
      (by simp +decide [SOp.Ok, Trk, regs, xS, xD, x2, cOne]) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) pb0
    have z3 := size_sIR I [.op .sub xS xS cOne, .op .add xD xD x2] t2
    generalize semXIR I (sIR [.op .sub xS xS cOne, .op .add xD xD x2]) t2 = t3 at e1 e2 e3 z3
    have hd : ∀ x, x ≠ xC2 → rd (decS xC2 t3).M x = rd t3.M x := fun x hx ↦ rd_decS (Ne.symm hx) _
    have nB : ∀ r, Trk r → r ≠ xS → r ≠ xD → rd t3.M r = rd t2.M r := fun r hr h1 h2 ↦ by
      rw [e1 r hr, sRun_frame _ _ _ _ (by simp [SOp.dst]; omega)]
    have hH : ∀ x, regs ≤ x → x ≠ D + 2 * k → rd (decS xC2 t3).M x = rd t.M x := fun x hx hx' ↦ by
      simp only [regs] at hx
      rw [hd x (by simp only [xC2]; omega), e2 x (by simp only [regs]; omega),
        c2 x hx' (by simp only [cTmp]; omega), a2 x (by simp only [regs]; omega)]
    have v0 : rd (decS xC2 t3).M (D + 2 * k) = rd s.M (A - k) := by
      rw [hd _ (by simp only [xC2]; omega), e2 _ (by simp only [regs]; omega), c1,
        a1 _ (trkB (by decide) (by decide)), pa1, i9 _ (by simp only [regs]; omega) (by omega)]
    refine ⟨inv_decS e3 (by decide), by rw [size_decS, z3, z2, z1, i2], ?_, ?_, ?_, ?_, ?_, fun k' hk' ↦ ?_,
      fun x hx hx' ↦ ?_⟩
    · rw [hd _ (by decide), e1 _ (trkB (by decide) (by decide)), pb1]; congr 1
    · rw [hd _ (by decide), e1 _ (trkB (by decide) (by decide)), pb2]; congr 1
    · rw [hd _ (by decide), nB _ (trkB (by decide) (by decide)) (by decide) (by decide),
        r2 _ (trkB (by decide) (by decide)) (by decide), i5]
    · rw [hd _ (by decide), nB _ (trkB (by decide) (by decide)) (by decide) (by decide),
        r2 _ (trkB (by decide) (by decide)) (by decide), i6]
    · rw [hd _ (by decide), nB _ (trkB (by decide) (by decide)) (by decide) (by decide),
        r2 _ (trkB (by decide) (by decide)) (by decide), i7]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
      · rw [hH _ (by simp only [regs]; omega) (by omega), i8 k' hk']
      · exact v0
    · rw [hH x hx (by omega), i9 x hx (by omega)]
  have hfin := loopK_run I expIn P s hM (c := xC2) (n := xN2) (K := 46) (by decide) (by decide) (by decide) hN
    (by norm_num) h0 hstep
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := hfin
  exact ⟨f1, f2, f3, f4.trans (by norm_num), f5, f6, f7, f8, fun x hx hx' ↦ f9 x hx (by omega)⟩

/-! ## The positions -/

theorem expPre_run (H f : ℕ → Word) (h base buf : ℕ) :
    sLd H (expPre h base buf) f ∧ sRun H (expPre h base buf) f xS = toWord (base + 45) ∧
      sRun H (expPre h base buf) f xD = toWord buf ∧ sRun H (expPre h base buf) f x2 = toWord 2 ∧
      sRun H (expPre h base buf) f x92 = toWord 92 ∧ sRun H (expPre h base buf) f x36 = toWord 36 ∧
      sRun H (expPre h base buf) f xN1 = toWord (2 ^ h) := by
  refine ⟨by simp [expPre, sLd, SOp.LdOk], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [↓reduceIte, Nat.reduceEqDiff, expPre, sRun, SOp.step, Function.update_apply, xS, xD, x2, x92, x36,
      xN1]

theorem expC_run (H f : ℕ → Word) {A D : ℕ} (hS : f xS = toWord A) (hD : f xD = toWord D) (h92 : f x92 = toWord 92)
    (h36 : f x36 = toWord 36) :
    sLd H [.op .add xS xS x92, .op .add xD xD x36] f ∧
      sRun H [.op .add xS xS x92, .op .add xD xD x36] f xS = toWord (A + 92) ∧
      sRun H [.op .add xS xS x92, .op .add xD xD x36] f xD = toWord (D + 36) := by
  replace hS : f 190 = toWord A := hS
  replace hD : f 191 = toWord D := hD
  replace h92 : f 194 = toWord 92 := h92
  replace h36 : f 195 = toWord 36 := h36
  refine ⟨by simp [sLd, SOp.LdOk], ?_, ?_⟩ <;>
    simp only [↓reduceIte, Nat.reduceEqDiff, sRun, SOp.step, Function.update_apply, xS, xD, x92, x36, hS, hD, h92,
      h36, add_toWord]

/-- **Level 0's expansion on the machine**: lane `k` of position `p` (two words at `buf + 2 (64 p + k)`) is
`(M[base + 46 p + 45 − k], 0)` for `k < 46` and `(0, 0)` for the padding lanes; the heap outside
`[buf, buf + 128·2^h)` is kept. -/
theorem expIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {h base buf : ℕ} (hb : regs ≤ base)
    (hb2 : base + 46 * 2 ^ h < 2 ^ 64) (hbuf : regs ≤ buf) (hbuf2 : buf + 128 * 2 ^ h < 2 ^ 64)
    (hsz : buf + 128 * 2 ^ h ≤ s.M.size) (hdis : base + 46 * 2 ^ h ≤ buf ∨ buf + 128 * 2 ^ h ≤ base) :
    let s' := semXIR I (expIR h base buf) s
    Inv s'.M ∧ s'.o = s.o ∧
      (∀ p < 2 ^ h, ∀ k < 64, rd s'.M (buf + 2 * (64 * p + k)) =
        (if k < 46 then rd s.M (base + 46 * p + 45 - k) else 0) ∧ rd s'.M (buf + 2 * (64 * p + k) + 1) = 0) ∧
      ∀ x, regs ≤ x → (x < buf ∨ buf + 128 * 2 ^ h ≤ x) → rd s'.M x = rd s.M x := by
  intro s'
  have hs := hM.1
  have hH : 2 ^ h < 2 ^ 64 := by omega
  simp only [regs] at hb hbuf hs
  have ho : s'.o = s.o := sem_o I _ s (by simp [expIR, expOut, expIn, hasOut, hasOut_sIR, zeroIR, zeroBody])
  suffices H : Inv s'.M ∧ (∀ p < 2 ^ h, ∀ k < 64, rd s'.M (buf + 2 * (64 * p + k)) =
      (if k < 46 then rd s.M (base + 46 * p + 45 - k) else 0) ∧ rd s'.M (buf + 2 * (64 * p + k) + 1) = 0) ∧
      ∀ x, regs ≤ x → (x < buf ∨ buf + 128 * 2 ^ h ≤ x) → rd s'.M x = rd s.M x by
    exact ⟨H.1, ho, H.2.1, H.2.2⟩
  simp only [s', expIR, semXIR_seq]
  -- the zero fill
  obtain ⟨c1, c2, c3⟩ := zeroIR_sem I s hM (n := 128 * 2 ^ h) (dst := buf) (by omega)
    (by simp only [regs]; omega) hbuf2 hsz
  have z1 := size_sem I (zeroIR (128 * 2 ^ h) buf) s
  generalize semXIR I (zeroIR (128 * 2 ^ h) buf) s = s1 at c1 c2 c3 z1
  -- the prologue
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := expPre_run (rd s1.M) (rd s1.M) h base buf
  obtain ⟨a1, a2, a3, -⟩ := sIR_sem I (rd s1.M) (expPre h base buf) s1 (rd s1.M) c3 (ok_expPre h base buf)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) p0
  have z2 := size_sIR I (expPre h base buf) s1
  have q1 := (a1 xS (trkB (by decide) (by decide))).trans p1
  have q2 := (a1 xD (trkB (by decide) (by decide))).trans p2
  have q3 := (a1 x2 (trkB (by decide) (by decide))).trans p3
  have q4 := (a1 x92 (trkB (by decide) (by decide))).trans p4
  have q5 := (a1 x36 (trkB (by decide) (by decide))).trans p5
  have q6 := (a1 xN1 (trkB (by decide) (by decide))).trans p6
  generalize semXIR I (sIR (expPre h base buf)) s1 = s0 at a1 a2 a3 z2 q1 q2 q3 q4 q5 q6
  have hS0 : ∀ x, regs ≤ x → (x < buf ∨ buf + 128 * 2 ^ h ≤ x) → rd s0.M x = rd s.M x := fun x hx hx' ↦ by
    rw [a2 x hx, c2 x hx hx']
  -- the position loop
  let Q : ℕ → St → Prop := fun p t ↦ Inv t.M ∧ t.M.size = s.M.size ∧ rd t.M xS = toWord (base + 46 * p + 45) ∧
    rd t.M xD = toWord (buf + 128 * p) ∧ rd t.M x2 = toWord 2 ∧ rd t.M x92 = toWord 92 ∧ rd t.M x36 = toWord 36 ∧
    (∀ p' < p, ∀ k < 46, rd t.M (buf + 128 * p' + 2 * k) = rd s.M (base + 46 * p' + 45 - k)) ∧
    ∀ x, regs ≤ x → (x < buf ∨ buf + 128 * p ≤ x ∨ (x - buf) % 2 = 1 ∨ 92 ≤ (x - buf) % 128) →
      rd t.M x = rd s0.M x
  have hE0 : ∀ i, i ≠ xC1 → i ≠ cTmp → rd (entryK xC1 xN1 (toWord (2 ^ h)) s0.M) i = rd s0.M i :=
    fun i h1 h2 ↦ entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : Q 0 ⟨entryK xC1 xN1 (toWord (2 ^ h)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK a3 (by decide), by simp only [size_entryK, z2, z1], ?_, ?_, ?_, ?_, ?_,
      fun p' hp' ↦ absurd hp' (Nat.not_lt_zero _), fun x hx _ ↦ ?_⟩ <;> dsimp only
    · rw [hE0 _ (by decide) (by decide), q1, Nat.mul_zero, Nat.add_zero]
    · rw [hE0 _ (by decide) (by decide), q2, Nat.mul_zero, Nat.add_zero]
    · rw [hE0 _ (by decide) (by decide), q3]
    · rw [hE0 _ (by decide) (by decide), q4]
    · rw [hE0 _ (by decide) (by decide), q5]
    · simp only [regs] at hx
      rw [hE0 _ (by simp only [xC1]; omega) (by simp only [cTmp]; omega)]
  have hstep : ∀ p t, p < 2 ^ h → Q p t → Q (p + 1) (decS xC1 (semXIR I expOut t)) := by
    rintro p t hp ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩
    have ht := i1.1
    simp only [regs] at ht
    rw [expOut, semXIR_seq]
    obtain ⟨b1, b2, b3, -⟩ := sIR_sem I (rd t.M) [.cst xN2 (toWord 46)] t (rd t.M) i1
      (by simp +decide [SOp.Ok, regs, xN2]) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by simp [sLd, SOp.LdOk])
    have z3 := size_sIR I [.cst xN2 (toWord 46)] t
    generalize semXIR I (sIR [.cst xN2 (toWord 46)]) t = t1 at b1 b2 b3 z3
    have n1 : ∀ r, Trk r → r ≠ xN2 → rd t1.M r = rd t.M r := fun r hr hr' ↦ by
      rw [b1 r hr, sRun_frame _ _ _ _ (by simp [SOp.dst]; omega)]
    have hN1 : rd t1.M xN2 = toWord 46 := by
      rw [b1 _ (trkB (by decide) (by decide))]; simp [sRun, SOp.step]
    rw [semXIR_seq]
    have hp1 : 46 * p + 46 ≤ 46 * 2 ^ h := by omega
    have hp2 : 128 * p + 128 ≤ 128 * 2 ^ h := by omega
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := expInner_sem I t1 b3 (A := base + 46 * p + 45)
      (D := buf + 128 * p) ((n1 _ (trkB (by decide) (by decide)) (by decide)).trans i3)
      ((n1 _ (trkB (by decide) (by decide)) (by decide)).trans i4)
      ((n1 _ (trkB (by decide) (by decide)) (by decide)).trans i5) hN1 (by omega) (by simp only [regs]; omega)
      (by simp only [regs]; omega) (by omega) (by omega) (by omega)
    generalize semXIR I (.loopK xC2 xN2 (toWord 46) expIn) t1 = t2 at g1 g2 g3 g4 g5 g6 g7 g8 g9
    obtain ⟨e0, e1, e2⟩ := expC_run (rd t2.M) (rd t2.M) g3 g4
      (g5.trans ((n1 _ (trkB (by decide) (by decide)) (by decide)).trans i6))
      (g6.trans ((n1 _ (trkB (by decide) (by decide)) (by decide)).trans i7))
    obtain ⟨d1, d2, d3, -⟩ := sIR_sem I (rd t2.M) [.op .add xS xS x92, .op .add xD xD x36] t2 (rd t2.M) g1
      (by simp +decide [SOp.Ok, Trk, regs, xS, xD, x92, x36]) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) e0
    have z4 := size_sIR I [.op .add xS xS x92, .op .add xD xD x36] t2
    generalize semXIR I (sIR [.op .add xS xS x92, .op .add xD xD x36]) t2 = t3 at d1 d2 d3 z4
    have hd : ∀ x, x ≠ xC1 → rd (decS xC1 t3).M x = rd t3.M x := fun x hx ↦ rd_decS (Ne.symm hx) _
    have nC : ∀ r, Trk r → r ≠ xS → r ≠ xD → rd t3.M r = rd t2.M r := fun r hr h1 h2 ↦ by
      rw [d1 r hr, sRun_frame _ _ _ _ (by simp [SOp.dst]; omega)]
    have hT : ∀ x, regs ≤ x → rd (decS xC1 t3).M x = rd t2.M x := fun x hx ↦ by
      simp only [regs] at hx
      rw [hd x (by simp only [xC1]; omega), d2 x (by simp only [regs]; omega)]
    refine ⟨inv_decS d3 (by decide), by rw [size_decS, z4, g2, z3, i2], ?_, ?_, ?_, ?_, ?_,
      fun p' hp' k hk ↦ ?_, fun x hx hx' ↦ ?_⟩
    · rw [hd _ (by decide), d1 _ (trkB (by decide) (by decide)), e1]; congr 1; omega
    · rw [hd _ (by decide), d1 _ (trkB (by decide) (by decide)), e2]; congr 1
    · rw [hd _ (by decide), nC _ (trkB (by decide) (by decide)) (by decide) (by decide), g7,
        n1 _ (trkB (by decide) (by decide)) (by decide), i5]
    · rw [hd _ (by decide), nC _ (trkB (by decide) (by decide)) (by decide) (by decide), g5,
        n1 _ (trkB (by decide) (by decide)) (by decide), i6]
    · rw [hd _ (by decide), nC _ (trkB (by decide) (by decide)) (by decide) (by decide), g6,
        n1 _ (trkB (by decide) (by decide)) (by decide), i7]
    · rw [hT _ (by simp only [regs]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp' with hp' | rfl
      · rw [g9 _ (by simp only [regs]; omega) (Or.inl (by omega)), b2 _ (by simp only [regs]; omega),
          i8 p' hp' k hk]
      · rw [g8 k hk, b2 _ (by simp only [regs]; omega), i9 _ (by simp only [regs]; omega) (by omega),
          hS0 _ (by simp only [regs]; omega) (by omega)]
    · rw [hT x hx, g9 x hx (by omega), b2 x hx, i9 x hx (by omega)]
  have hfin := loopK_run I expOut Q s0 a3 (c := xC1) (n := xN1) (K := 2 ^ h) (by decide) (by decide)
    (by decide) q6 hH h0 hstep
  obtain ⟨f1, -, -, -, -, -, -, f8, f9⟩ := hfin
  refine ⟨f1, fun p hp k hk ↦ ⟨?_, ?_⟩, fun x hx hx' ↦ ?_⟩
  · split_ifs with hk46
    · rw [show buf + 2 * (64 * p + k) = buf + 128 * p + 2 * k by ring]
      exact f8 p hp k hk46
    · rw [f9 _ (by simp only [regs]; omega) (by omega), a2 _ (by simp only [regs]; omega)]
      exact c1 (2 * (64 * p + k)) (by omega)
  · have e := c1 (2 * (64 * p + k) + 1) (by omega)
    rw [← Nat.add_assoc] at e
    rw [f9 _ (by simp only [regs]; omega) (by omega), a2 _ (by simp only [regs]; omega), e]
  · rw [f9 x hx (by omega), hS0 x hx hx']

end Lvm6.X
