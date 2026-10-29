-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, the next level's message; stage S-H2,
-- track L-ext).
import FRXFlag
import FRXReadLv

/-!
# The next message's two coordinate rows on the machine

Level `i`'s flags compare the fold with `Enc(f⁽ⁱ⁺¹⁾)` in `F` coordinates
(`FRXLevel.mem_consSet_iff`). `fwdIR` computes `Enc` of a zero-padded `F` row, so the next
message `nextMsg κ L es i` is laid out as two rows, `X[x] = (nextMsg x).f₀` at `xb + 2x` and
`Y[x] = (nextMsg x).f₁` at `yb + 2x`, zero from the message's length on.

* `zeroIR n b`: the words `b … b + n − 1` are zero (`zeroIR_sem`);
* `finIR k tw xb yb` (level 4): K element `x < k` from the tape words `tw + 4x … tw + 4x + 3`
  (`finIR_sem`); with `tw = finW = 5 + 64,640/8`, π's final field (A.3 field 13, revision 3.13),
  `tapeF_fin`, and with the chain link `finalAt es = finPi π`, `nextMsg 4` (`msg4_next`);
* `gathIR k ob xb yb` (levels 0–3): K element `x < 8k` from the decoded rows of the next level
  (row `c` at `ob + 2kc`): rows `2(x mod 8)` and `2(x mod 8) + 1`, column `x div 8`
  (`FRXLevel.nextMsg_coords`), `gathIR_sem`, and `nextMsg i` (`msgH_next`).
* `msgTIR`, `msgHIR`: both rows zeroed (`2^n` entries), then the tape or the gathered elements.

Registers `190 … 207` (free at this point of the decoder).
-/

namespace FR.X

open RecursionFast FR Finset

attribute [local irreducible] entryK storeM runPrims

/-! ## Registers -/

/-- A store pointer. -/ def mP : ℕ := 190
/-- A zero word. -/ def mZ : ℕ := 191
/-- Loop counter. -/ def mC : ℕ := 192
/-- Its count. -/ def mN : ℕ := 193
/-- The tape position. -/ def mA : ℕ := 194
/-- The `X` pointer. -/ def mX : ℕ := 195
/-- The `Y` pointer. -/ def mY : ℕ := 196
/-- The stores' scratch. -/ def mX1 : ℕ := 197
/-- Constant scratch. -/ def mK : ℕ := 198
/-- Address scratch. -/ def mT : ℕ := 199
/-- Address scratch. -/ def mU : ℕ := 200
/-- The source address. -/ def mS : ℕ := 201
/-- The loads' scratch. -/ def mS1 : ℕ := 202
/-- The position `x`. -/ def mJ : ℕ := 203
/-- The four words of a K element. -/ def mV : ℕ := 204

/-! ## Zeroing -/

/-- `mP := b`, `mZ := 0`, the count. -/
def zPre (n b : ℕ) : List Prim := [.const mP (toWord b), .const mZ 0, .const mN (toWord n)]

/-- `M[mP] := 0`, `mP += 1`. -/
def zBody : XIR := .seq (.store mP mZ) (.blk [.op .add mP mP cOne])

/-- **The words `b … b + n − 1` set to zero.** -/
def zeroIR (n b : ℕ) : XIR := .seq (.blk (zPre n b)) (.loopK mC mN (toWord n) zBody)

theorem wf_zeroIR (n b : ℕ) : WF (zeroIR n b) := by
  simp +decide only [zeroIR, zPre, zBody, WF, Writes, Prim.dst, mP, mZ, mC, mN, cTmp, regs,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem noLoopT_zeroIR (n b : ℕ) : NoLoopT (zeroIR n b) := by simp [zeroIR, zBody, NoLoopT]

theorem outs_zeroIR (n b t : ℕ) : outs (zeroIR n b) t = 0 := by simp [zeroIR, zBody, outs]

theorem cost_zeroIR (n b t : ℕ) (hn : n < 2 ^ 64) : cost (zeroIR n b) t = 14 + 9 * n := by
  have a : (toWord n).toNat = n := toNat_toWord hn
  simp only [zeroIR, zPre, zBody, cost, blkSteps, List.length_cons, List.length_nil, a]
  norm_num; ring

theorem zPre_sem (I : Array Word) (s : St) (hM : Inv s.M) (n b : ℕ) :
    rd (semXIR I (.blk (zPre n b)) s).M mP = toWord b ∧ rd (semXIR I (.blk (zPre n b)) s).M mZ = 0 ∧
    rd (semXIR I (.blk (zPre n b)) s).M mN = toWord n ∧
    (∀ i, i ≠ mP → i ≠ mZ → i ≠ mN → rd (semXIR I (.blk (zPre n b)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (zPre n b)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk (zPre n b)) s = ⟨runPrims (zPre n b) s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, ?_, ?_, fun i h1 h2 h3 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [zPre, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3) _,
    inv_runPrims (by simp [zPre, Prim.dst, mP, mZ, mN]) hM⟩
  all_goals simp only [zPre, runPrims, List.foldl, Prim.run]
  all_goals simp (disch := first | decide | (simp only [size_set, mP, mZ, mN]; omega)) only
      [rd_set_self, rd_set_ne]

/-- **Zeroing**: `zeroIR n b` leaves `0` at `b + w` for every `w < n` and keeps the heap
outside `[b, b + n)`. -/
theorem zeroIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n b : ℕ} (hn : n < 2 ^ 64)
    (hb : regs ≤ b) (hb2 : b + n < 2 ^ 64) (hsz : b + n ≤ s.M.size) :
    (∀ w < n, rd (semXIR I (zeroIR n b) s).M (b + w) = 0) ∧
    (∀ i, regs ≤ i → (i < b ∨ b + n ≤ i) → rd (semXIR I (zeroIR n b) s).M i = rd s.M i) ∧
    Inv (semXIR I (zeroIR n b) s).M := by
  have hs := hM.1
  simp only [regs] at hs hb
  obtain ⟨r1, r2, r3, r4, hM0⟩ := zPre_sem I s hM n b
  have z0 := size_sem I (.blk (zPre n b)) s
  rw [zeroIR, semXIR_seq]
  generalize semXIR I (.blk (zPre n b)) s = s0 at r1 r2 r3 r4 hM0 z0
  let P : ℕ → St → Prop := fun w s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M mP = toWord (b + w) ∧ rd s'.M mZ = 0 ∧ (∀ v < w, rd s'.M (b + v) = 0) ∧
    ∀ i, regs ≤ i → (i < b ∨ b + w ≤ i) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ mC → i ≠ cTmp → rd (entryK mC mN (toWord n) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have p0 : P 0 ⟨entryK mC mN (toWord n) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun v hv => absurd hv (Nat.not_lt_zero _), fun i hi _ => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), r1, Nat.add_zero]
    · dsimp only; rw [hE _ (by decide) (by decide), r2]
    · dsimp only
      rw [hE _ (by simp only [mC, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        r4 _ (by simp only [mP, regs] at *; omega) (by simp only [mZ, regs] at *; omega)
          (by simp only [mN, regs] at *; omega)]
  have step : ∀ w s', w < n → P w s' → P (w + 1) (decS mC (semXIR I zBody s')) := by
    rintro w s' hw ⟨i1, i2, i3, i4, i5, i6⟩
    have st : ∀ i, i ≠ cTmp → rd (storeM s'.M mP mZ) i =
        if i = b + w then rd s'.M mZ else rd s'.M i :=
      fun i hi => rd_storeM i1 i3 (by simp only [regs]; omega) (by omega) (by omega) (by decide)
        (by decide) hi
    have hM1 : Inv (storeM s'.M mP mZ) := inv_of_frame i1 (size_storeM ..) fun i hi => by
      rw [st i (by simp only [cTmp]; omega), if_neg (by omega)]
    have e1 : semXIR I zBody s' = ⟨runPrims [.op .add mP mP cOne] (storeM s'.M mP mZ), s'.o⟩ := rfl
    have hP1 : rd (storeM s'.M mP mZ) mP = toWord (b + w) := by
      rw [st _ (by decide), if_neg (by simp only [mP]; omega), i3]
    obtain ⟨n1, n2⟩ := incr_sem _ hM1 (r := mP) (by decide) (by decide) hP1
    have hd : ∀ i, i ≠ mC → rd (decS mC (semXIR I zBody s')).M i = rd (semXIR I zBody s').M i :=
      fun i h => rd_decS (Ne.symm h) _
    rw [e1] at hd ⊢
    refine ⟨inv_decS (inv_runPrims (by simp [Prim.dst, mP]) hM1) (by decide),
      by rw [size_decS, size_runPrims, size_storeM, i2], ?_, ?_, fun v hv => ?_, fun i hi hi2 => ?_⟩
    · rw [hd _ (by decide), n1, Nat.add_assoc]
    · rw [hd _ (by decide), n2 _ (by decide), st _ (by decide), if_neg (by simp only [mZ]; omega), i4]
    · rw [hd _ (by simp only [mC]; omega), n2 _ (by simp only [mP]; omega),
        st _ (by simp only [cTmp]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | rfl
      · rw [if_neg (by omega), i5 v h]
      · rw [if_pos rfl, i4]
    · simp only [regs] at hi
      rw [hd _ (by simp only [mC]; omega), n2 _ (by simp only [mP]; omega),
        st _ (by simp only [cTmp]; omega), if_neg (by omega), i6 i (by simp only [regs]; omega)
        (hi2.imp_right fun h => by omega)]
  have hN : rd s0.M mN = toWord n := r3
  have := loopK_run I zBody P s0 hM0 (by decide) (by decide) (by decide) hN hn p0 step
  exact ⟨this.2.2.2.2.1, fun i hi hi2 => this.2.2.2.2.2 i hi hi2, this.1⟩

/-! ## The final message from the tape (level 4) -/

/-- `mA := tw`, `mX := xb`, `mY := yb`, the count. -/
def finPre (k tw xb yb : ℕ) : List Prim :=
  [.const mA (toWord tw), .const mX (toWord xb), .const mY (toWord yb), .const mN (toWord k)]

/-- One tape word from `mA` into `d`; `mA += 1`. -/
def inW (d : ℕ) : XIR := .seq (.input d mA) (.blk [.op .add mA mA cOne])

/-- The four tape words from `mA` into `mV … mV + 3`; `mA += 4`. -/
def finIn : XIR := .seq (inW mV) (.seq (inW (mV + 1)) (.seq (inW (mV + 2)) (inW (mV + 3))))

/-- One K element: `f₀` to `X`, `f₁` to `Y`; `mX += 2`, `mY += 2`. -/
def finBody : XIR :=
  .seq finIn (.seq (stF mX mX1 mV) (.seq (stF mY mX1 (mV + 2))
    (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK])))

/-- **`k` K elements from the tape** at `tw`: element `x` from words `tw + 4x … tw + 4x + 3`,
`f₀` to `xb + 2x`, `f₁` to `yb + 2x`. -/
def finIR (k tw xb yb : ℕ) : XIR := .seq (.blk (finPre k tw xb yb)) (.loopK mC mN (toWord k) finBody)

theorem wf_finIR (k tw xb yb : ℕ) : WF (finIR k tw xb yb) := by
  simp +decide only [finIR, finPre, finBody, finIn, inW, stF, WF, Writes, Prim.dst, mA, mX, mY, mX1,
    mK, mV, mC, mN, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]

theorem noLoopT_finIR (k tw xb yb : ℕ) : NoLoopT (finIR k tw xb yb) := by
  simp [finIR, finBody, finIn, inW, stF, NoLoopT]

theorem outs_finIR (k tw xb yb t : ℕ) : outs (finIR k tw xb yb) t = 0 := by
  simp [finIR, finBody, finIn, inW, stF, outs]

theorem cost_finIR (k tw xb yb t : ℕ) (hk : k < 2 ^ 64) : cost (finIR k tw xb yb) t = 16 + 48 * k := by
  have a : (toWord k).toNat = k := toNat_toWord hk
  simp only [finIR, finPre, finBody, finIn, inW, stF, cost, blkSteps, List.length_cons,
    List.length_nil, a]
  norm_num; ring

theorem inW_sem (I : Array Word) (s : St) (hM : Inv s.M) {d a : ℕ} (hd4 : 4 ≤ d) (hdr : d < regs)
    (hdA : d ≠ mA) (ha : a + 1 < 2 ^ 64) (hA : rd s.M mA = toWord a) :
    rd (semXIR I (inW d) s).M d = I.getD a 0 ∧ rd (semXIR I (inW d) s).M mA = toWord (a + 1) ∧
    (∀ i, i ≠ d → i ≠ mA → rd (semXIR I (inW d) s).M i = rd s.M i) ∧
    Inv (semXIR I (inW d) s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs hdr
  have t0 : (toWord a).toNat = a := toNat_toWord (by omega)
  have e : semXIR I (inW d) s = ⟨runPrims [.op .add mA mA cOne]
      (s.M.setIfInBounds d (I.getD (rd s.M mA).toNat 0)), s.o⟩ := rfl
  rw [e]
  generalize hM1 : s.M.setIfInBounds d (I.getD (rd s.M mA).toNat 0) = M1
  have a1 : rd M1 d = I.getD a 0 := by rw [← hM1, rd_set_self (by omega), hA, t0]
  have a2 : ∀ i, i ≠ d → rd M1 i = rd s.M i := fun i hi => by rw [← hM1, rd_set_ne (Ne.symm hi)]
  have hI1 : Inv M1 := inv_of_frame hM (by rw [← hM1, size_set]) fun i hi => a2 i (by omega)
  obtain ⟨n1, n2⟩ := incr_sem M1 hI1 (r := mA) (by decide) (by decide) ((a2 _ (Ne.symm hdA)).trans hA)
  exact ⟨by rw [n2 _ hdA, a1], n1, fun i h1 h2 => by rw [n2 _ h2, a2 _ h1],
    inv_runPrims (by simp [Prim.dst, mA]) hI1⟩

theorem finIn_sem (I : Array Word) (s : St) (hM : Inv s.M) {a : ℕ} (ha : a + 4 < 2 ^ 64)
    (hA : rd s.M mA = toWord a) :
    rd (semXIR I finIn s).M mV = I.getD a 0 ∧ rd (semXIR I finIn s).M (mV + 1) = I.getD (a + 1) 0 ∧
    rd (semXIR I finIn s).M (mV + 2) = I.getD (a + 2) 0 ∧
    rd (semXIR I finIn s).M (mV + 3) = I.getD (a + 3) 0 ∧
    rd (semXIR I finIn s).M mA = toWord (a + 4) ∧
    (∀ i, i ≠ mV → i ≠ mV + 1 → i ≠ mV + 2 → i ≠ mV + 3 → i ≠ mA →
      rd (semXIR I finIn s).M i = rd s.M i) ∧
    Inv (semXIR I finIn s).M := by
  rw [finIn, semXIR_seq]
  obtain ⟨a1, a2, a3, hM1⟩ := inW_sem I s hM (d := mV) (by decide) (by decide) (by decide)
    (by omega) hA
  generalize semXIR I (inW mV) s = s1 at a1 a2 a3 hM1
  rw [semXIR_seq]
  obtain ⟨b1, b2, b3, hM2⟩ := inW_sem I s1 hM1 (d := mV + 1) (by decide) (by decide) (by decide)
    (by omega) a2
  generalize semXIR I (inW (mV + 1)) s1 = s2 at b1 b2 b3 hM2
  rw [semXIR_seq]
  obtain ⟨c1, c2, c3, hM3⟩ := inW_sem I s2 hM2 (d := mV + 2) (by decide) (by decide) (by decide)
    (by omega) b2
  generalize semXIR I (inW (mV + 2)) s2 = s3 at c1 c2 c3 hM3
  obtain ⟨d1, d2, d3, hM4⟩ := inW_sem I s3 hM3 (d := mV + 3) (by decide) (by decide) (by decide)
    (by omega) c2
  generalize semXIR I (inW (mV + 3)) s3 = s4 at d1 d2 d3 hM4
  refine ⟨?_, ?_, ?_, d1, d2, fun i i1 i2 i3 i4 i5 => ?_, hM4⟩
  · rw [d3 _ (by decide) (by decide), c3 _ (by decide) (by decide), b3 _ (by decide) (by decide),
      a1]
  · rw [d3 _ (by decide) (by decide), c3 _ (by decide) (by decide), b1]
  · rw [d3 _ (by decide) (by decide), c1]
  · rw [d3 _ i4 i5, c3 _ i3 i5, b3 _ i2 i5, a3 _ i1 i5]

/-- `mX += 2`, `mY += 2`. -/
theorem stepXY_sem (I : Array Word) (s : St) (hM : Inv s.M) {x y : ℕ} (hX : rd s.M mX = toWord x)
    (hY : rd s.M mY = toWord y) :
    rd (semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s).M mX = toWord (x + 2) ∧
    rd (semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s).M mY = toWord (y + 2) ∧
    (∀ i, i ≠ mK → i ≠ mX → i ≠ mY →
      rd (semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s =
      ⟨runPrims [.const mK 2, .op .add mX mX mK, .op .add mY mY mK] s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, ?_, fun i h1 h2 h3 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3) _,
    inv_runPrims (by simp [Prim.dst, mK, mX, mY]) hM⟩
  all_goals simp only [runPrims, List.foldl, Prim.run]
  all_goals simp (disch := first | decide | (simp only [size_set, mK, mX, mY]; omega)) only
    [rd_set_self, rd_set_ne]
  · rw [hX, show (2 : Word) = toWord 2 from rfl, add_toWord]
  · rw [hY, show (2 : Word) = toWord 2 from rfl, add_toWord]

/-- The `F` pair of tape words `a`, `a + 1`. -/
def tapeF (I : Array Word) (a : ℕ) : F := ⟨wB (I.getD a 0), wB (I.getD (a + 1) 0)⟩

/-- **The final message's rows**: `finIR k tw xb yb` leaves at `xb + 2x` and `yb + 2x` the
`F` pairs of tape words `tw + 4x` and `tw + 4x + 2` (`x < k`), and keeps the heap outside the
two rows. -/
theorem finIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k tw xb yb : ℕ} (hk : k < 2 ^ 64)
    (htw : tw + 4 * k < 2 ^ 64) (hxb : regs ≤ xb) (hxb2 : xb + 2 * k < 2 ^ 64)
    (hyb : regs ≤ yb) (hyb2 : yb + 2 * k < 2 ^ 64) (hxs : xb + 2 * k ≤ s.M.size)
    (hys : yb + 2 * k ≤ s.M.size) (hd : xb + 2 * k ≤ yb ∨ yb + 2 * k ≤ xb) :
    (∀ x < k, rdF (semXIR I (finIR k tw xb yb) s).M (xb + 2 * x) = tapeF I (tw + 4 * x) ∧
      rdF (semXIR I (finIR k tw xb yb) s).M (yb + 2 * x) = tapeF I (tw + 4 * x + 2)) ∧
    (∀ i, regs ≤ i → (i < xb ∨ xb + 2 * k ≤ i) → (i < yb ∨ yb + 2 * k ≤ i) →
      rd (semXIR I (finIR k tw xb yb) s).M i = rd s.M i) ∧
    Inv (semXIR I (finIR k tw xb yb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hxb hyb
  have hw0 : WF (.blk (finPre k tw xb yb)) := by simp +decide only [finPre, WF, Prim.dst, mA, mX,
    mY, mN, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have e0 : semXIR I (.blk (finPre k tw xb yb)) s = ⟨runPrims (finPre k tw xb yb) s.M, s.o⟩ := rfl
  have r0 : rd (runPrims (finPre k tw xb yb) s.M) mA = toWord tw ∧
      rd (runPrims (finPre k tw xb yb) s.M) mX = toWord xb ∧
      rd (runPrims (finPre k tw xb yb) s.M) mY = toWord yb ∧
      rd (runPrims (finPre k tw xb yb) s.M) mN = toWord k := by
    simp only [finPre, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp (disch := first | decide | (simp only [size_set, mA, mX, mY, mN]; omega)) only
        [rd_set_self, rd_set_ne]
  have r4 : ∀ i, regs ≤ i → rd (runPrims (finPre k tw xb yb) s.M) i = rd s.M i := fun i hi =>
    rd_runPrims_of_not_writes (by
      simp only [finPre, List.mem_cons, List.mem_nil_iff, or_false]
      simp only [regs] at hi
      rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, mA, mX, mY, mN] <;> omega) _
  have hM0 : Inv (runPrims (finPre k tw xb yb) s.M) := by
    have h := inv_sem I hw0 hM; rwa [e0] at h
  have z0 : (runPrims (finPre k tw xb yb) s.M).size = s.M.size := size_runPrims _ _
  rw [finIR, semXIR_seq, e0]
  generalize runPrims (finPre k tw xb yb) s.M = M0 at r0 r4 hM0 z0
  obtain ⟨r1, r2, r3, rN⟩ := r0
  let P : ℕ → St → Prop := fun x s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M mA = toWord (tw + 4 * x) ∧ rd s'.M mX = toWord (xb + 2 * x) ∧
    rd s'.M mY = toWord (yb + 2 * x) ∧
    (∀ v < x, rdF s'.M (xb + 2 * v) = tapeF I (tw + 4 * v) ∧
      rdF s'.M (yb + 2 * v) = tapeF I (tw + 4 * v + 2)) ∧
    ∀ i, regs ≤ i → (i < xb ∨ xb + 2 * x ≤ i) → (i < yb ∨ yb + 2 * x ≤ i) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ mC → i ≠ cTmp → rd (entryK mC mN (toWord k) M0) i = rd M0 i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have p0 : P 0 ⟨entryK mC mN (toWord k) M0, s.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_, ?_,
      fun v hv => absurd hv (Nat.not_lt_zero _), fun i hi _ _ => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), r1, Nat.mul_zero, Nat.add_zero]
    · dsimp only; rw [hE _ (by decide) (by decide), r2, Nat.mul_zero, Nat.add_zero]
    · dsimp only; rw [hE _ (by decide) (by decide), r3, Nat.mul_zero, Nat.add_zero]
    · dsimp only
      rw [hE _ (by simp only [mC, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        r4 i hi]
  have step : ∀ x s', x < k → P x s' → P (x + 1) (decS mC (semXIR I finBody s')) := by
    rintro x s' hx ⟨i1, i2, i3, i4, i5, i6, i7⟩
    rw [finBody, semXIR_seq]
    obtain ⟨a1, a2, a3, a4, a5, a6, hM1⟩ := finIn_sem I s' i1 (a := tw + 4 * x) (by omega) i3
    have z1 := size_sem I finIn s'
    generalize semXIR I finIn s' = s1 at a1 a2 a3 a4 a5 a6 hM1 z1
    rw [semXIR_seq]
    have hX1 : rd s1.M mX = toWord (xb + 2 * x) := (a6 _ (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans i4
    obtain ⟨b1, b2, hM2⟩ := stF_sem I s1 hM1 (p := mX) (p1 := mX1) (v := mV) (x := xb + 2 * x)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hX1 (by simp only [regs]; omega) (by omega) (by omega)
    have z2 := size_sem I (stF mX mX1 mV) s1
    generalize semXIR I (stF mX mX1 mV) s1 = s2 at b1 b2 hM2 z2
    rw [semXIR_seq]
    have hY2 : rd s2.M mY = toWord (yb + 2 * x) :=
      (b2 _ (by simp only [mY]; omega) (by simp only [mY]; omega) (by decide) (by decide)).trans
        ((a6 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans i5)
    obtain ⟨c1, c2, hM3⟩ := stF_sem I s2 hM2 (p := mY) (p1 := mX1) (v := mV + 2) (x := yb + 2 * x)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hY2 (by simp only [regs]; omega) (by omega) (by omega)
    have z3 := size_sem I (stF mY mX1 (mV + 2)) s2
    generalize semXIR I (stF mY mX1 (mV + 2)) s2 = s3 at c1 c2 hM3 z3
    have hX3 : rd s3.M mX = toWord (xb + 2 * x) :=
      (c2 _ (by simp only [mX]; omega) (by simp only [mX]; omega) (by decide) (by decide)).trans
        ((b2 _ (by simp only [mX]; omega) (by simp only [mX]; omega) (by decide) (by decide)).trans hX1)
    have hY3 : rd s3.M mY = toWord (yb + 2 * x) :=
      (c2 _ (by simp only [mY]; omega) (by simp only [mY]; omega) (by decide) (by decide)).trans hY2
    obtain ⟨d1, d2, d3, hM4⟩ := stepXY_sem I s3 hM3 hX3 hY3
    have z4 := size_sem I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s3
    generalize semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s3 = s4
      at d1 d2 d3 hM4 z4
    have hd : ∀ i, i ≠ mC → rd (decS mC s4).M i = rd s4.M i := fun i h => rd_decS (Ne.symm h) _
    -- the heap of `s4`
    have h4 : ∀ i, regs ≤ i → i ≠ xb + 2 * x → i ≠ xb + 2 * x + 1 → i ≠ yb + 2 * x →
        i ≠ yb + 2 * x + 1 → rd s4.M i = rd s'.M i := fun i hi j1 j2 j3 j4 => by
      simp only [regs] at hi
      rw [d3 i (by simp only [mK]; omega) (by simp only [mX]; omega) (by simp only [mY]; omega),
        c2 i j3 j4 (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
        b2 i j1 j2 (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
        a6 i (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mV]; omega)
          (by simp only [mV]; omega) (by simp only [mA]; omega)]
    have hX4 : rdF s4.M (xb + 2 * x) = tapeF I (tw + 4 * x) := by
      have e1 : rdF s4.M (xb + 2 * x) = rdF s2.M (xb + 2 * x) :=
        rdF_eq ((d3 _ (by simp only [mK]; omega) (by simp only [mX]; omega)
          (by simp only [mY]; omega)).trans (c2 _ (by omega) (by omega) (by simp only [mX1]; omega)
          (by simp only [cTmp]; omega)))
          ((d3 _ (by simp only [mK]; omega) (by simp only [mX]; omega)
          (by simp only [mY]; omega)).trans (c2 _ (by omega) (by omega) (by simp only [mX1]; omega)
          (by simp only [cTmp]; omega)))
      rw [e1, b1, tapeF]
      simp only [rdF, rdB, a1, a2]
    have hY4 : rdF s4.M (yb + 2 * x) = tapeF I (tw + 4 * x + 2) := by
      have e1 : rdF s4.M (yb + 2 * x) = rdF s3.M (yb + 2 * x) :=
        rdF_eq (d3 _ (by simp only [mK]; omega) (by simp only [mX]; omega)
          (by simp only [mY]; omega)) (d3 _ (by simp only [mK]; omega) (by simp only [mX]; omega)
          (by simp only [mY]; omega))
      have e2 : rd s2.M (mV + 2) = rd s1.M (mV + 2) := b2 _ (by simp only [mV]; omega)
        (by simp only [mV]; omega) (by decide) (by decide)
      have e3 : rd s2.M (mV + 2 + 1) = rd s1.M (mV + 3) := b2 _ (by simp only [mV]; omega)
        (by simp only [mV]; omega) (by decide) (by decide)
      rw [e1, c1, tapeF]
      simp only [rdF, rdB, e2, e3, a3, a4]
    refine ⟨inv_decS hM4 (by decide), by rw [size_decS, z4, z3, z2, z1, i2], ?_, ?_, ?_,
      fun v hv => ?_, fun i hi hi2 hi3 => ?_⟩
    · rw [hd _ (by decide), d3 _ (by decide) (by decide) (by decide), c2 _ (by simp only [mA]; omega)
        (by simp only [mA]; omega) (by decide) (by decide), b2 _ (by simp only [mA]; omega)
        (by simp only [mA]; omega) (by decide) (by decide), a5]
      exact congrArg toWord (by ring)
    · rw [hd _ (by decide), d1]; exact congrArg toWord (by ring)
    · rw [hd _ (by decide), d2]; exact congrArg toWord (by ring)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | rfl
      · have g := i6 v h
        constructor
        · rw [← g.1]
          exact rdF_eq ((hd _ (by simp only [mC]; omega)).trans
            (h4 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
            ((hd _ (by simp only [mC]; omega)).trans
            (h4 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
        · rw [← g.2]
          exact rdF_eq ((hd _ (by simp only [mC]; omega)).trans
            (h4 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
            ((hd _ (by simp only [mC]; omega)).trans
            (h4 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
      · exact ⟨(rdF_eq (hd _ (by simp only [mC]; omega)) (hd _ (by simp only [mC]; omega))).trans hX4,
          (rdF_eq (hd _ (by simp only [mC]; omega)) (hd _ (by simp only [mC]; omega))).trans hY4⟩
    · simp only [regs] at hi
      rw [hd _ (by simp only [mC]; omega), h4 i (by simp only [regs]; omega) (by omega) (by omega)
        (by omega) (by omega), i7 i (by simp only [regs]; omega) (hi2.imp_right fun h => by omega)
        (hi3.imp_right fun h => by omega)]
  have := loopK_run I finBody P ⟨M0, s.o⟩ hM0 (by decide) (by decide) (by decide) rN hk p0 step
  exact ⟨this.2.2.2.2.2.1, this.2.2.2.2.2.2, this.1⟩

/-! ## Level 4's message rows -/

/-- **The rows of a tape message**: both rows of `2^n` entries zeroed, then `k` K elements from
the tape at `tw`. -/
def msgTIR (n k tw xb yb : ℕ) : XIR :=
  .seq (zeroIR (2 * 2 ^ n) xb) (.seq (zeroIR (2 * 2 ^ n) yb) (finIR k tw xb yb))

theorem wf_msgTIR (n k tw xb yb : ℕ) : WF (msgTIR n k tw xb yb) :=
  ⟨wf_zeroIR _ _, wf_zeroIR _ _, wf_finIR _ _ _ _⟩

theorem noLoopT_msgTIR (n k tw xb yb : ℕ) : NoLoopT (msgTIR n k tw xb yb) :=
  ⟨noLoopT_zeroIR _ _, noLoopT_zeroIR _ _, noLoopT_finIR _ _ _ _⟩

theorem outs_msgTIR (n k tw xb yb t : ℕ) : outs (msgTIR n k tw xb yb) t = 0 := by
  simp only [msgTIR, outs, outs_zeroIR, outs_finIR]

theorem cost_msgTIR (n k tw xb yb t : ℕ) (hn : 2 * 2 ^ n < 2 ^ 64) (hk : k < 2 ^ 64) :
    cost (msgTIR n k tw xb yb) t = 46 + 36 * 2 ^ n + 48 * k := by
  simp only [msgTIR, cost, cost_zeroIR _ _ _ hn, cost_finIR _ _ _ _ _ hk]; ring

/-- `F`'s zero from two zero words. -/
theorem rdF_zero_of {M : Mem} {a : ℕ} (h0 : rd M a = 0) (h1 : rd M (a + 1) = 0) : rdF M a = 0 := by
  simp only [rdF, rdB, h0, h1]; rfl

/-- **A tape message's rows**: entry `j < 2^n` of `X` (`Y`) is the tape pair at `tw + 4j`
(`tw + 4j + 2`) for `j < k`, and `0` from `k` on; the heap outside the rows is kept. -/
theorem msgTIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n k tw xb yb : ℕ} (hn : n ≤ 20)
    (hk : k ≤ 2 ^ n) (htw : tw + 4 * k < 2 ^ 64) (hxb : regs ≤ xb) (hyb : regs ≤ yb)
    (hxb2 : xb + 2 * 2 ^ n < 2 ^ 64) (hyb2 : yb + 2 * 2 ^ n < 2 ^ 64)
    (hxs : xb + 2 * 2 ^ n ≤ s.M.size) (hys : yb + 2 * 2 ^ n ≤ s.M.size)
    (hd : xb + 2 * 2 ^ n ≤ yb ∨ yb + 2 * 2 ^ n ≤ xb) :
    (∀ j < 2 ^ n, rdF (semXIR I (msgTIR n k tw xb yb) s).M (xb + 2 * j) =
        (if j < k then tapeF I (tw + 4 * j) else 0) ∧
      rdF (semXIR I (msgTIR n k tw xb yb) s).M (yb + 2 * j) =
        (if j < k then tapeF I (tw + 4 * j + 2) else 0)) ∧
    (∀ i, regs ≤ i → (i < xb ∨ xb + 2 * 2 ^ n ≤ i) → (i < yb ∨ yb + 2 * 2 ^ n ≤ i) →
      rd (semXIR I (msgTIR n k tw xb yb) s).M i = rd s.M i) ∧
    Inv (semXIR I (msgTIR n k tw xb yb) s).M := by
  have hP : 2 ^ n ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hn
  have hs := hM.1
  simp only [regs] at hs hxb hyb
  rw [msgTIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := zeroIR_sem I s hM (n := 2 * 2 ^ n) (b := xb) (by omega)
    (by simp only [regs]; omega) hxb2 hxs
  have z1 := size_sem I (zeroIR (2 * 2 ^ n) xb) s
  generalize semXIR I (zeroIR (2 * 2 ^ n) xb) s = s1 at a1 a2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 * 2 ^ n) (b := yb) (by omega)
    (by simp only [regs]; omega) hyb2 (by omega)
  have z2 := size_sem I (zeroIR (2 * 2 ^ n) yb) s1
  generalize semXIR I (zeroIR (2 * 2 ^ n) yb) s1 = s2 at b1 b2 hM2 z2
  obtain ⟨c1, c2, hM3⟩ := finIR_sem I s2 hM2 (k := k) (tw := tw) (xb := xb) (yb := yb) (by omega)
    htw (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega) (by omega) (by omega)
    (by omega) (by omega)
  refine ⟨fun j hj => ?_, fun i hi hi2 hi3 => ?_, hM3⟩
  · by_cases hjk : j < k
    · rw [if_pos hjk, if_pos hjk]; exact c1 j hjk
    · rw [if_neg hjk, if_neg hjk]
      have hx : rdF s2.M (xb + 2 * j) = 0 := rdF_zero_of
        ((b2 _ (by simp only [regs]; omega) (by omega)).trans (a1 _ (by omega)))
        ((b2 _ (by simp only [regs]; omega) (by omega)).trans
          (by rw [show xb + 2 * j + 1 = xb + (2 * j + 1) by omega]; exact a1 _ (by omega)))
      have hy : rdF s2.M (yb + 2 * j) = 0 := rdF_zero_of (b1 _ (by omega))
        (by rw [show yb + 2 * j + 1 = yb + (2 * j + 1) by omega]; exact b1 _ (by omega))
      constructor
      · rw [← hx]
        exact rdF_eq (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
      · rw [← hy]
        exact rdF_eq (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
  · rw [c2 i hi (hi2.imp_right fun h => by omega) (hi3.imp_right fun h => by omega),
      b2 i hi hi3, a2 i hi hi2]

/-- The byte offset of the final message in π (A.3 field 13, revision 3.13). -/
def finOff : ℕ := 64640

/-- Its first tape word. -/
def finW : ℕ := 5 + finOff / 8

/-- **The final message's element `x` as π carries it**: the 32 bytes at `finOff + 32x`. -/
def finPi (π : Proof) (x : ℕ) : K := chK (bytesAt π (finOff + 32 * x) 32)

/-- **Value control of the offset** (A.3, revision 3.13): the final message follows level 4's
cap (`2^7` entries of 32 bytes) and ends where the columns start (68,736). -/
theorem finOff_ctl : finOff = capOffL 4 + 32 * 2 ^ capLogL 4 ∧ finOff + 32 * 128 = 68736 ∧
    finW = 8085 := by decide

/-- **The tape at the final message**: the two tape pairs of element `x < 128` are `finPi`. -/
theorem tapeF_fin (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) {x : ℕ}
    (hx : x < 128) :
    (⟨tapeF (tp c π L) (finW + 4 * x), tapeF (tp c π L) (finW + 4 * x + 2)⟩ : K) = finPi π x := by
  have hp : π.size = 797904 := hs.trans piSize_eq
  have T : ∀ m < 4, (tp c π L).getD (finW + 4 * x + m) 0 =
      (packBytes (bytesAt π (finOff + 32 * x) 32).toList).getD m 0 := fun m hm => by
    rw [tp, getD_toArray]
    exact tape_capL c π L (off := finOff) (by decide) (by rw [hp]; simp only [finOff]; omega) hm
  rw [finPi, chK_words, tapeF, tapeF, ← T 0 (by norm_num), ← T 1 (by norm_num),
    ← T 2 (by norm_num), ← T 3 (by norm_num)]
  rfl

/-! ## The message rows from the next level's decoded rows (levels 0–3) -/

/-- `mS := ob + 4k (x mod 8) + 2 (x div 8)` (`x` in `mJ`): row `2 (x mod 8)` of `2k` cells,
column `x div 8`. -/
def gAd (k ob : ℕ) : List Prim :=
  [.const mK 7, .op .and mT mJ mK, .const mK (toWord (4 * k)), .op .mul mT mT mK, .const mK 3,
   .op .shr mU mJ mK, .op .add mU mU mU, .op .add mT mT mU, .const mK (toWord ob),
   .op .add mS mT mK]

/-- `mS += 2k`: the next row. -/
def gNx (k : ℕ) : List Prim := [.const mK (toWord (2 * k)), .op .add mS mS mK]

/-- The pointers: `mX += 2`, `mY += 2`. -/
def stepXY : List Prim := [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]

/-- One K element: `X[x] :=` row `2 (x mod 8)`, `Y[x] :=` row `2 (x mod 8) + 1`, column `x div 8`. -/
def gBody (k ob : ℕ) : XIR :=
  .seq (.blk (gAd k ob)) (.seq (ldF mV mS mS1) (.seq (stF mX mX1 mV) (.seq (.blk (gNx k))
    (.seq (ldF mV mS mS1) (.seq (stF mY mX1 mV) (.seq (.blk stepXY)
      (.blk [.op .add mJ mJ cOne])))))))

/-- The start: `x := 0`, the pointers, the count `8k`. -/
def gPre (k xb yb : ℕ) : List Prim :=
  [.const mJ 0, .const mX (toWord xb), .const mY (toWord yb), .const mN (toWord (8 * k))]

/-- **The next message's rows from the decoded rows** (row `c` at `ob + 2kc`, `k` entries):
`8k` K elements. -/
def gathIR (k ob xb yb : ℕ) : XIR :=
  .seq (.blk (gPre k xb yb)) (.loopK mC mN (toWord (8 * k)) (gBody k ob))

theorem wf_gathIR (k ob xb yb : ℕ) : WF (gathIR k ob xb yb) := by
  simp +decide only [gathIR, gPre, gBody, gAd, gNx, stepXY, ldF, stF, WF, Writes, Prim.dst, mJ, mX,
    mY, mN, mK, mT, mU, mS, mS1, mV, mX1, mC, cTmp, regs, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, exists_eq_or_imp, forall_eq, exists_eq_left, or_false, and_true]

theorem noLoopT_gathIR (k ob xb yb : ℕ) : NoLoopT (gathIR k ob xb yb) := by
  simp [gathIR, gBody, ldF, stF, NoLoopT]

theorem outs_gathIR (k ob xb yb t : ℕ) : outs (gathIR k ob xb yb) t = 0 := by
  simp [gathIR, gBody, ldF, stF, outs]

theorem cost_gathIR (k ob xb yb t : ℕ) (hk : 8 * k < 2 ^ 64) :
    cost (gathIR k ob xb yb) t = 16 + 8 * k * 70 := by
  have a : (toWord (8 * k)).toNat = 8 * k := toNat_toWord hk
  simp only [gathIR, gPre, gBody, gAd, gNx, stepXY, ldF, stF, cost, blkSteps, List.length_cons,
    List.length_nil, a]
  norm_num; ring

theorem and7_toWord {a : ℕ} (ha : a < 2 ^ 64) : XOp.and.eval (toWord a) 7 = toWord (a % 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_and, toNat_toWord ha, show (7 : Word).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, toNat_toWord (by omega)]

theorem gAd_sem (I : Array Word) (s : St) (hM : Inv s.M) {k ob x : ℕ} (hx : x < 2 ^ 64)
    (hJ : rd s.M mJ = toWord x) :
    rd (semXIR I (.blk (gAd k ob)) s).M mS = toWord (ob + 4 * k * (x % 8) + 2 * (x / 8)) ∧
    (∀ i, i ≠ mK → i ≠ mT → i ≠ mU → i ≠ mS → rd (semXIR I (.blk (gAd k ob)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (gAd k ob)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk (gAd k ob)) s = ⟨runPrims (gAd k ob) s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, fun i h1 h2 h3 h4 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [gAd, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4) _,
    inv_runPrims (by simp [gAd, Prim.dst, mK, mT, mU, mS]) hM⟩
  simp only [gAd, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, mK, mT, mU, mS]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [hJ, and7_toWord hx, mul_toWord, show (3 : Word) = toWord 3 from rfl, shr_toWord hx (by norm_num),
    add_toWord, add_toWord, add_toWord]
  exact congrArg toWord (by rw [show (2 : ℕ) ^ 3 = 8 from rfl]; ring)

theorem gNx_sem (I : Array Word) (s : St) (hM : Inv s.M) {k a : ℕ} (hS : rd s.M mS = toWord a) :
    rd (semXIR I (.blk (gNx k)) s).M mS = toWord (a + 2 * k) ∧
    (∀ i, i ≠ mK → i ≠ mS → rd (semXIR I (.blk (gNx k)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (gNx k)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk (gNx k)) s = ⟨runPrims (gNx k) s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, fun i h1 h2 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [gNx, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2) _,
    inv_runPrims (by simp [gNx, Prim.dst, mK, mS]) hM⟩
  simp only [gNx, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, mK, mS]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [hS, add_toWord]

/-- **The gathered rows**: for `x < 8k`, `X[x]` is the `F` element of row `2 (x mod 8)` (rows of
`2k` cells from `ob`) at column `x div 8`, `Y[x]` that of row `2 (x mod 8) + 1`; the heap outside
the two rows is kept. -/
theorem gathIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k ob xb yb : ℕ}
    (hk : 8 * k < 2 ^ 64) (hob : regs ≤ ob) (hob2 : ob + 32 * k < 2 ^ 64)
    (hxb : regs ≤ xb) (hxb2 : xb + 16 * k < 2 ^ 64) (hyb : regs ≤ yb) (hyb2 : yb + 16 * k < 2 ^ 64)
    (hxs : xb + 16 * k ≤ s.M.size) (hys : yb + 16 * k ≤ s.M.size)
    (hd : xb + 16 * k ≤ yb ∨ yb + 16 * k ≤ xb) (hdx : ob + 32 * k ≤ xb ∨ xb + 16 * k ≤ ob)
    (hdy : ob + 32 * k ≤ yb ∨ yb + 16 * k ≤ ob) :
    (∀ x < 8 * k, rdF (semXIR I (gathIR k ob xb yb) s).M (xb + 2 * x) =
        rdF s.M (ob + 4 * k * (x % 8) + 2 * (x / 8)) ∧
      rdF (semXIR I (gathIR k ob xb yb) s).M (yb + 2 * x) =
        rdF s.M (ob + 4 * k * (x % 8) + 2 * (x / 8) + 2 * k)) ∧
    (∀ i, regs ≤ i → (i < xb ∨ xb + 16 * k ≤ i) → (i < yb ∨ yb + 16 * k ≤ i) →
      rd (semXIR I (gathIR k ob xb yb) s).M i = rd s.M i) ∧
    Inv (semXIR I (gathIR k ob xb yb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hxb hyb hob
  have hw0 : WF (.blk (gPre k xb yb)) := by simp +decide only [gPre, WF, Prim.dst, mJ, mX, mY, mN,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have e0 : semXIR I (.blk (gPre k xb yb)) s = ⟨runPrims (gPre k xb yb) s.M, s.o⟩ := rfl
  have r0 : rd (runPrims (gPre k xb yb) s.M) mJ = toWord 0 ∧
      rd (runPrims (gPre k xb yb) s.M) mX = toWord xb ∧
      rd (runPrims (gPre k xb yb) s.M) mY = toWord yb ∧
      rd (runPrims (gPre k xb yb) s.M) mN = toWord (8 * k) := by
    simp only [gPre, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp (disch := first | decide | (simp only [size_set, mJ, mX, mY, mN]; omega)) only
        [rd_set_self, rd_set_ne] <;> rfl
  have r4 : ∀ i, regs ≤ i → rd (runPrims (gPre k xb yb) s.M) i = rd s.M i := fun i hi =>
    rd_runPrims_of_not_writes (by
      simp only [gPre, List.mem_cons, List.mem_nil_iff, or_false]
      simp only [regs] at hi
      rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, mJ, mX, mY, mN] <;> omega) _
  have hM0 : Inv (runPrims (gPre k xb yb) s.M) := by
    have h := inv_sem I hw0 hM; rwa [e0] at h
  have z0 : (runPrims (gPre k xb yb) s.M).size = s.M.size := size_runPrims _ _
  rw [gathIR, semXIR_seq, e0]
  generalize runPrims (gPre k xb yb) s.M = M0 at r0 r4 hM0 z0
  obtain ⟨r1, r2, r3, rN⟩ := r0
  let P : ℕ → St → Prop := fun x s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M mJ = toWord x ∧ rd s'.M mX = toWord (xb + 2 * x) ∧ rd s'.M mY = toWord (yb + 2 * x) ∧
    (∀ v < x, rdF s'.M (xb + 2 * v) = rdF s.M (ob + 4 * k * (v % 8) + 2 * (v / 8)) ∧
      rdF s'.M (yb + 2 * v) = rdF s.M (ob + 4 * k * (v % 8) + 2 * (v / 8) + 2 * k)) ∧
    ∀ i, regs ≤ i → (i < xb ∨ xb + 2 * x ≤ i) → (i < yb ∨ yb + 2 * x ≤ i) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ mC → i ≠ cTmp → rd (entryK mC mN (toWord (8 * k)) M0) i = rd M0 i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have p0 : P 0 ⟨entryK mC mN (toWord (8 * k)) M0, s.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_, ?_,
      fun v hv => absurd hv (Nat.not_lt_zero _), fun i hi _ _ => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), r1]
    · dsimp only; rw [hE _ (by decide) (by decide), r2, Nat.mul_zero, Nat.add_zero]
    · dsimp only; rw [hE _ (by decide) (by decide), r3, Nat.mul_zero, Nat.add_zero]
    · dsimp only
      rw [hE _ (by simp only [mC, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        r4 i hi]
  have step : ∀ x s', x < 8 * k → P x s' → P (x + 1) (decS mC (semXIR I (gBody k ob) s')) := by
    rintro x s' hx ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hm8 : 4 * k * (x % 8) ≤ 4 * k * 7 := Nat.mul_le_mul_left _ (by omega)
    have hd8 : x / 8 < k := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega)
    -- the source address
    rw [gBody, semXIR_seq]
    obtain ⟨a1, a2, hM1⟩ := gAd_sem I s' i1 (k := k) (ob := ob) (by omega) i3
    have z1 := size_sem I (.blk (gAd k ob)) s'
    generalize semXIR I (.blk (gAd k ob)) s' = s1 at a1 a2 hM1 z1
    generalize ha : ob + 4 * k * (x % 8) + 2 * (x / 8) = a at a1
    have ha2 : a + 2 * k + 2 ≤ ob + 32 * k := by omega
    have h1 : ∀ i, regs ≤ i → rd s1.M i = rd s'.M i := fun i hi => by
      simp only [regs] at hi
      exact a2 i (by simp only [mK]; omega) (by simp only [mT]; omega) (by simp only [mU]; omega)
        (by simp only [mS]; omega)
    -- `X[x]`
    rw [semXIR_seq]
    obtain ⟨b1, b2, b3⟩ := ldF_sem I s1 hM1 (d := mV) (p := mS) (p1 := mS1) (x := a) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) a1 (by simp only [regs]; omega)
      (by omega)
    have hM2 := inv_sem I (P := ldF mV mS mS1) (s := s1) (by simp +decide only [ldF, WF, Prim.dst,
      mV, mS1, and_true]) hM1
    have z2 := size_sem I (ldF mV mS mS1) s1
    generalize semXIR I (ldF mV mS mS1) s1 = s2 at b1 b2 b3 hM2 z2
    rw [semXIR_seq]
    have hX2 : rd s2.M mX = toWord (xb + 2 * x) := by
      rw [b3 _ (by decide) (by decide) (by decide), a2 _ (by decide) (by decide) (by decide)
        (by decide), i4]
    obtain ⟨c1, c2, hM3⟩ := stF_sem I s2 hM2 (p := mX) (p1 := mX1) (v := mV) (x := xb + 2 * x)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hX2 (by simp only [regs]; omega) (by omega) (by omega)
    have z3 := size_sem I (stF mX mX1 mV) s2
    generalize semXIR I (stF mX mX1 mV) s2 = s3 at c1 c2 hM3 z3
    -- the next row
    rw [semXIR_seq]
    have hS3 : rd s3.M mS = toWord a := by
      rw [c2 _ (by simp only [mS]; omega) (by simp only [mS]; omega) (by decide) (by decide),
        b3 _ (by decide) (by decide) (by decide), a1]
    obtain ⟨d1, d2, hM4⟩ := gNx_sem I s3 hM3 (k := k) hS3
    have z4 := size_sem I (.blk (gNx k)) s3
    generalize semXIR I (.blk (gNx k)) s3 = s4 at d1 d2 hM4 z4
    -- `Y[x]`
    rw [semXIR_seq]
    obtain ⟨f1, f2, f3⟩ := ldF_sem I s4 hM4 (d := mV) (p := mS) (p1 := mS1) (x := a + 2 * k)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d1
      (by simp only [regs]; omega) (by omega)
    have hM5 := inv_sem I (P := ldF mV mS mS1) (s := s4) (by simp +decide only [ldF, WF, Prim.dst,
      mV, mS1, and_true]) hM4
    have z5 := size_sem I (ldF mV mS mS1) s4
    generalize semXIR I (ldF mV mS mS1) s4 = s5 at f1 f2 f3 hM5 z5
    rw [semXIR_seq]
    have hY5 : rd s5.M mY = toWord (yb + 2 * x) := by
      rw [f3 _ (by decide) (by decide) (by decide), d2 _ (by decide) (by decide),
        c2 _ (by simp only [mY]; omega) (by simp only [mY]; omega) (by decide) (by decide),
        b3 _ (by decide) (by decide) (by decide), a2 _ (by decide) (by decide) (by decide)
        (by decide), i5]
    obtain ⟨g1, g2, hM6⟩ := stF_sem I s5 hM5 (p := mY) (p1 := mX1) (v := mV) (x := yb + 2 * x)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hY5 (by simp only [regs]; omega) (by omega) (by omega)
    have z6 := size_sem I (stF mY mX1 mV) s5
    generalize semXIR I (stF mY mX1 mV) s5 = s6 at g1 g2 hM6 z6
    -- the pointers
    rw [semXIR_seq]
    have hX6 : rd s6.M mX = toWord (xb + 2 * x) := by
      rw [g2 _ (by simp only [mX]; omega) (by simp only [mX]; omega) (by decide) (by decide),
        f3 _ (by decide) (by decide) (by decide), d2 _ (by decide) (by decide),
        c2 _ (by simp only [mX]; omega) (by simp only [mX]; omega) (by decide) (by decide), hX2]
    have hY6 : rd s6.M mY = toWord (yb + 2 * x) := by
      rw [g2 _ (by simp only [mY]; omega) (by simp only [mY]; omega) (by decide) (by decide), hY5]
    obtain ⟨k1, k2, k3, hM7⟩ := stepXY_sem I s6 hM6 hX6 hY6
    have z7 := size_sem I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s6
    have estep : (.blk stepXY : XIR) = .blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK] :=
      rfl
    rw [estep]
    generalize semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s6 = s7
      at k1 k2 k3 hM7 z7
    have hJ7 : rd s7.M mJ = toWord x := by
      rw [k3 _ (by decide) (by decide) (by decide),
        g2 _ (by simp only [mJ]; omega) (by simp only [mJ]; omega) (by decide) (by decide),
        f3 _ (by decide) (by decide) (by decide), d2 _ (by decide) (by decide),
        c2 _ (by simp only [mJ]; omega) (by simp only [mJ]; omega) (by decide) (by decide),
        b3 _ (by decide) (by decide) (by decide), a2 _ (by decide) (by decide) (by decide)
        (by decide), i3]
    have e8 : semXIR I (.blk [.op .add mJ mJ cOne]) s7 = ⟨runPrims [.op .add mJ mJ cOne] s7.M, s7.o⟩ :=
      rfl
    rw [e8]
    obtain ⟨n1, n2⟩ := incr_sem s7.M hM7 (r := mJ) (by decide) (by decide) hJ7
    have hd : ∀ i, i ≠ mC → rd (decS mC ⟨runPrims [.op .add mJ mJ cOne] s7.M, s7.o⟩).M i =
        rd (runPrims [.op .add mJ mJ cOne] s7.M) i := fun i h => rd_decS (Ne.symm h) _
    -- the heap
    have h8 : ∀ i, regs ≤ i → i ≠ xb + 2 * x → i ≠ xb + 2 * x + 1 → i ≠ yb + 2 * x →
        i ≠ yb + 2 * x + 1 → rd (runPrims [.op .add mJ mJ cOne] s7.M) i = rd s'.M i :=
      fun i hi j1 j2 j3 j4 => by
        simp only [regs] at hi
        rw [n2 _ (by simp only [mJ]; omega),
          k3 i (by simp only [mK]; omega) (by simp only [mX]; omega) (by simp only [mY]; omega),
          g2 i j3 j4 (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
          f3 i (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mS1]; omega),
          d2 i (by simp only [mK]; omega) (by simp only [mS]; omega),
          c2 i j1 j2 (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
          b3 i (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mS1]; omega),
          h1 i (by simp only [regs]; omega)]
    have hcell : ∀ i, regs ≤ i → (i < xb ∨ xb + 16 * k ≤ i) → (i < yb ∨ yb + 16 * k ≤ i) →
        rd s'.M i = rd s.M i := fun i hi j1 j2 =>
      i7 i hi (j1.imp_right fun h => by omega) (j2.imp_right fun h => by omega)
    have hX8 : rdF (runPrims [.op .add mJ mJ cOne] s7.M) (xb + 2 * x) =
        rdF s.M (ob + 4 * k * (x % 8) + 2 * (x / 8)) := by
      have e1 : rdF (runPrims [.op .add mJ mJ cOne] s7.M) (xb + 2 * x) = rdF s3.M (xb + 2 * x) := by
        refine rdF_eq ?_ ?_
        · rw [n2 _ (by simp only [mJ]; omega), k3 _ (by simp only [mK]; omega)
            (by simp only [mX]; omega) (by simp only [mY]; omega),
            g2 _ (by omega) (by omega) (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
            f3 _ (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mS1]; omega),
            d2 _ (by simp only [mK]; omega) (by simp only [mS]; omega)]
        · rw [n2 _ (by simp only [mJ]; omega), k3 _ (by simp only [mK]; omega)
            (by simp only [mX]; omega) (by simp only [mY]; omega),
            g2 _ (by omega) (by omega) (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
            f3 _ (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mS1]; omega),
            d2 _ (by simp only [mK]; omega) (by simp only [mS]; omega)]
      rw [e1, c1, b1, ← ha]
      exact rdF_eq ((h1 _ (by simp only [regs]; omega)).trans
          (hcell _ (by simp only [regs]; omega) (by omega) (by omega)))
        ((h1 _ (by simp only [regs]; omega)).trans
          (hcell _ (by simp only [regs]; omega) (by omega) (by omega)))
    have hY8 : rdF (runPrims [.op .add mJ mJ cOne] s7.M) (yb + 2 * x) =
        rdF s.M (ob + 4 * k * (x % 8) + 2 * (x / 8) + 2 * k) := by
      have e1 : rdF (runPrims [.op .add mJ mJ cOne] s7.M) (yb + 2 * x) = rdF s6.M (yb + 2 * x) := by
        refine rdF_eq ?_ ?_
        · rw [n2 _ (by simp only [mJ]; omega), k3 _ (by simp only [mK]; omega)
            (by simp only [mX]; omega) (by simp only [mY]; omega)]
        · rw [n2 _ (by simp only [mJ]; omega), k3 _ (by simp only [mK]; omega)
            (by simp only [mX]; omega) (by simp only [mY]; omega)]
      have e2 : ∀ i, regs ≤ i → i ≠ xb + 2 * x → i ≠ xb + 2 * x + 1 → rd s4.M i = rd s'.M i :=
        fun i hi j1 j2 => by
          simp only [regs] at hi
          rw [d2 i (by simp only [mK]; omega) (by simp only [mS]; omega),
            c2 i j1 j2 (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
            b3 i (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mS1]; omega),
            h1 i (by simp only [regs]; omega)]
      rw [e1, g1, f1, ← ha]
      exact rdF_eq ((e2 _ (by simp only [regs]; omega) (by omega) (by omega)).trans
          (hcell _ (by simp only [regs]; omega) (by omega) (by omega)))
        ((e2 _ (by simp only [regs]; omega) (by omega) (by omega)).trans
          (hcell _ (by simp only [regs]; omega) (by omega) (by omega)))
    refine ⟨inv_decS (inv_runPrims (by simp [Prim.dst, mJ]) hM7) (by decide),
      by rw [size_decS, size_runPrims, z7, z6, z5, z4, z3, z2, z1, i2], ?_, ?_, ?_,
      fun v hv => ?_, fun i hi hi2 hi3 => ?_⟩
    · rw [hd _ (by decide), n1]
    · rw [hd _ (by decide), n2 _ (by decide), k1]; exact congrArg toWord (by ring)
    · rw [hd _ (by decide), n2 _ (by decide), k2]; exact congrArg toWord (by ring)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | rfl
      · have g := i6 v h
        constructor
        · rw [← g.1]
          exact rdF_eq ((hd _ (by simp only [mC]; omega)).trans
            (h8 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
            ((hd _ (by simp only [mC]; omega)).trans
            (h8 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
        · rw [← g.2]
          exact rdF_eq ((hd _ (by simp only [mC]; omega)).trans
            (h8 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
            ((hd _ (by simp only [mC]; omega)).trans
            (h8 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
      · exact ⟨(rdF_eq (hd _ (by simp only [mC]; omega)) (hd _ (by simp only [mC]; omega))).trans hX8,
          (rdF_eq (hd _ (by simp only [mC]; omega)) (hd _ (by simp only [mC]; omega))).trans hY8⟩
    · simp only [regs] at hi
      rw [hd _ (by simp only [mC]; omega), h8 i (by simp only [regs]; omega) (by omega) (by omega)
        (by omega) (by omega), i7 i (by simp only [regs]; omega) (hi2.imp_right fun h => by omega)
        (hi3.imp_right fun h => by omega)]
  have := loopK_run I (gBody k ob) P ⟨M0, s.o⟩ hM0 (by decide) (by decide) (by decide) rN hk p0 step
  exact ⟨this.2.2.2.2.2.1, fun i hi h2 h3 => this.2.2.2.2.2.2 i hi
    (h2.imp_right fun h => by omega) (h3.imp_right fun h => by omega), this.1⟩

/-- **The rows of the next level's message** (levels 0–3): both rows of `2^n` entries zeroed,
then the `8k` K elements gathered from the decoded rows at `ob`. -/
def msgHIR (n k ob xb yb : ℕ) : XIR :=
  .seq (zeroIR (2 * 2 ^ n) xb) (.seq (zeroIR (2 * 2 ^ n) yb) (gathIR k ob xb yb))

theorem wf_msgHIR (n k ob xb yb : ℕ) : WF (msgHIR n k ob xb yb) :=
  ⟨wf_zeroIR _ _, wf_zeroIR _ _, wf_gathIR _ _ _ _⟩

theorem noLoopT_msgHIR (n k ob xb yb : ℕ) : NoLoopT (msgHIR n k ob xb yb) :=
  ⟨noLoopT_zeroIR _ _, noLoopT_zeroIR _ _, noLoopT_gathIR _ _ _ _⟩

theorem outs_msgHIR (n k ob xb yb t : ℕ) : outs (msgHIR n k ob xb yb) t = 0 := by
  simp only [msgHIR, outs, outs_zeroIR, outs_gathIR]

theorem cost_msgHIR (n k ob xb yb t : ℕ) (hn : 2 * 2 ^ n < 2 ^ 64) (hk : 8 * k < 2 ^ 64) :
    cost (msgHIR n k ob xb yb) t = 46 + 36 * 2 ^ n + 560 * k := by
  simp only [msgHIR, cost, cost_zeroIR _ _ _ hn, cost_gathIR _ _ _ _ _ hk]; ring

theorem msgHIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n k ob xb yb : ℕ} (hn : n ≤ 20)
    (hk : 8 * k ≤ 2 ^ n) (hob : regs ≤ ob) (hob2 : ob + 32 * k < 2 ^ 64)
    (hxb : regs ≤ xb) (hyb : regs ≤ yb)
    (hxb2 : xb + 2 * 2 ^ n < 2 ^ 64) (hyb2 : yb + 2 * 2 ^ n < 2 ^ 64)
    (hxs : xb + 2 * 2 ^ n ≤ s.M.size) (hys : yb + 2 * 2 ^ n ≤ s.M.size)
    (hd : xb + 2 * 2 ^ n ≤ yb ∨ yb + 2 * 2 ^ n ≤ xb) (hdx : ob + 32 * k ≤ xb ∨ xb + 2 * 2 ^ n ≤ ob)
    (hdy : ob + 32 * k ≤ yb ∨ yb + 2 * 2 ^ n ≤ ob) :
    (∀ j < 2 ^ n, rdF (semXIR I (msgHIR n k ob xb yb) s).M (xb + 2 * j) =
        (if j < 8 * k then rdF s.M (ob + 4 * k * (j % 8) + 2 * (j / 8)) else 0) ∧
      rdF (semXIR I (msgHIR n k ob xb yb) s).M (yb + 2 * j) =
        (if j < 8 * k then rdF s.M (ob + 4 * k * (j % 8) + 2 * (j / 8) + 2 * k) else 0)) ∧
    (∀ i, regs ≤ i → (i < xb ∨ xb + 2 * 2 ^ n ≤ i) → (i < yb ∨ yb + 2 * 2 ^ n ≤ i) →
      rd (semXIR I (msgHIR n k ob xb yb) s).M i = rd s.M i) ∧
    Inv (semXIR I (msgHIR n k ob xb yb) s).M := by
  have hP : 2 ^ n ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hn
  have hs := hM.1
  simp only [regs] at hs hxb hyb hob
  rw [msgHIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := zeroIR_sem I s hM (n := 2 * 2 ^ n) (b := xb) (by omega)
    (by simp only [regs]; omega) hxb2 hxs
  have z1 := size_sem I (zeroIR (2 * 2 ^ n) xb) s
  generalize semXIR I (zeroIR (2 * 2 ^ n) xb) s = s1 at a1 a2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 * 2 ^ n) (b := yb) (by omega)
    (by simp only [regs]; omega) hyb2 (by omega)
  have z2 := size_sem I (zeroIR (2 * 2 ^ n) yb) s1
  generalize semXIR I (zeroIR (2 * 2 ^ n) yb) s1 = s2 at b1 b2 hM2 z2
  have h2 : ∀ i, regs ≤ i → (i < xb ∨ xb + 2 * 2 ^ n ≤ i) → (i < yb ∨ yb + 2 * 2 ^ n ≤ i) →
      rd s2.M i = rd s.M i := fun i hi h1 h2 => by rw [b2 i hi h2, a2 i hi h1]
  obtain ⟨c1, c2, hM3⟩ := gathIR_sem I s2 hM2 (k := k) (ob := ob) (xb := xb) (yb := yb) (by omega)
    (by simp only [regs]; omega) hob2 (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hsrc : ∀ j < 8 * k, ob + 4 * k * (j % 8) + 2 * (j / 8) + 2 * k + 2 ≤ ob + 32 * k := by
    intro j hj
    have hm8 : 4 * k * (j % 8) ≤ 4 * k * 7 := Nat.mul_le_mul_left _ (by omega)
    have hd8 : j / 8 < k := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega)
    omega
  refine ⟨fun j hj => ?_, fun i hi hi2 hi3 => ?_, hM3⟩
  · by_cases hjk : j < 8 * k
    · rw [if_pos hjk, if_pos hjk, (c1 j hjk).1, (c1 j hjk).2]
      have := hsrc j hjk
      constructor
      · exact rdF_eq (h2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (h2 _ (by simp only [regs]; omega) (by omega) (by omega))
      · exact rdF_eq (h2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (h2 _ (by simp only [regs]; omega) (by omega) (by omega))
    · rw [if_neg hjk, if_neg hjk]
      have hx : rdF s2.M (xb + 2 * j) = 0 := rdF_zero_of
        ((b2 _ (by simp only [regs]; omega) (by omega)).trans (a1 _ (by omega)))
        ((b2 _ (by simp only [regs]; omega) (by omega)).trans
          (by rw [show xb + 2 * j + 1 = xb + (2 * j + 1) by omega]; exact a1 _ (by omega)))
      have hy : rdF s2.M (yb + 2 * j) = 0 := rdF_zero_of (b1 _ (by omega))
        (by rw [show yb + 2 * j + 1 = yb + (2 * j + 1) by omega]; exact b1 _ (by omega))
      constructor
      · rw [← hx]
        exact rdF_eq (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
      · rw [← hy]
        exact rdF_eq (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
  · rw [c2 i hi (hi2.imp_right fun h => by omega) (hi3.imp_right fun h => by omega), h2 i hi hi2 hi3]

/-! ## The rows are the next message's coordinates -/

open FR.Snd

theorem nextMsg_four (L es : Log) (x : ℕ) : nextMsg .N30 L es 4 x = finalAt es x := by
  rw [nextMsg, if_neg (by decide)]

/-- **Level 4's rows** (`msgTIR 10 32 finW`): with the chain link `finalAt es x = finPi π x`
(C.4's absorb is π's final field), entry `j < 2^10` of `X` (`Y`) is `(nextMsg 4 j).f₀` (`.f₁`)
for `j < 2^mLog = 32`, and `0` above: the input of `fwdIR_enc`. -/
theorem msg4_next (c : Digest) (π : Proof) (L es : Log) (hs : π.size = piSize)
    (hfin : ∀ x < 32, finalAt es x = finPi π x) (s : St) (hM : Inv s.M) {xb yb : ℕ}
    (hxb : regs ≤ xb) (hyb : regs ≤ yb) (hxb2 : xb + 2 * 2 ^ 10 < 2 ^ 64)
    (hyb2 : yb + 2 * 2 ^ 10 < 2 ^ 64) (hxs : xb + 2 * 2 ^ 10 ≤ s.M.size)
    (hys : yb + 2 * 2 ^ 10 ≤ s.M.size) (hd : xb + 2 * 2 ^ 10 ≤ yb ∨ yb + 2 * 2 ^ 10 ≤ xb) :
    ∀ j < 2 ^ 10,
      rdF (semXIR (tp c π L) (msgTIR 10 32 finW xb yb) s).M (xb + 2 * j) =
        (if j < 2 ^ mLog .N30 4 then (nextMsg .N30 L es 4 j).f₀ else 0) ∧
      rdF (semXIR (tp c π L) (msgTIR 10 32 finW xb yb) s).M (yb + 2 * j) =
        (if j < 2 ^ mLog .N30 4 then (nextMsg .N30 L es 4 j).f₁ else 0) := by
  intro j hj
  have hm : 2 ^ mLog .N30 4 = 32 := by decide
  obtain ⟨h1, h2⟩ := (msgTIR_sem (tp c π L) s hM (n := 10) (k := 32) (tw := finW) (xb := xb)
    (yb := yb) (by norm_num) (by norm_num) (by simp only [finW, finOff]; norm_num) hxb hyb hxb2 hyb2
    hxs hys hd).1 j hj
  rw [h1, h2, hm]
  by_cases hj32 : j < 32
  · rw [if_pos hj32, if_pos hj32, if_pos hj32, if_pos hj32, nextMsg_four, hfin j hj32,
      ← tapeF_fin c π L hs (x := j) (by omega)]
    exact ⟨rfl, rfl⟩
  · rw [if_neg hj32, if_neg hj32, if_neg hj32, if_neg hj32]
    exact ⟨rfl, rfl⟩

/-- **The rows of levels 0–3** (`msgHIR`): if level `i + 1`'s decoded row `r` sits at
`ob + 2kr` (`k = 2^mLog (i + 1)`) as the `F` values of `msgOf (i + 1) r`, entry `j < 2^n` of `X`
(`Y`) is `(nextMsg i j).f₀` (`.f₁`) for `j < 8k = 2^mLog i`, and `0` above. -/
theorem msgH_next {L es : Log} {i : ℕ} (hi : i < 4) (I : Array Word) (s : St) (hM : Inv s.M)
    {ob xb yb : ℕ}
    (hdec : ∀ r < 16, ∀ x < 2 ^ mLog .N30 (i + 1),
      algebraMap F K (rdF s.M (ob + 2 * 2 ^ mLog .N30 (i + 1) * r + 2 * x)) =
        msgOf .N30 L es (i + 1) r x)
    (hF : ∀ r x, msgOf .N30 L es (i + 1) r x = algebraMap F K (msgOf .N30 L es (i + 1) r x).f₀)
    (hob : regs ≤ ob) (hob2 : ob + 32 * 2 ^ mLog .N30 (i + 1) < 2 ^ 64)
    (hxb : regs ≤ xb) (hyb : regs ≤ yb)
    (hxb2 : xb + 2 * 2 ^ (lvl .N30 i).logN < 2 ^ 64) (hyb2 : yb + 2 * 2 ^ (lvl .N30 i).logN < 2 ^ 64)
    (hxs : xb + 2 * 2 ^ (lvl .N30 i).logN ≤ s.M.size) (hys : yb + 2 * 2 ^ (lvl .N30 i).logN ≤ s.M.size)
    (hd : xb + 2 * 2 ^ (lvl .N30 i).logN ≤ yb ∨ yb + 2 * 2 ^ (lvl .N30 i).logN ≤ xb)
    (hdx : ob + 32 * 2 ^ mLog .N30 (i + 1) ≤ xb ∨ xb + 2 * 2 ^ (lvl .N30 i).logN ≤ ob)
    (hdy : ob + 32 * 2 ^ mLog .N30 (i + 1) ≤ yb ∨ yb + 2 * 2 ^ (lvl .N30 i).logN ≤ ob) :
    ∀ j < 2 ^ (lvl .N30 i).logN,
      rdF (semXIR I (msgHIR (lvl .N30 i).logN (2 ^ mLog .N30 (i + 1)) ob xb yb) s).M (xb + 2 * j) =
        (if j < 2 ^ mLog .N30 i then (nextMsg .N30 L es i j).f₀ else 0) ∧
      rdF (semXIR I (msgHIR (lvl .N30 i).logN (2 ^ mLog .N30 (i + 1)) ob xb yb) s).M (yb + 2 * j) =
        (if j < 2 ^ mLog .N30 i then (nextMsg .N30 L es i j).f₁ else 0) := by
  intro j hj
  have hm : 2 ^ mLog .N30 i = 8 * 2 ^ mLog .N30 (i + 1) := by interval_cases i <;> decide
  have hn : (lvl .N30 i).logN ≤ 20 := by interval_cases i <;> decide
  have hk : 8 * 2 ^ mLog .N30 (i + 1) ≤ 2 ^ (lvl .N30 i).logN := by interval_cases i <;> decide
  obtain ⟨h1, h2⟩ := (msgHIR_sem I s hM (k := 2 ^ mLog .N30 (i + 1)) hn hk hob hob2 hxb hyb hxb2
    hyb2 hxs hys hd hdx hdy).1 j hj
  rw [h1, h2, hm]
  by_cases hjk : j < 8 * 2 ^ mLog .N30 (i + 1)
  · rw [if_pos hjk, if_pos hjk, if_pos hjk, if_pos hjk,
      nextMsg_coords (by simp only [nLevels]; omega) hF]
    have hd8 : j / 8 < 2 ^ mLog .N30 (i + 1) := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega)
    have r0 := hdec (2 * (j % 8)) (by omega) (j / 8) hd8
    have r1 := hdec (2 * (j % 8) + 1) (by omega) (j / 8) hd8
    constructor
    · show _ = (msgOf .N30 L es (i + 1) (2 * (j % 8)) (j / 8)).f₀
      rw [← r0]
      show _ = rdF s.M (ob + 2 * 2 ^ mLog .N30 (i + 1) * (2 * (j % 8)) + 2 * (j / 8))
      congr 1; ring
    · show _ = (msgOf .N30 L es (i + 1) (2 * (j % 8) + 1) (j / 8)).f₀
      rw [← r1]
      show _ = rdF s.M (ob + 2 * 2 ^ mLog .N30 (i + 1) * (2 * (j % 8) + 1) + 2 * (j / 8))
      congr 1; ring
  · rw [if_neg hjk, if_neg hjk, if_neg hjk, if_neg hjk]
    exact ⟨rfl, rfl⟩

end FR.X
