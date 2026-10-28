-- New for `flock-recursive` (BLUEPRINT §6.2 step 4: `Enc(g⁽ⁱ⁺¹⁾)`; stage S-H2, track L-ext).
import FRXBfly
import FRXEncB

/-!
# The forward butterflies on the machine (`Enc` of a message)

The program `fwdIR ℓ tb` runs the levels `ℓ − 1, …, 0` of `FRXEncB.fwdRun` in place on a row of
`2^ℓ` `F` elements at `rA0`. It reuses the inverse butterflies' pair addresses (`pairPs`), `α`
(`alphaIR`) and the basis table (`wtabIR`). Two things differ:
- the arithmetic `farithIR`: `lo := u + α w`, `hi := u + α w + w`;
- the level order: `rLv := rKf − 1` with `rKf = ℓ − j` counting down, and `rTr := tb + 40·rLv`.

* `fpairBody_sem`, `flevelIR_sem`: one forward butterfly, one level (`fwdLevel`).
* **`fwdIR_sem`**: the row ends holding `fwdRun ℓ Y`; the heap outside it is kept.
* **`fwdIR_enc`**: on a message zero-padded to `2^ℓ`, the row ends holding `encF m c`
  (`fwdRun_enc`).

Registers `140 … 177` (shared with `bflyIR`), `rKf = 185`, `rTbf = 186`.
-/

namespace FR.X

open RecursionFast Finset

/-- The levels left, `ℓ − j`. -/ def rKf : ℕ := 185
/-- The table's first cell. -/ def rTbf : ℕ := 186

/-! ## The programs -/

/-- The forward arithmetic: `fT := α w`, `fN := u + fT`, `fH := fN + w`. -/
def farithIR : XIR :=
  .seq (ldF fU rAL rAL1) (.seq (ldF fW rAH rAH1) (.seq (mulF fT fAl fW) (.seq (addF fN fU fT)
    (addF fH fN fW))))

/-- **One forward butterfly**: pair `q` of the level in `rLv`. -/
def fpairBody : XIR :=
  .seq (.blk pairPs) (.seq alphaIR (.seq farithIR (.seq (stF rAL rAL1 fN)
    (.seq (stF rAH rAH1 fH) (.blk [.op .add rQ rQ cOne])))))

/-- **A forward level**: the `2^(ℓ−1)` pairs, `P = 2^l`. -/
def flevelIR (ℓ : ℕ) : XIR :=
  .seq (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))])
    (.loopK rC1 rN1 (toWord (2 ^ (ℓ - 1))) fpairBody)

/-- The level's registers: `rLv := rKf − 1`, `rTr := tb + 40 rLv`. -/
def fPre : List Prim :=
  [.op .sub rLv rKf cOne, .const uT1 40, .op .mul rTr rLv uT1, .op .add rTr rTr rTbf]

/-- One step: the level `rKf − 1`, then `rKf −= 1`. -/
def fStep (ℓ : ℕ) : XIR := .seq (.blk fPre) (.seq (flevelIR ℓ) (.blk [.op .sub rKf rKf cOne]))

/-- **The forward butterflies**: levels `ℓ − 1 … 0` on the row at `rA0`, the table at `tb`. -/
def fwdIR (ℓ tb : ℕ) : XIR :=
  .seq (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)])
    (.loopK rC3 rN3 (toWord ℓ) (fStep ℓ))

/-! ## Well formed, no tape loop, no output, cost -/

theorem wf_fwdIR (ℓ tb : ℕ) : WF (fwdIR ℓ tb) := by
  simp [fwdIR, fStep, fPre, flevelIR, fpairBody, pairPs, farithIR, alphaIR, alphaBody, ldF, stF,
    addF, mulF, addFC, mulFC, redC, WF, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL,
    rAL1, rAH, rAH1, rTa, rTa1, rBit, uI, rTr, rC1, rN1, rC2, rN2, rC3, rN3, fAl, fU, fW, fH, fT,
    fN, fG, rKf, rTbf, cTmp, regs]

theorem noLoopT_fwdIR (ℓ tb : ℕ) : NoLoopT (fwdIR ℓ tb) := by
  simp [fwdIR, fStep, flevelIR, fpairBody, farithIR, alphaIR, alphaBody, ldF, stF, addF, mulF,
    NoLoopT]

theorem outs_fwdIR (ℓ tb t : ℕ) : outs (fwdIR ℓ tb) t = 0 := by
  simp [fwdIR, fStep, flevelIR, fpairBody, farithIR, alphaIR, alphaBody, ldF, stF, addF, mulF,
    outs]

theorem cost_fpairBody (t : ℕ) : cost fpairBody t = 738 := by
  simp only [fpairBody, pairPs, farithIR, ldF, stF, cost, cost_alphaIR, addF, mulF, blkSteps,
    len_addFC, len_mulFC, List.length_cons, List.length_nil]
  norm_num

/-- **The forward butterflies' cost**: `ℓ` levels of `2^(ℓ−1)` pairs. -/
theorem cost_fwdIR (ℓ tb t : ℕ) (hℓ : 2 ^ (ℓ - 1) < 2 ^ 64) (hℓ' : ℓ < 2 ^ 64) :
    cost (fwdIR ℓ tb) t = 14 + ℓ * (741 * 2 ^ (ℓ - 1) + 27) := by
  have a1 : (toWord (2 ^ (ℓ - 1))).toNat = 2 ^ (ℓ - 1) := toNat_toWord hℓ
  have a2 : (toWord ℓ).toNat = ℓ := toNat_toWord hℓ'
  simp only [fwdIR, fStep, fPre, flevelIR, cost, cost_fpairBody, blkSteps, List.length_cons,
    List.length_nil, a1, a2]
  norm_num
  ring

/-! ## The pure level at a pair -/

theorem fwdLevel_lo (l q : ℕ) (Y : ℕ → F) :
    fwdLevel (M := F) l Y (loP l q) = Y (loP l q) + wAtD l (baseP l q) * Y (hiP l q) := by
  have hm := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  obtain ⟨d1, d2⟩ := loP_div l q
  simp only [fwdLevel, d1, d2, Nat.mod_mod, if_pos hm]
  rw [show q / 2 ^ l * 2 ^ (l + 1) + 2 ^ l + q % 2 ^ l = hiP l q by
    simp only [hiP, loP, baseP]; omega]
  rfl

theorem fwdLevel_hi (l q : ℕ) (Y : ℕ → F) :
    fwdLevel (M := F) l Y (hiP l q) =
      Y (loP l q) + wAtD l (baseP l q) * Y (hiP l q) + Y (hiP l q) := by
  have hm := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  obtain ⟨d1, d2⟩ := hiP_div l q
  simp only [fwdLevel, d1, d2, if_neg (show ¬ (q % 2 ^ l + 2 ^ l < 2 ^ l) by omega),
    Nat.add_mod_right, Nat.mod_mod]
  rw [show q / 2 ^ l * 2 ^ (l + 1) + 2 ^ l + q % 2 ^ l = hiP l q by
    simp only [hiP, loP, baseP]; omega]
  rfl

/-- The first `j` forward levels, `ℓ − 1, …, ℓ − j`. -/
def fwdTop (ℓ : ℕ) : ℕ → (ℕ → F) → ℕ → F
  | 0, Y => Y
  | j + 1, Y => fwdLevel (ℓ - 1 - j) (fwdTop ℓ j Y)

theorem fwdRun_top (ℓ : ℕ) (Y : ℕ → F) : ∀ j ≤ ℓ, fwdRun ℓ Y = fwdRun (ℓ - j) (fwdTop ℓ j Y)
  | 0, _ => rfl
  | j + 1, hj => by
    rw [fwdRun_top ℓ Y j (by omega), show ℓ - j = (ℓ - (j + 1)) + 1 by omega, fwdRun, fwdTop,
      show ℓ - (j + 1) = ℓ - 1 - j by omega]

/-! ## One forward butterfly, a level -/

theorem wf_farithIR : WF farithIR := by
  simp [farithIR, ldF, addF, mulF, addFC, mulFC, redC, WF, Prim.dst, fU, fW, fH, fT, fN, rAL1, rAH1]

theorem lo_farithIR : Lo farithIR := by
  simp [farithIR, ldF, addF, mulF, addFC, mulFC, redC, Lo, Prim.dst, regs, fU, fW, fH, fT, fN, rAL1,
    rAH1]

theorem wf_fpairBody : WF fpairBody := by
  simp [fpairBody, pairPs, farithIR, alphaIR, alphaBody, ldF, stF, addF, mulF, addFC, mulFC, redC, WF,
    Writes, Prim.dst, rQ, uX, uT1, uT2, rBs, rAL, rAL1, rAH, rAH1, rTa, rTa1, rBit, uI, rC2, rN2,
    fAl, fU, fW, fH, fT, fN, fG, cTmp, regs]

/-- **The forward arithmetic**: `fN := U + α W`, `fH := U + α W + W` for the heap elements `U`
at `a` and `W` at `b`, `α` in `fAl`. -/
theorem farith_sem (I : Array Word) (s : St) (hM : Inv s.M) {a b : ℕ} (ha : regs ≤ a)
    (ha2 : a + 1 < 2 ^ 64) (hb : regs ≤ b) (hb2 : b + 1 < 2 ^ 64)
    (hAL : rd s.M rAL = toWord a) (hAH : rd s.M rAH = toWord b) :
    rdF (semXIR I farithIR s).M fN = rdF s.M a + rdF s.M fAl * rdF s.M b ∧
    rdF (semXIR I farithIR s).M fH = rdF s.M a + rdF s.M fAl * rdF s.M b + rdF s.M b := by
  have hs := hM.1
  simp only [regs] at hs ha hb
  rw [farithIR, semXIR_seq]
  obtain ⟨u1, -, u3⟩ := ldF_sem I s hM (d := fU) (p := rAL) (p1 := rAL1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hAL (by simp only [regs]; omega) ha2
  have hM1 := inv_sem I (P := ldF fU rAL rAL1) (by simp [ldF, WF, Prim.dst, fU, rAL1]) hM
  generalize semXIR I (ldF fU rAL rAL1) s = s1 at u1 u3 hM1
  have hAH1 : rd s1.M rAH = toWord b := (u3 _ (by decide) (by decide) (by decide)).trans hAH
  have hal1 : rdF s1.M fAl = rdF s.M fAl :=
    rdF_eq (u3 _ (by decide) (by decide) (by decide)) (u3 _ (by decide) (by decide) (by decide))
  have hb1 : rdF s1.M b = rdF s.M b :=
    rdF_eq (u3 _ (by simp only [fU]; omega) (by simp only [fU]; omega) (by simp only [rAL1]; omega))
      (u3 _ (by simp only [fU]; omega) (by simp only [fU]; omega) (by simp only [rAL1]; omega))
  rw [semXIR_seq]
  obtain ⟨w1, -, w3⟩ := ldF_sem I s1 hM1 (d := fW) (p := rAH) (p1 := rAH1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hAH1 (by simp only [regs]; omega) hb2
  have hM2 := inv_sem I (P := ldF fW rAH rAH1) (by simp [ldF, WF, Prim.dst, fW, rAH1]) hM1
  generalize semXIR I (ldF fW rAH rAH1) s1 = s2 at w1 w3 hM2
  have hu2 : rdF s2.M fU = rdF s.M a :=
    (rdF_eq (w3 _ (by decide) (by decide) (by decide)) (w3 _ (by decide) (by decide) (by decide))).trans u1
  have hal2 : rdF s2.M fAl = rdF s.M fAl :=
    (rdF_eq (w3 _ (by decide) (by decide) (by decide)) (w3 _ (by decide) (by decide) (by decide))).trans hal1
  have hw2 : rdF s2.M fW = rdF s.M b := w1.trans hb1
  rw [semXIR_seq]
  have h3 := mulF_sem (I := I) (s := s2) hM2 (d := fT) (a := fAl) (b := fW) (by decide) (by decide)
    (by decide) (by decide)
  have f3 : ∀ i, 15 ≤ i → i ≠ fT → i ≠ fT + 1 → rd (semXIR I (mulF fT fAl fW) s2).M i = rd s2.M i :=
    fun i h0 h1 h2 => by rw [mulF, sem_blk]; exact mulFC_frame _ _ _ (.inr h0) h1 h2 _
  have hM3 := inv_sem I (wf_mulF fT fAl fW (by decide)) hM2
  generalize semXIR I (mulF fT fAl fW) s2 = s3 at h3 f3 hM3
  have hu3 : rdF s3.M fU = rdF s.M a :=
    (rdF_eq (f3 _ (by decide) (by decide) (by decide)) (f3 _ (by decide) (by decide) (by decide))).trans hu2
  have hw3 : rdF s3.M fW = rdF s.M b :=
    (rdF_eq (f3 _ (by decide) (by decide) (by decide)) (f3 _ (by decide) (by decide) (by decide))).trans hw2
  rw [semXIR_seq]
  have h4 := addF_sem (I := I) (s := s3) hM3 (d := fN) (a := fU) (b := fT) (by decide) (by decide)
    (by decide)
  have f4 : ∀ i, i ≠ fN → i ≠ fN + 1 → rd (semXIR I (addF fN fU fT) s3).M i = rd s3.M i :=
    fun i h1 h2 => addFC_frame _ _ _ h1 h2 _
  have hM4 := inv_sem I (wf_addF fN fU fT (by decide)) hM3
  generalize semXIR I (addF fN fU fT) s3 = s4 at h4 f4 hM4
  have hw4 : rdF s4.M fW = rdF s.M b :=
    (rdF_eq (f4 _ (by decide) (by decide)) (f4 _ (by decide) (by decide))).trans hw3
  have hn4 : rdF s4.M fN = rdF s.M a + rdF s.M fAl * rdF s.M b := by rw [h4, hu3, h3, hal2, hw2]
  have h5 := addF_sem (I := I) (s := s4) hM4 (d := fH) (a := fN) (b := fW) (by decide) (by decide)
    (by decide)
  refine ⟨?_, ?_⟩
  · rw [addF, ← hn4]
    exact rdF_eq (addFC_frame fH fN fW (i := fN) (by decide) (by decide) _)
      (addFC_frame fH fN fW (i := fN + 1) (by decide) (by decide) _)
  · rw [h5, hn4, hw4]

theorem fpairBody_nw {r : ℕ} (hr : r = rA0 ∨ r = rP2 ∨ r = rTr ∨ r = rLv ∨ r = rC1 ∨ r = rN1 ∨
    r = rC3 ∨ r = rN3) : ¬ Writes fpairBody r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [fpairBody, pairPs, farithIR, alphaIR, alphaBody, ldF, stF, addF, mulF, addFC, mulFC, redC,
    Writes, Prim.dst, rQ, uX, uT1, uT2, rBs, rAL, rAL1, rAH, rAH1, rTa, rTa1, rBit, uI, rC2, rN2,
    fAl, fU, fW, fH, fT, fN, fG, cTmp, rA0, rP2, rTr, rLv, rC1, rN1, rC3, rN3]

/-- **One butterfly**: the pair's low and high elements become `u + α (w + u)` and `w + u`,
`α = Σ_{i<20} [bit_i(base)] T(i)`; nothing else on the heap changes; `q += 1`. -/
theorem fpairBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {A ta l q : ℕ} {T : ℕ → F}
    (hl : l < 20) (hA : regs ≤ A) (hq : q < 2 ^ 64) (hhi : A + 2 * hiP l q + 2 < 2 ^ 64)
    (hsz : A + 2 * hiP l q + 1 < s.M.size) (hta : regs ≤ ta) (hta2 : ta + 40 < 2 ^ 64)
    (hQ : rd s.M rQ = toWord q) (hP2 : rd s.M rP2 = toWord (2 ^ l)) (hA0 : rd s.M rA0 = toWord A)
    (hTr : rd s.M rTr = toWord ta) (hT : ∀ i < 20, rdF s.M (ta + 2 * i) = T i) :
    rdF (semXIR I fpairBody s).M (A + 2 * loP l q) = rdF s.M (A + 2 * loP l q) +
      (∑ i ∈ range 20, if (baseP l q).testBit i then T i else 0) * rdF s.M (A + 2 * hiP l q) ∧
    rdF (semXIR I fpairBody s).M (A + 2 * hiP l q) = rdF s.M (A + 2 * loP l q) +
      (∑ i ∈ range 20, if (baseP l q).testBit i then T i else 0) * rdF s.M (A + 2 * hiP l q) +
        rdF s.M (A + 2 * hiP l q) ∧
    (∀ x, regs ≤ x → x ≠ A + 2 * loP l q → x ≠ A + 2 * loP l q + 1 → x ≠ A + 2 * hiP l q →
      x ≠ A + 2 * hiP l q + 1 → rd (semXIR I fpairBody s).M x = rd s.M x) ∧
    rd (semXIR I fpairBody s).M rQ = toWord (q + 1) := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hlh := loP_lt_hiP l q
  have hP : 2 ^ l < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hbase : baseP l q < 2 ^ 64 := by have : baseP l q ≤ loP l q := by simp [loP]
                                        omega
  -- the addresses
  have w1 : WF (.blk pairPs) := by
    simp [pairPs, WF, Prim.dst, uT1, uX, uT2, rBs, rAL, rAH]
  obtain ⟨p1, p2, p3⟩ := pairPs_sem I s hM (A := A) hq hP hQ hP2 hA0
  have hM1 := inv_sem I w1 hM
  have z1 := size_sem I (.blk pairPs) s
  have hH1 := hframe I (.blk pairPs) s (by simp [pairPs, Lo, Prim.dst, regs, uT1, uX, uT2, rBs, rAL,
    rAH])
  have q1 : rd (semXIR I (.blk pairPs) s).M rQ = toWord q := by
    rw [frame I _ s w1 hM _ (by decide) (by simp [pairPs, Writes, Prim.dst, uT1, uX, uT2, rBs, rAL,
      rAH, rQ]), hQ]
  have t1 : rd (semXIR I (.blk pairPs) s).M rTr = toWord ta := by
    rw [frame I _ s w1 hM _ (by decide) (by simp [pairPs, Writes, Prim.dst, uT1, uX, uT2, rBs, rAL,
      rAH, rTr]), hTr]
  rw [fpairBody, semXIR_seq]
  generalize semXIR I (.blk pairPs) s = s1 at p1 p2 p3 hM1 hH1 q1 t1 z1
  have hT1 : ∀ i < 20, rdF s1.M (ta + 2 * i) = T i := fun i hi => by
    rw [← hT i hi]; exact rdF_eq (hH1 _ (by simp only [regs]; omega)) (hH1 _ (by simp only [regs]; omega))
  -- `α`
  have a2 := alphaIR_sem I s1 hM1 hbase (by simp only [regs]; omega) hta2 p1 t1 hT1
  have hM2 := inv_sem I wf_alphaIR hM1
  have z2 := size_sem I alphaIR s1
  have hH2 := hframeK I alphaIR s1 loK_alphaIR
  have nwA : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I alphaIR s1).M r = rd s1.M r :=
    fun r hr => frame I _ s1 wf_alphaIR hM1 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp [alphaIR, alphaBody, ldF, Writes, Prim.dst, rBit, uT1, rTa, rTa1, fG, fAl, uI, rN2, rC2,
        cTmp, rAL, rAH, rQ])
  rw [semXIR_seq]
  generalize semXIR I alphaIR s1 = s2 at a2 hM2 hH2 nwA z2
  have l2 : rd s2.M rAL = toWord (A + 2 * loP l q) := (nwA _ (.inl rfl)).trans p2
  have h2 : rd s2.M rAH = toWord (A + 2 * hiP l q) := (nwA _ (.inr (.inl rfl))).trans p3
  have q2 : rd s2.M rQ = toWord q := (nwA _ (.inr (.inr rfl))).trans q1
  have hY : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => (hH2 x hx).trans (hH1 x hx)
  -- the arithmetic
  obtain ⟨b1, b2⟩ := farith_sem I s2 hM2 (a := A + 2 * loP l q) (b := A + 2 * hiP l q)
    (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega) (by omega) l2 h2
  have hM3 := inv_sem I wf_farithIR hM2
  have z3 := size_sem I farithIR s2
  have hH3 := hframe I farithIR s2 lo_farithIR
  have nwB : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I farithIR s2).M r = rd s2.M r :=
    fun r hr => frame I _ s2 wf_farithIR hM2 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp [farithIR, ldF, addF, mulF, addFC, mulFC, redC, Writes, Prim.dst, fU, fW, fH, fT, fN,
        rAL1, rAH1, rAL, rAH, rQ])
  have eU : rdF s2.M (A + 2 * loP l q) = rdF s.M (A + 2 * loP l q) :=
    rdF_eq (hY _ (by simp only [regs]; omega)) (hY _ (by simp only [regs]; omega))
  have eW : rdF s2.M (A + 2 * hiP l q) = rdF s.M (A + 2 * hiP l q) :=
    rdF_eq (hY _ (by simp only [regs]; omega)) (hY _ (by simp only [regs]; omega))
  rw [eU, eW, a2] at b1
  rw [eU, eW, a2] at b2
  rw [semXIR_seq]
  generalize semXIR I farithIR s2 = s3 at b1 b2 hM3 hH3 nwB z3
  have l3 : rd s3.M rAL = toWord (A + 2 * loP l q) := (nwB _ (.inl rfl)).trans l2
  have h3 : rd s3.M rAH = toWord (A + 2 * hiP l q) := (nwB _ (.inr (.inl rfl))).trans h2
  have q3 : rd s3.M rQ = toWord q := (nwB _ (.inr (.inr rfl))).trans q2
  -- the stores
  obtain ⟨c1, c2, hM4⟩ := stF_sem I s3 hM3 (p := rAL) (p1 := rAL1) (v := fN)
    (x := A + 2 * loP l q) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) l3 (by simp only [regs]; omega) (by omega) (by omega)
  have z4 := size_sem I (stF rAL rAL1 fN) s3
  rw [semXIR_seq]
  generalize semXIR I (stF rAL rAL1 fN) s3 = s4 at c1 c2 hM4 z4
  have hr4 : ∀ r, r < 256 → r ≠ rAL1 → r ≠ cTmp → rd s4.M r = rd s3.M r := fun r hr h1 h2 =>
    c2 r (by omega) (by omega) h1 h2
  have h4 : rd s4.M rAH = toWord (A + 2 * hiP l q) := (hr4 _ (by decide) (by decide) (by decide)).trans h3
  have q4 : rd s4.M rQ = toWord q := (hr4 _ (by decide) (by decide) (by decide)).trans q3
  have f4 : rdF s4.M fH = rdF s3.M fH :=
    rdF_eq (hr4 _ (by decide) (by decide) (by decide)) (hr4 _ (by decide) (by decide) (by decide))
  obtain ⟨d1, d2, hM5⟩ := stF_sem I s4 hM4 (p := rAH) (p1 := rAH1) (v := fH)
    (x := A + 2 * hiP l q) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h4 (by simp only [regs]; omega) (by omega) (by omega)
  rw [semXIR_seq]
  generalize semXIR I (stF rAH rAH1 fH) s4 = s5 at d1 d2 hM5
  have hr5 : ∀ r, r < 256 → r ≠ rAH1 → r ≠ cTmp → rd s5.M r = rd s4.M r := fun r hr h1 h2 =>
    d2 r (by omega) (by omega) h1 h2
  -- `q += 1`
  have e6 : ∀ x, x ≠ rQ → rd (semXIR I (.blk [.op .add rQ rQ cOne]) s5).M x = rd s5.M x :=
    fun x hx => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact fun h => hx h.symm) _
  have hT4 : cTmp = 4 := rfl
  refine ⟨?_, ?_, fun x hx x1 x2 x3 x4 => ?_, ?_⟩
  · rw [rdF_eq (e6 _ (by simp only [rQ]; omega)) (e6 _ (by simp only [rQ]; omega)),
      rdF_eq (d2 _ (by omega) (by omega) (by simp only [rAH1]; omega) (by omega))
        (d2 _ (by omega) (by omega) (by simp only [rAH1]; omega) (by omega)), c1, b1]
  · rw [rdF_eq (e6 _ (by simp only [rQ]; omega)) (e6 _ (by simp only [rQ]; omega)), d1, f4, b2]
  · simp only [regs] at hx
    rw [e6 _ (by simp only [rQ]; omega), d2 _ x3 x4 (by simp only [rAH1]; omega) (by omega),
      c2 _ x1 x2 (by simp only [rAL1]; omega) (by omega), hH3 x (by simp only [regs]; omega),
      hY x (by simp only [regs]; omega)]
  · have hs5 := hM5.1
    simp only [regs] at hs5
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rQ]; omega), hr5 _ (by decide) (by decide) (by decide), q4,
      hr5 _ (by decide) (by decide) (by decide), show rd s4.M cOne = 1 from hM4.2 0 (by decide)]
    exact add_one_toWord q

/-! ## A level, and the iteration -/

/-- **A level** `l < ℓ` on the row of `2^ℓ` elements at `A`, with the table row `wRow D 20 l` at
`ta`: every element becomes `bflyLevel`'s; the heap outside the row is kept. -/
theorem flevelIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {A ta ℓ l : ℕ} {Y : ℕ → F}
    (hℓ : ℓ ≤ 20) (hl : l < ℓ) (hA : regs ≤ A) (hA2 : A + 2 * 2 ^ ℓ + 1 < 2 ^ 64)
    (hsz : A + 2 * 2 ^ ℓ ≤ s.M.size) (hta : regs ≤ ta) (hta2 : ta + 40 < 2 ^ 64)
    (hdisj : ta + 40 ≤ A ∨ A + 2 * 2 ^ ℓ ≤ ta)
    (hLv : rd s.M rLv = toWord l) (hA0 : rd s.M rA0 = toWord A) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < 20, rdF s.M (ta + 2 * i) = (wRow D logNMax l).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdF s.M (A + 2 * i) = Y i) :
    (∀ i < 2 ^ ℓ, rdF (semXIR I (flevelIR ℓ) s).M (A + 2 * i) =
      fwdLevel (M := F) l Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 * 2 ^ ℓ ≤ x) → rd (semXIR I (flevelIR ℓ) s).M x = rd s.M x) ∧
    (semXIR I (flevelIR ℓ) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hP1 : 2 ^ (ℓ - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hPl : l * 1 < 64 := by omega
  have w0 : WF (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))]) := by
    simp [WF, Prim.dst, rQ, rP2, rN1]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s
  have hH0 := hframe I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s (by simp [Lo, Prim.dst, regs, rQ, rP2, rN1])
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
    · rw [hLv, show rd s.M cOne = toWord 1 from hM.2 0 (by decide),
        shl_toWord (by omega) (by rw [Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)),
        Nat.one_mul]
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
    (∀ x, regs ≤ x → (x < A ∨ A + 2 * 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdF s'.M (A + 2 * i) =
      if pairOf l i < j then fwdLevel (M := F) l Y i else Y i
  have nwP : ∀ r, (r = rA0 ∨ r = rP2 ∨ r = rTr) → ∀ s', Inv s'.M →
      rd (decS rC1 (semXIR I fpairBody s')).M r = rd s'.M r := fun r hr s' hs' => by
    rw [rd_decS (by rcases hr with rfl | rfl | rfl <;> decide)]
    exact frame I _ s' wf_fpairBody hs' _ (by rcases hr with rfl | rfl | rfl <;> decide)
      (fpairBody_nw (by rcases hr with rfl | rfl | rfl <;> simp))
  have step : ∀ j s', j < 2 ^ (ℓ - 1) → P j s' → P (j + 1) (decS rC1 (semXIR I fpairBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    have hhi := hiP_lt hl hj
    have hlh := loP_lt_hiP l j
    have hT' : ∀ i < 20, rdF s'.M (ta + 2 * i) = (wRow D logNMax l).getD i 0 := fun i hi => by
      rw [← hT i hi]
      exact rdF_eq (i7 _ (by simp only [regs]; omega) (by omega))
        (i7 _ (by simp only [regs]; omega) (by omega))
    have hp2 : 2 * hiP l j + 2 ≤ 2 * 2 ^ ℓ := by omega
    obtain ⟨e1, e2, e3, e4⟩ := fpairBody_sem I s' i1 (A := A) (T := fun i => (wRow D logNMax l).getD i 0)
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
      rw [hd _ (by simp only [rC1]; omega), e3 x (by simp only [regs]; omega) (by omega) (by omega)
        (by omega) (by omega), i7 x (by simp only [regs]; omega) hx2]
    · have hdF : ∀ y, regs ≤ y → rdF (decS rC1 (semXIR I fpairBody s')).M y =
          rdF (semXIR I fpairBody s').M y := fun y hy =>
        rdF_eq (hd _ (by simp only [rC1, regs] at *; omega)) (hd _ (by simp only [rC1, regs] at *; omega))
      rw [hdF _ (by simp only [regs]; omega)]
      by_cases hq : pairOf l i = j
      · rw [if_pos (by omega)]
        rcases pair_cases hq with rfl | rfl
        · rw [e1, hlo', hhi', fwdLevel_lo]; rfl
        · rw [e2, hlo', hhi', fwdLevel_hi]; rfl
      · have hil : i ≠ loP l j := fun h => hq (by rw [h, pairOf_loP])
        have hih : i ≠ hiP l j := fun h => hq (by rw [h, pairOf_hiP])
        rw [rdF_eq (e3 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega))
          (e3 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)), i8 i hi]
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
      exact rdF_eq ((hE _ (by simp only [rC1]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
        ((hE _ (by simp only [rC1]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
  have := iterL_ind (f := semXIR I fpairBody) (c := rC1) (m := 2 ^ (ℓ - 1)) P step (2 ^ (ℓ - 1)) 0 _
    (by omega) hP0
  rw [Nat.zero_add] at this
  obtain ⟨-, z, -, -, -, -, f7, f8⟩ := this
  refine ⟨fun i hi => ?_, f7, z⟩
  rw [f8 i hi, if_pos (pairOf_lt hl hi)]

theorem flevelIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rLv ∨ r = rTr ∨ r = rC3 ∨ r = rN3) (ℓ : ℕ) :
    ¬ Writes (flevelIR ℓ) r := by
  intro h
  simp only [flevelIR, Writes] at h
  rcases h with ⟨p, hp, he⟩ | h | h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [Prim.dst, rQ, rP2, rN1, rA0, rLv, rTr, rC3, rN3] at he
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [rC1, rA0, rLv, rTr, rC3, rN3] at h
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [cTmp, rA0, rLv, rTr, rC3, rN3] at h
  · exact fpairBody_nw (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) h

/-! ## The forward butterflies -/

theorem fPre_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ j tb : ℕ} (hj : j < ℓ)
    (hℓ : ℓ < 2 ^ 64) (htb : tb + 40 * ℓ < 2 ^ 64)
    (hK : rd s.M rKf = toWord (ℓ - j)) (hTb : rd s.M rTbf = toWord tb) :
    rd (semXIR I (.blk fPre) s).M rLv = toWord (ℓ - 1 - j) ∧
    rd (semXIR I (.blk fPre) s).M rTr = toWord (tb + 40 * (ℓ - 1 - j)) ∧
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
    rw [hK, e1, sub_toWord (by omega) (by omega), hTb, show (40 : Word) = toWord 40 from rfl,
      mul_toWord, add_toWord]
    congr 1; rw [show ℓ - j - 1 = ℓ - 1 - j by omega]; ring

/-- **The forward butterflies** (`fwdRun`) on the machine: from the row `Y` of `2^ℓ` elements at
`A` (`rA0 = A`) and the basis table at `tb`, `fwdIR ℓ tb` leaves `fwdRun ℓ Y` in the row and keeps
the heap outside it. -/
theorem fwdIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ} {Y : ℕ → F}
    (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 20) (hA : regs ≤ A) (hA2 : A + 2 * 2 ^ ℓ + 1 < 2 ^ 64)
    (hsz : A + 2 * 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 800 < 2 ^ 64)
    (hdisj : tb + 800 ≤ A ∨ A + 2 * 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdF s.M (A + 2 * i) = Y i) :
    (∀ i < 2 ^ ℓ, rdF (semXIR I (fwdIR ℓ tb) s).M (A + 2 * i) = fwdRun (M := F) ℓ Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 * 2 ^ ℓ ≤ x) → rd (semXIR I (fwdIR ℓ tb) s).M x = rd s.M x) ∧
    Inv (semXIR I (fwdIR ℓ tb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hA htb
  have hℓ64 : ℓ < 2 ^ 64 := by omega
  have w0 : WF (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)]) := by
    simp [WF, Prim.dst, rKf, rTbf, rN3]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)]) s
  have hH0 := hframe I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)]) s
    (by simp [Lo, Prim.dst, regs, rKf, rTbf, rN3])
  have r0 : rd (semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)])
        s).M rKf = toWord (ℓ - 0) ∧
      rd (semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)])
        s).M rTbf = toWord tb ∧
      rd (semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)])
        s).M rN3 = toWord ℓ ∧
      rd (semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)])
        s).M rA0 = toWord A := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rKf, rTbf, rN3]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · exact hA0
  rw [fwdIR, semXIR_seq]
  generalize semXIR I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)]) s
    = s0 at hM0 z0 hH0 r0
  obtain ⟨k0, t0, n0, a0⟩ := r0
  rw [loopK_eq I (fStep ℓ) s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hℓ64]
  have hE : ∀ i, i ≠ rC3 → i ≠ cTmp → rd (entryK rC3 rN3 (toWord ℓ) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC3) (n := rN3) (K := toWord ℓ) hM0 (by decide)
  have wf := wf_fwdIR ℓ tb
  have wpre : WF (.blk fPre) := by simp [fPre, WF, Prim.dst, rLv, uT1, rTr]
  have wl : WF (flevelIR ℓ) := by
    simp [flevelIR, fpairBody, pairPs, farithIR, alphaIR, alphaBody, ldF, stF, addF, mulF, addFC,
      mulFC, redC, WF, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAL1, rAH, rAH1, rTa,
      rTa1, rBit, uI, rTr, rC1, rN1, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, regs]
  have wlb : WF (.blk [.op .sub rKf rKf cOne]) := by simp [WF, Prim.dst, rKf]
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rKf = toWord (ℓ - j) ∧ rd s'.M rTbf = toWord tb ∧ rd s'.M rA0 = toWord A ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 * 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdF s'.M (A + 2 * i) = fwdTop ℓ j Y i
  have step : ∀ j s', j < ℓ → P j s' → P (j + 1) (decS rC3 (semXIR I (fStep ℓ) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨p1, p2, p3⟩ := fPre_sem I s' i1 hj hℓ64 (tb := tb) (by omega) i3 i4
    have hM1 := inv_sem I wpre i1
    have hH1 := hframe I (.blk fPre) s' (by simp [fPre, Lo, Prim.dst, regs, rLv, uT1, rTr])
    have z1 := size_sem I (.blk fPre) s'
    rw [fStep, semXIR_seq, semXIR_seq]
    generalize semXIR I (.blk fPre) s' = s1 at p1 p2 p3 hM1 hH1 z1
    have hT : ∀ i < 20, rdF s1.M (tb + 40 * (ℓ - 1 - j) + 2 * i) =
        (wRow D logNMax (ℓ - 1 - j)).getD i 0 := fun i hi => by
      rw [← hW (ℓ - 1 - j) (by omega) i hi]
      exact rdF_eq ((hH1 _ (by simp only [regs]; omega)).trans
          (i6 _ (by simp only [regs]; omega) (by omega)))
        ((hH1 _ (by simp only [regs]; omega)).trans (i6 _ (by simp only [regs]; omega) (by omega)))
    have hY1 : ∀ i < 2 ^ ℓ, rdF s1.M (A + 2 * i) = fwdTop ℓ j Y i := fun i hi => by
      rw [← i7 i hi]
      exact rdF_eq (hH1 _ (by simp only [regs]; omega)) (hH1 _ (by simp only [regs]; omega))
    have a1 : rd s1.M rA0 = toWord A := (p3 _ (by decide) (by decide) (by decide)).trans i5
    obtain ⟨e1, e2, e3⟩ := flevelIR_sem I s1 hM1 (Y := fwdTop ℓ j Y) (l := ℓ - 1 - j) hℓ (by omega)
      (by simp only [regs]; omega) hA2 (by omega) (by simp only [regs]; omega) (by omega)
      (by omega) p1 a1 p2 hT hY1
    have hM2 := inv_sem I wl hM1
    have nw : ∀ r, (r = rA0 ∨ r = rKf ∨ r = rTbf) → rd (semXIR I (flevelIR ℓ) s1).M r = rd s1.M r :=
      fun r hr => frame I _ s1 wl hM1 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
        rcases hr with rfl | rfl | rfl <;>
        simp [flevelIR, fpairBody, pairPs, farithIR, alphaIR, alphaBody, ldF, stF, addF, mulF,
          addFC, mulFC, redC, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAL1, rAH,
          rAH1, rTa, rTa1, rBit, uI, rTr, rC1, rN1, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp,
          rA0, rKf, rTbf])
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
    · rw [rdF_eq ((hd _ (by simp only [rC3]; omega)).trans (hb _ (by simp only [rKf]; omega)))
        ((hd _ (by simp only [rC3]; omega)).trans (hb _ (by simp only [rKf]; omega))), e1 i hi]
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
      exact rdF_eq ((hE _ (by simp only [rC3]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
        ((hE _ (by simp only [rC3]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
  have := iterL_ind (f := semXIR I (fStep ℓ)) (c := rC3) (m := ℓ) P step ℓ 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  refine ⟨fun i hi => ?_, this.2.2.2.2.2.1, this.1⟩
  rw [this.2.2.2.2.2.2 i hi, fwdRun_top ℓ Y ℓ le_rfl, Nat.sub_self]
  rfl

/-- **`Enc` on the machine**: on a message `c` of `2^m` coefficients zero-padded to the row of
`2^ℓ` elements (`m ≤ ℓ`), `fwdIR ℓ tb` leaves `encF m c j` at every position `j < 2^ℓ`. -/
theorem fwdIR_enc (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ m : ℕ}
    (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 20) (hmℓ : m ≤ ℓ) (hA : regs ≤ A) (hA2 : A + 2 * 2 ^ ℓ + 1 < 2 ^ 64)
    (hsz : A + 2 * 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 800 < 2 ^ 64)
    (hdisj : tb + 800 ≤ A ∨ A + 2 * 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (c : Fin (2 ^ m) → F)
    (hY : ∀ i < 2 ^ ℓ, rdF s.M (A + 2 * i) = if h : i < 2 ^ m then c ⟨i, h⟩ else 0) :
    ∀ j < 2 ^ ℓ, rdF (semXIR I (fwdIR ℓ tb) s).M (A + 2 * j) = encF m c j := by
  intro j hj
  rw [(fwdIR_sem I s hM hℓ1 hℓ hA hA2 hsz htb htb2 hdisj hA0 hW
    (Y := fun i => if h : i < 2 ^ m then c ⟨i, h⟩ else 0) hY).1 j hj]
  exact fwdRun_enc hmℓ hℓ c _ (fun _ => rfl) hj

end FR.X
