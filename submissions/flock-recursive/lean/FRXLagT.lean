-- New for `flock-recursive` (BLUEPRINT revision 4.2, §10 changes 27 (A)(ii); stage S-H4, pass 2).
import FRXLag

/-!
# The target half of `lagIR`: the forward and backward passes, the outputs

`FRXLag` proves the weights and values (`yTab_sem`). This module proves the target loop `tgIR`:

* `fwdLoop_sem`: the forward pass stores the prefix products `P_t = preP J s t` at `pb + t`;
* `accIR_sem`: the `C` unrolled rows add `e · Y_c[t]` to the accumulators;
* `bwdLoop_sem`: the backward pass leaves `acc_c = Σ_{t<k} P_t · Q_t · Y_c[t]`
  (`Q_t = sufP J k s (t + 1)`);
* `stAcc_sem`: the `C` outputs, row `c` at `o + 2kc`;
* `tgIR_sem`: every target `s < k`; then **`lagIR_sem`** (output row `c` at target `s` is
  `lagVal J k s y_{c₀+c}`) and **`lagIR_interp`** (the same is `interpF D J y s`).
-/

namespace FR.X

open RecursionFast FR Finset

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-! ## The forward pass -/

theorem fwd_blk (M : Mem) (hM : Inv M) {a b : ℕ} (hA : rd M lgA = toWord a) (hB : rd M lgB = toWord b) :
    let M' := runPrims ([.op .xor lgD lgS lgJ, .op .add lgA lgA cOne, .op .add lgB lgB cOne] ++
      mulBC lgP lgP lgD) M
    rd M' lgA = toWord (a + 1) ∧ rd M' lgB = toWord (b + 1) ∧
    rdB M' lgP = rdB M lgP * wB (rd M lgS ^^^ rd M lgJ) ∧
    (∀ i, i ≠ lgD → i ≠ lgA → i ≠ lgB → i ≠ lgP → (i < 5 ∨ 9 ≤ i) → rd M' i = rd M i) ∧ Inv M' := by
  intro M'
  have hs : 256 ≤ M.size := hM.1
  have h1 : rd M cOne = 1 := hM.2 0 (by decide)
  have e : M' = runPrims (mulBC lgP lgP lgD)
      (runPrims [.op .xor lgD lgS lgJ, .op .add lgA lgA cOne, .op .add lgB lgB cOne] M) :=
    runPrims_append ..
  have hI : Inv (runPrims [.op .xor lgD lgS lgJ, .op .add lgA lgA cOne, .op .add lgB lgB cOne] M) :=
    inv_runPrims (by simp [Prim.dst, lgD, lgA, lgB]) hM
  have r : ∀ i, i ≠ lgD → i ≠ lgA → i ≠ lgB →
      rd (runPrims [.op .xor lgD lgS lgJ, .op .add lgA lgA cOne, .op .add lgB lgB cOne] M) i =
        rd M i := fun i a b c =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b, Ne.symm c⟩) _
  rw [e]
  refine ⟨?_, ?_, ?_, fun i h1 h2 h3 h4 h5 => ?_, mulBC_inv _ _ _ (by decide) hI⟩
  · rw [mulBC_frame _ _ _ (by decide) (by decide)]
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgD]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hA, h1, add_one_toWord]
  · rw [mulBC_frame _ _ _ (by decide) (by decide)]
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgD]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hB, h1, add_one_toWord]
  · rw [rdB, mulBC_run hI (by decide) (by decide) (by decide) (by decide), mulBW_spec,
      r _ (by decide) (by decide) (by decide)]
    simp only [rdB, runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgD]; omega)) only
      [rd_set_self, rd_set_ne, eval_xor]
  · rw [mulBC_frame _ _ _ h5 h4, r _ h1 h2 h3]

/-- **The forward step**: `M[b] := P`, `P *= S ⊕ M[a]`, `lgA, lgB += 1`. -/
theorem fwdL_sem (I : Array Word) (s : St) (hM : Inv s.M) {a b : ℕ} (hA : rd s.M lgA = toWord a)
    (hB : rd s.M lgB = toWord b) (ha : a + 1 < 2 ^ 64) (hb : regs ≤ b) (hb2 : b + 1 < 2 ^ 64)
    (hbs : b < s.M.size) :
    rd (semXIR I fwdL s).M lgA = toWord (a + 1) ∧ rd (semXIR I fwdL s).M lgB = toWord (b + 1) ∧
    rd (semXIR I fwdL s).M b = rd s.M lgP ∧
    rdB (semXIR I fwdL s).M lgP = rdB s.M lgP * wB (rd s.M lgS ^^^ rd s.M a) ∧
    (∀ i, regs ≤ i → i ≠ b → rd (semXIR I fwdL s).M i = rd s.M i) ∧
    Inv (semXIR I fwdL s).M := by
  simp only [regs] at hb
  simp only [fwdL, semXIR_seq, semB]
  obtain ⟨l1, l1f⟩ := bload_sem I s hM (d := lgJ) (a := lgA) (x := a) (by decide) hA (by omega)
  have hM1 := inv_sem I (P := .load lgJ lgA) (by simp [WF, lgJ]) hM
  have z1 := size_sem I (.load lgJ lgA) s
  generalize semXIR I (.load lgJ lgA) s = s1 at l1 l1f hM1 z1 ⊢
  have a2 := fun i (hi : i ≠ cTmp) => st_rd I s1 hM1 ((l1f lgB (by decide)).trans hB)
    (by simp only [regs]; omega) (by omega) (by omega) (by decide) (by decide) (v := lgP) hi
  have hM2 := inv_sem I (P := .store lgB lgP) (s := s1) (by simp [WF, lgB, cTmp]) hM1
  generalize semXIR I (.store lgB lgP) s1 = s2 at a2 hM2 ⊢
  have r2 : ∀ i, i ≠ cTmp → i ≠ b → i ≠ lgJ → rd s2.M i = rd s.M i := fun i hT hb hJ => by
    rw [a2 i hT, if_neg hb, l1f i hJ]
  have hJ2 : rd s2.M lgJ = rd s.M a := by rw [a2 _ (by decide), if_neg (by simp only [lgJ]; omega), l1]
  obtain ⟨f1, f2, f3, f4, f5⟩ := fwd_blk s2.M hM2 (a := a) (b := b)
    (by rw [r2 _ (by decide) (by simp only [lgA]; omega) (by decide), hA])
    (by rw [r2 _ (by decide) (by simp only [lgB]; omega) (by decide), hB])
  refine ⟨f1, f2, ?_, ?_, fun i hi hib => ?_, f5⟩
  · rw [f4 _ (by simp only [lgD]; omega) (by simp only [lgA]; omega) (by simp only [lgB]; omega)
      (by simp only [lgP]; omega) (.inr (by omega)), a2 _ (by simp only [cTmp]; omega), if_pos rfl,
      l1f _ (by decide)]
  · rw [f3, hJ2, rdB, rdB, r2 _ (by decide) (by simp only [lgP]; omega) (by decide),
      r2 _ (by decide) (by simp only [lgS]; omega) (by decide)]
  · simp only [regs] at hi
    rw [f4 _ (by simp only [lgD]; omega) (by simp only [lgA]; omega) (by simp only [lgB]; omega)
      (by simp only [lgP]; omega) (.inr (by omega)),
      r2 _ (by simp only [cTmp]; omega) hib (by simp only [lgJ]; omega)]

theorem wf_fwdL : WF fwdL := by simp [fwdL, WF, mulBC, redC, Prim.dst, lgJ, lgB, cTmp, lgD, lgA, lgP]

theorem nw_fwdL {i : ℕ} (h1 : i ≠ lgJ) (h2 : i ≠ lgD) (h3 : i ≠ lgA) (h4 : i ≠ lgB) (h5 : i ≠ lgP)
    (h6 : i ≠ cTmp) (h7 : i < 5 ∨ 9 ≤ i) : ¬ Writes fwdL i := by
  intro h
  simp [fwdL, Writes, mulBC, redC, Prim.dst] at h
  simp only [lgJ, lgD, lgA, lgB, lgP, cTmp] at *
  omega

/-- **The forward pass**: from `P = 1`, `lgA = jb`, `lgB = pb`, the prefix products
`P_t = preP J s t` at `pb + t` for `t < k`; the heap outside `[pb, pb + k)` is kept. -/
theorem fwdLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb pb sv : ℕ} {Jl : List ℕ}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (hjp : jb + k ≤ pb) (hpb2 : pb + k + 1 < 2 ^ 64)
    (hps : pb + k ≤ s.M.size) (hA : rd s.M lgA = toWord jb) (hB : rd s.M lgB = toWord pb)
    (hN : rd s.M lgN2 = toWord k) (hP : rdB s.M lgP = 1) (hS : rd s.M lgS = toWord sv)
    (hJ : ∀ u < k, rd s.M (jb + u) = jw Jl u) :
    rd (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) s).M lgA = toWord (jb + k) ∧
    rd (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) s).M lgB = toWord (pb + k) ∧
    (∀ t < k, rdB (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) s).M (pb + t) = preP Jl sv t) ∧
    (∀ i, regs ≤ i → (i < pb ∨ pb + k ≤ i) →
      rd (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) s).M i = rd s.M i) ∧
    Inv (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) s).M := by
  simp only [regs] at hjb
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧
    rd st.M lgA = toWord (jb + j) ∧ rd st.M lgB = toWord (pb + j) ∧ rdB st.M lgP = preP Jl sv j ∧
    rd st.M lgS = toWord sv ∧ (∀ t < j, rdB st.M (pb + t) = preP Jl sv t) ∧
    (∀ i, regs ≤ i → (i < pb ∨ pb + j ≤ i) → rd st.M i = rd s.M i)
  have ef : ∀ i, i ≠ lgC2 → i ≠ cTmp → rd (entryK lgC2 lgN2 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I fwdL P s hM (by decide) (by decide) (by decide) hN hk
    ⟨inv_entryK hM (by decide), size_entryK .., by rw [ef _ (by decide) (by decide), hA]; rfl,
      by rw [ef _ (by decide) (by decide), hB]; rfl,
      by rw [rdB, ef _ (by decide) (by decide), ← rdB, hP]; rfl,
      by rw [ef _ (by decide) (by decide), hS], fun t ht => absurd ht (Nat.not_lt_zero _),
      fun i hi _ => ef i (by simp only [regs, lgC2] at hi ⊢; omega)
        (by simp only [regs, cTmp] at hi ⊢; omega)⟩ ?_
  · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, h.1⟩
  rintro j st hj ⟨hI, hz, hA', hB', hP', hS', hV, hH⟩
  obtain ⟨b1, b2, b3, b4, b5, hI2⟩ := fwdL_sem I st hI (a := jb + j) (b := pb + j) hA' hB'
    (by omega) (by simp only [regs]; omega) (by omega) (by omega)
  have hS2 : rd (semXIR I fwdL st).M lgS = toWord sv := by
    rw [frame I _ _ wf_fwdL hI _ (by decide) (nw_fwdL (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)), hS']
  have hd : ∀ i, regs ≤ i → rd (decS lgC2 (semXIR I fwdL st)).M i = rd (semXIR I fwdL st).M i :=
    fun i hi => rd_decS (by simp only [regs, lgC2] at hi ⊢; omega) _
  refine ⟨inv_decS hI2 (by decide), by rw [size_decS, size_sem, hz], ?_, ?_, ?_, ?_,
    fun t ht => ?_, fun i hi hi2 => ?_⟩
  · rw [rd_decS (by decide), b1]; exact congrArg toWord (by omega)
  · rw [rd_decS (by decide), b2]; exact congrArg toWord (by omega)
  · rw [rdB, rd_decS (by decide), ← rdB, b4, hP', hS', hH _ (by simp only [regs]; omega)
      (.inl (by omega)), hJ j hj, preP, preP, Finset.prod_range_succ]; rfl
  · rw [rd_decS (by decide), hS2]
  · rw [rdB, hd _ (by simp only [regs]; omega), ← rdB]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · rw [rdB, b5 _ (by simp only [regs]; omega) (by omega), ← rdB]; exact hV t ht
    · rw [rdB, b3, ← rdB, hP']
  · rw [hd i hi, b5 i hi (by omega), hH i hi (by omega)]

/-! ## The rows' accumulation -/

theorem rdF_mk (M : Mem) (a : ℕ) : rdF M a = ⟨wB (rd M a), wB (rd M (a + 1))⟩ := rfl

/-- **Row `c`'s step**: `acc_c += e · M[x]` (`F`, two words), `lgX += 2`. -/
theorem accRow_sem (I : Array Word) (s : St) (hM : Inv s.M) {c x : ℕ} (hc : c < 16)
    (hX : rd s.M lgX = toWord x) (hx : regs ≤ x) (hx2 : x + 2 < 2 ^ 64) :
    rd (semXIR I (accRow c) s).M lgX = toWord (x + 2) ∧
    rdF (semXIR I (accRow c) s).M (lgAc + 2 * c) =
      rdF s.M (lgAc + 2 * c) + F.smulBase (rdB s.M lgE) (rdF s.M x) ∧
    (∀ i, i ≠ lgX → i ≠ lgV → i ≠ lgV1 → i ≠ lgAc + 2 * c → i ≠ lgAc + 2 * c + 1 → (i < 5 ∨ 9 ≤ i) →
      rd (semXIR I (accRow c) s).M i = rd s.M i) ∧
    Inv (semXIR I (accRow c) s).M := by
  simp only [regs] at hx
  simp only [accRow, semXIR_seq, semB]
  obtain ⟨l1, l1f⟩ := bload_sem I s hM (d := lgV) (a := lgX) (x := x) (by decide) hX (by omega)
  have hM1 := inv_sem I (P := .load lgV lgX) (by simp [WF, lgV]) hM
  generalize semXIR I (.load lgV lgX) s = s1 at l1 l1f hM1 ⊢
  obtain ⟨i2, i2f⟩ := incr_sem s1.M hM1 (r := lgX) (x := x) (by decide) (by decide)
    ((l1f _ (by decide)).trans hX)
  have hM2 : Inv (runPrims [.op .add lgX lgX cOne] s1.M) := inv_runPrims (by simp [Prim.dst, lgX]) hM1
  generalize runPrims [.op .add lgX lgX cOne] s1.M = M2 at i2 i2f hM2 ⊢
  obtain ⟨l3, l3f⟩ := bload_sem I ⟨M2, s1.o⟩ hM2 (d := lgV1) (a := lgX) (x := x + 1) (by decide) i2
    (by omega)
  have hM3 := inv_sem I (P := .load lgV1 lgX) (s := ⟨M2, s1.o⟩) (by simp [WF, lgV1]) hM2
  generalize semXIR I (.load lgV1 lgX) ⟨M2, s1.o⟩ = s3 at l3 l3f hM3 ⊢
  have hX3 : rd s3.M lgX = toWord (x + 1) := (l3f _ (by decide)).trans i2
  have hb : ∀ i, i ≠ lgX → i ≠ lgV → i ≠ lgV1 → rd s3.M i = rd s.M i := fun i h1 h2 h3 =>
    (l3f _ h3).trans ((i2f _ h1).trans (l1f _ h2))
  obtain ⟨a1, a2, a3, a4⟩ := amm_run hM3 (r := lgX) (a := lgV) (b := lgV1) (q := lgE) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hX3
  have hM4 : Inv (runPrims ([.op .add lgX lgX cOne] ++ mulBC lgV lgV lgE ++ mulBC lgV1 lgV1 lgE) s3.M) := by
    rw [runPrims_append, runPrims_append]
    exact mulBC_inv _ _ _ (by decide) (mulBC_inv _ _ _ (by decide)
      (inv_runPrims (by simp [Prim.dst, lgX]) hM3))
  rw [runPrims_append]
  generalize runPrims ([.op .add lgX lgX cOne] ++ mulBC lgV lgV lgE ++ mulBC lgV1 lgV1 lgE) s3.M = M4
    at a1 a2 a3 a4 hM4 ⊢
  have hs4 : 256 ≤ M4.size := hM4.1
  have hA : lgAc + 2 * c + 1 < 256 := by simp only [lgAc]; omega
  have x1 : rd (runPrims [.op .xor (lgAc + 2 * c) (lgAc + 2 * c) lgV,
      .op .xor (lgAc + 2 * c + 1) (lgAc + 2 * c + 1) lgV1] M4) (lgAc + 2 * c) =
      rd M4 (lgAc + 2 * c) ^^^ rd M4 lgV := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    rw [rd_set_ne (by omega), rd_set_self (by omega), eval_xor]
  have x2 : rd (runPrims [.op .xor (lgAc + 2 * c) (lgAc + 2 * c) lgV,
      .op .xor (lgAc + 2 * c + 1) (lgAc + 2 * c + 1) lgV1] M4) (lgAc + 2 * c + 1) =
      rd M4 (lgAc + 2 * c + 1) ^^^ rd M4 lgV1 := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    rw [rd_set_self (by rw [size_set]; omega), eval_xor, rd_set_ne (by omega),
      rd_set_ne (by simp only [lgAc, lgV1]; omega)]
  have xf : ∀ i, i ≠ lgAc + 2 * c → i ≠ lgAc + 2 * c + 1 →
      rd (runPrims [.op .xor (lgAc + 2 * c) (lgAc + 2 * c) lgV,
        .op .xor (lgAc + 2 * c + 1) (lgAc + 2 * c + 1) lgV1] M4) i = rd M4 i := fun i h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hAc : ∀ e < 2, rd M4 (lgAc + 2 * c + e) = rd s.M (lgAc + 2 * c + e) := fun e he => by
    rw [a4 _ (by simp only [lgAc, lgX]; omega) (by simp only [lgAc, lgV]; omega)
      (by simp only [lgAc, lgV1]; omega) (.inr (by simp only [lgAc]; omega)),
      hb _ (by simp only [lgAc, lgX]; omega) (by simp only [lgAc, lgV]; omega)
        (by simp only [lgAc, lgV1]; omega)]
  have hE : rd s3.M lgE = rd s.M lgE := hb _ (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, fun i h1 h2 h3 h4 h5 h6 => ?_,
    inv_runPrims (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp only [Prim.dst, lgAc] <;> omega) hM4⟩
  · rw [xf _ (by simp only [lgAc, lgX]; omega) (by simp only [lgAc, lgX]; omega), a1]
  · rw [rdF_mk, rdF_mk, rdF_mk, x1, x2, a2, a3, hE, l3f _ (by decide), i2f _ (by decide), l1, l3,
      i2f _ (by simp only [lgX]; omega), l1f _ (by simp only [lgV]; omega),
      show lgAc + 2 * c = lgAc + 2 * c + 0 from rfl, hAc 0 (by omega), hAc 1 (by omega)]
    show F.mk _ _ = F.mk _ _
    rw [wB_xor, wB_xor, mulBW_spec, mulBW_spec]
    exact congrArg₂ F.mk (congrArg (_ + ·) (mul_comm _ _)) (congrArg (_ + ·) (mul_comm _ _))
  · rw [xf _ h4 h5, a4 _ h1 h2 h3 h6, hb _ h1 h2 h3]

theorem wf_accRow (c : ℕ) : WF (accRow c) := by
  simp [accRow, WF, mulBC, redC, Prim.dst, lgV, lgV1, lgX, lgAc]
  constructor <;> omega

/-- **The `C` rows**: `acc_c += e · M[x + 2c]` for `c < C` (`C ≤ 16`), `lgX += 2C`. -/
theorem accIR_sem (I : Array Word) : ∀ (C : ℕ) (s : St), Inv s.M → ∀ {x : ℕ}, C ≤ 16 →
    rd s.M lgX = toWord x → regs ≤ x → x + 2 * C + 2 < 2 ^ 64 →
    rd (semXIR I (accIR C) s).M lgX = toWord (x + 2 * C) ∧
    (∀ c < C, rdF (semXIR I (accIR C) s).M (lgAc + 2 * c) =
      rdF s.M (lgAc + 2 * c) + F.smulBase (rdB s.M lgE) (rdF s.M (x + 2 * c))) ∧
    (∀ i, i ≠ lgX → i ≠ lgV → i ≠ lgV1 → (i < lgAc ∨ lgAc + 2 * C ≤ i) → (i < 5 ∨ 9 ≤ i) →
      rd (semXIR I (accIR C) s).M i = rd s.M i) ∧
    Inv (semXIR I (accIR C) s).M
  | 0, s, hM, x, _, hX, _, _ => by
    have e : semXIR I (accIR 0) s = s := by rw [accIR, semB, runPrims_nil]
    rw [e]
    exact ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact hX, fun c hc => absurd hc (Nat.not_lt_zero _),
      fun _ _ _ _ _ _ => rfl, hM⟩
  | C + 1, s, hM, x, hC, hX, hx, hx2 => by
    obtain ⟨a1, a2, a3, hM1⟩ := accIR_sem I C s hM (by omega) hX hx (by omega)
    rw [accIR, semXIR_seq]
    generalize semXIR I (accIR C) s = s1 at a1 a2 a3 hM1 ⊢
    obtain ⟨b1, b2, b3, hM2⟩ := accRow_sem I s1 hM1 (c := C) (by omega) a1
      (by simp only [regs] at hx ⊢; omega) (by omega)
    have hH : ∀ i, regs ≤ i → rd s1.M i = rd s.M i := fun i hi => by
      simp only [regs] at hi
      exact a3 i (by simp only [lgX]; omega) (by simp only [lgV]; omega) (by simp only [lgV1]; omega)
        (.inr (by simp only [lgAc]; omega)) (.inr (by omega))
    have hE : rd s1.M lgE = rd s.M lgE := a3 _ (by decide) (by decide) (by decide) (.inl (by decide))
      (.inr (by decide))
    refine ⟨b1.trans (congrArg toWord (by omega)), fun c hc => ?_,
      fun i h1 h2 h3 h4 h5 => ?_, hM2⟩
    · have q0 : lgAc + 2 * c ≠ lgX ∧ lgAc + 2 * c ≠ lgV ∧ lgAc + 2 * c ≠ lgV1 ∧
          9 ≤ lgAc + 2 * c := by simp only [lgAc, lgX, lgV, lgV1]; omega
      have q1 : lgAc + 2 * c + 1 ≠ lgX ∧ lgAc + 2 * c + 1 ≠ lgV ∧ lgAc + 2 * c + 1 ≠ lgV1 ∧
          9 ≤ lgAc + 2 * c + 1 := by simp only [lgAc, lgX, lgV, lgV1]; omega
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · obtain ⟨u1, u2, u3, u4⟩ := q0
        obtain ⟨v1, v2, v3, v4⟩ := q1
        rw [rdF_eq (b3 (lgAc + 2 * c) u1 u2 u3 (by omega) (by omega) (.inr u4))
          (b3 (lgAc + 2 * c + 1) v1 v2 v3 (by omega) (by omega) (.inr v4))]
        exact a2 c hc
      · obtain ⟨u1, u2, u3, u4⟩ := q0
        obtain ⟨v1, v2, v3, v4⟩ := q1
        simp only [regs] at hx
        rw [b2, rdB, hE, ← rdB, rdF_eq (hH (x + 2 * c) (by simp only [regs]; omega))
          (hH (x + 2 * c + 1) (by simp only [regs]; omega)),
          rdF_eq (a3 (lgAc + 2 * c) u1 u2 u3 (.inr (by omega)) (.inr u4))
            (a3 (lgAc + 2 * c + 1) v1 v2 v3 (.inr (by omega)) (.inr v4))]
    · rw [b3 i h1 h2 h3 (by omega) (by omega) h5, a3 i h1 h2 h3 (by omega) h5]

/-! ## The backward pass -/

/-- The backward step's pointer block: `lgA, lgB −= 1`, `lgY −= 2C`, `lgX := lgY`. -/
theorem bwd_ptr (M : Mem) (hM : Inv M) {a b y C : ℕ} (hA : rd M lgA = toWord (a + 1))
    (hB : rd M lgB = toWord (b + 1)) (hY : rd M lgY = toWord (y + 2 * C)) (hK : rd M lgK = toWord (2 * C))
    (ha : a + 1 < 2 ^ 64) (hb : b + 1 < 2 ^ 64) (hy : y + 2 * C < 2 ^ 64) :
    let M' := runPrims [.op .sub lgA lgA cOne, .op .sub lgB lgB cOne, .op .sub lgY lgY lgK,
      .op .or lgX lgY lgY] M
    rd M' lgA = toWord a ∧ rd M' lgB = toWord b ∧ rd M' lgY = toWord y ∧ rd M' lgX = toWord y ∧
    (∀ i, i ≠ lgA → i ≠ lgB → i ≠ lgY → i ≠ lgX → rd M' i = rd M i) ∧ Inv M' := by
  intro M'
  have hs : 256 ≤ M.size := hM.1
  have h1 : rd M cOne = toWord 1 := hM.2 0 (by decide)
  have hy' : rd (runPrims [.op .sub lgA lgA cOne, .op .sub lgB lgB cOne, .op .sub lgY lgY lgK] M) lgY =
      toWord y := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgY]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hY, hK, sub_toWord hy (by omega), Nat.add_sub_cancel]
  have e := runPrims_append [.op .sub lgA lgA cOne, .op .sub lgB lgB cOne, .op .sub lgY lgY lgK]
    [.op .or lgX lgY lgY] M
  simp only [List.cons_append, List.nil_append] at e
  refine ⟨?_, ?_, ?_, ?_, fun i h1 h2 h3 h4 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4⟩) _,
    inv_runPrims (by simp [Prim.dst, lgA, lgB, lgY, lgX]) hM⟩
  · simp only [M', runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgY, lgX]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hA, h1, sub_toWord ha (by omega), Nat.add_sub_cancel]
  · simp only [M', runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgB, lgY, lgX]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hB, h1, sub_toWord hb (by omega), Nat.add_sub_cancel]
  · simp only [M', e]
    rw [rd_runPrims_of_not_writes (by simp [Prim.dst, lgX, lgY]), hy']
  · simp only [M', e]
    simp only [runPrims_cons (.op .or lgX lgY lgY), runPrims_nil, Prim.run]
    rw [rd_set_self (by simp only [size_runPrims, lgX]; omega), hy', or_self_eval]

/-- The backward step's products: `D := S ⊕ J`, `E *= Q`, `Q *= D`. -/
theorem bwd_mul (M : Mem) (hM : Inv M) :
    let M' := runPrims ([.op .xor lgD lgS lgJ] ++ mulBC lgE lgE lgQ ++ mulBC lgQ lgQ lgD) M
    rdB M' lgE = rdB M lgE * rdB M lgQ ∧ rdB M' lgQ = rdB M lgQ * wB (rd M lgS ^^^ rd M lgJ) ∧
    (∀ i, i ≠ lgD → i ≠ lgE → i ≠ lgQ → (i < 5 ∨ 9 ≤ i) → rd M' i = rd M i) ∧ Inv M' := by
  intro M'
  have hs : 256 ≤ M.size := hM.1
  have hI1 : Inv (runPrims [.op .xor lgD lgS lgJ] M) := inv_runPrims (by simp [Prim.dst, lgD]) hM
  have hI2 := mulBC_inv lgE lgE lgQ (by decide) hI1
  have d1 : rd (runPrims [.op .xor lgD lgS lgJ] M) lgD = rd M lgS ^^^ rd M lgJ := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    rw [rd_set_self (by simp only [lgD]; omega), eval_xor]
  have d1f : ∀ i, i ≠ lgD → rd (runPrims [.op .xor lgD lgS lgJ] M) i = rd M i := fun i h =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm h) _
  have e : M' = runPrims (mulBC lgQ lgQ lgD) (runPrims (mulBC lgE lgE lgQ)
      (runPrims [.op .xor lgD lgS lgJ] M)) := by simp only [M', runPrims_append]
  rw [e]
  refine ⟨?_, ?_, fun i h1 h2 h3 h4 => ?_, mulBC_inv _ _ _ (by decide) hI2⟩
  · rw [rdB, mulBC_frame _ _ _ (by decide) (by decide), mulBC_run hI1 (by decide) (by decide)
      (by decide) (by decide), mulBW_spec, d1f _ (by decide), d1f _ (by decide)]; rfl
  · rw [rdB, mulBC_run hI2 (by decide) (by decide) (by decide) (by decide), mulBW_spec,
      mulBC_frame _ _ _ (by decide) (by decide), mulBC_frame _ _ _ (by decide) (by decide), d1,
      d1f _ (by decide)]; rfl
  · rw [mulBC_frame _ _ _ h4 h3, mulBC_frame _ _ _ h4 h2, d1f _ h1]

/-- **The backward step** (`t` from `k − 1` down): `lgA, lgB −= 1`, `lgY −= 2C`;
`acc_c += (M[b] · Q) · M[y + 2c]`, `Q *= S ⊕ M[a]`. -/
theorem bwdL_sem (I : Array Word) (s : St) (hM : Inv s.M) {C a b y : ℕ} (hC : C ≤ 16)
    (hA : rd s.M lgA = toWord (a + 1)) (hB : rd s.M lgB = toWord (b + 1))
    (hY : rd s.M lgY = toWord (y + 2 * C)) (hK : rd s.M lgK = toWord (2 * C))
    (ha : a + 1 < 2 ^ 64) (hb : b + 1 < 2 ^ 64) (ha0 : regs ≤ a) (hb0 : regs ≤ b) (hy : regs ≤ y)
    (hy2 : y + 2 * C + 2 < 2 ^ 64) :
    rd (semXIR I (bwdL C) s).M lgA = toWord a ∧ rd (semXIR I (bwdL C) s).M lgB = toWord b ∧
    rd (semXIR I (bwdL C) s).M lgY = toWord y ∧
    rdB (semXIR I (bwdL C) s).M lgQ = rdB s.M lgQ * wB (rd s.M lgS ^^^ rd s.M a) ∧
    (∀ c < C, rdF (semXIR I (bwdL C) s).M (lgAc + 2 * c) =
      rdF s.M (lgAc + 2 * c) + F.smulBase (rdB s.M b * rdB s.M lgQ) (rdF s.M (y + 2 * c))) ∧
    rd (semXIR I (bwdL C) s).M lgS = rd s.M lgS ∧ rd (semXIR I (bwdL C) s).M lgK = rd s.M lgK ∧
    (∀ i, regs ≤ i → rd (semXIR I (bwdL C) s).M i = rd s.M i) ∧
    Inv (semXIR I (bwdL C) s).M := by
  simp only [regs] at hy ha0 hb0
  simp only [bwdL, semXIR_seq, semB]
  obtain ⟨p1, p2, p3, p4, pf, hM1⟩ := bwd_ptr s.M hM hA hB hY hK ha hb (by omega)
  generalize runPrims [.op .sub lgA lgA cOne, .op .sub lgB lgB cOne, .op .sub lgY lgY lgK,
      .op .or lgX lgY lgY] s.M = M1 at p1 p2 p3 p4 pf hM1 ⊢
  have hH1 : ∀ i, regs ≤ i → rd M1 i = rd s.M i := fun i hi => pf i
    (by simp only [regs, lgA] at hi ⊢; omega) (by simp only [regs, lgB] at hi ⊢; omega)
    (by simp only [regs, lgY] at hi ⊢; omega) (by simp only [regs, lgX] at hi ⊢; omega)
  obtain ⟨l2, l2f⟩ := bload_sem I ⟨M1, s.o⟩ hM1 (d := lgJ) (a := lgA) (x := a) (by decide) p1 (by omega)
  have hM2 := inv_sem I (P := .load lgJ lgA) (s := ⟨M1, s.o⟩) (by simp [WF, lgJ]) hM1
  generalize semXIR I (.load lgJ lgA) ⟨M1, s.o⟩ = s2 at l2 l2f hM2 ⊢
  obtain ⟨l3, l3f⟩ := bload_sem I s2 hM2 (d := lgE) (a := lgB) (x := b)
    (by decide) ((l2f _ (by decide)).trans p2) (by omega)
  have hM3 := inv_sem I (P := .load lgE lgB) (s := s2) (by simp [WF, lgE]) hM2
  generalize semXIR I (.load lgE lgB) s2 = s3 at l3 l3f hM3 ⊢
  have r3 : ∀ i, i ≠ lgJ → i ≠ lgE → rd s3.M i = rd M1 i := fun i h1 h2 => (l3f _ h2).trans (l2f _ h1)
  obtain ⟨m1, m2, mf, hM4⟩ := bwd_mul s3.M hM3
  generalize runPrims ([.op .xor lgD lgS lgJ] ++ mulBC lgE lgE lgQ ++ mulBC lgQ lgQ lgD) s3.M = M4
    at m1 m2 mf hM4 ⊢
  have r4 : ∀ i, i ≠ lgJ → i ≠ lgE → i ≠ lgD → i ≠ lgQ → (i < 5 ∨ 9 ≤ i) → rd M4 i = rd M1 i :=
    fun i h1 h2 h3 h4 h5 => (mf i h3 h2 h4 h5).trans (r3 i h1 h2)
  obtain ⟨a1, a2, a3, hM5⟩ := accIR_sem I C ⟨M4, s3.o⟩ hM4 hC
    ((r4 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans p4)
    (by simp only [regs]; omega) (by omega)
  have q5 : ∀ i, i ≠ lgX → i ≠ lgV → i ≠ lgV1 → (i < lgAc ∨ lgAc + 2 * C ≤ i) → (i < 5 ∨ 9 ≤ i) →
      i ≠ lgJ → i ≠ lgE → i ≠ lgD → i ≠ lgQ →
      rd (semXIR I (accIR C) ⟨M4, s3.o⟩).M i = rd M1 i := fun i h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    (a3 i h1 h2 h3 h4 h5).trans (r4 i h6 h7 h8 h9 h5)
  have hQ3 : rd s3.M lgQ = rd s.M lgQ := (r3 _ (by decide) (by decide)).trans
    (pf _ (by decide) (by decide) (by decide) (by decide))
  have hS3 : rd s3.M lgS = rd s.M lgS := (r3 _ (by decide) (by decide)).trans
    (pf _ (by decide) (by decide) (by decide) (by decide))
  have hE3 : rd s3.M lgE = rd s.M b := by rw [l3, l2f _ (by simp only [lgJ]; omega), hH1 b (by
    simp only [regs]; omega)]
  have hJ3 : rd s3.M lgJ = rd s.M a := by
    rw [l3f _ (by decide), l2, hH1 a (by simp only [regs]; omega)]
  refine ⟨?_, ?_, ?_, ?_, fun c hc => ?_, ?_, ?_, fun i hi => ?_, hM5⟩
  · rw [q5 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) (by decide)
      (by decide) (by decide) (by decide), p1]
  · rw [q5 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) (by decide)
      (by decide) (by decide) (by decide), p2]
  · rw [q5 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) (by decide)
      (by decide) (by decide) (by decide), p3]
  · rw [rdB, a3 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)), ← rdB, m2]
    unfold rdB
    rw [hQ3, hS3, hJ3]
  · rw [a2 c hc]
    have e1 : rdF M4 (lgAc + 2 * c) = rdF s.M (lgAc + 2 * c) := by
      have q0 : lgAc + 2 * c ≠ lgJ ∧ lgAc + 2 * c ≠ lgE ∧ lgAc + 2 * c ≠ lgD ∧ lgAc + 2 * c ≠ lgQ ∧
          lgAc + 2 * c + 1 ≠ lgJ ∧ lgAc + 2 * c + 1 ≠ lgE ∧ lgAc + 2 * c + 1 ≠ lgD ∧
          lgAc + 2 * c + 1 ≠ lgQ ∧ lgAc + 2 * c ≠ lgA ∧ lgAc + 2 * c ≠ lgB ∧ lgAc + 2 * c ≠ lgY ∧
          lgAc + 2 * c ≠ lgX ∧ lgAc + 2 * c + 1 ≠ lgA ∧ lgAc + 2 * c + 1 ≠ lgB ∧
          lgAc + 2 * c + 1 ≠ lgY ∧ lgAc + 2 * c + 1 ≠ lgX ∧ 9 ≤ lgAc + 2 * c := by
        simp only [lgAc, lgJ, lgE, lgD, lgQ, lgA, lgB, lgY, lgX]; omega
      obtain ⟨u1, u2, u3, u4, v1, v2, v3, v4, w1, w2, w3, w4, x1, x2, x3, x4, u5⟩ := q0
      exact rdF_eq ((r4 _ u1 u2 u3 u4 (.inr u5)).trans (pf _ w1 w2 w3 w4))
        ((r4 _ v1 v2 v3 v4 (.inr (by omega))).trans (pf _ x1 x2 x3 x4))
    have e2 : rdF M4 (y + 2 * c) = rdF s.M (y + 2 * c) := by
      refine rdF_eq ?_ ?_
      · rw [r4 _ (by simp only [lgJ]; omega) (by simp only [lgE]; omega) (by simp only [lgD]; omega)
          (by simp only [lgQ]; omega) (.inr (by omega)), hH1 _ (by simp only [regs]; omega)]
      · rw [r4 _ (by simp only [lgJ]; omega) (by simp only [lgE]; omega) (by simp only [lgD]; omega)
          (by simp only [lgQ]; omega) (.inr (by omega)), hH1 _ (by simp only [regs]; omega)]
    rw [e1, e2]
    show _ + F.smulBase (rdB M4 lgE) _ = _
    rw [m1]
    unfold rdB
    rw [hE3, hQ3]
  · rw [q5 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) (by decide)
      (by decide) (by decide) (by decide), pf _ (by decide) (by decide) (by decide) (by decide)]
  · rw [q5 _ (by decide) (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) (by decide)
      (by decide) (by decide) (by decide), pf _ (by decide) (by decide) (by decide) (by decide)]
  · simp only [regs] at hi
    rw [q5 i (by simp only [lgX]; omega) (by simp only [lgV]; omega) (by simp only [lgV1]; omega)
      (.inr (by simp only [lgAc]; omega)) (.inr (by omega)) (by simp only [lgJ]; omega)
      (by simp only [lgE]; omega) (by simp only [lgD]; omega) (by simp only [lgQ]; omega),
      hH1 i (by simp only [regs]; omega)]

theorem wf_bwdL (C : ℕ) : WF (bwdL C) := by
  simp only [bwdL, WF, wf_accIR C, and_true]
  simp [mulBC, redC, Prim.dst, lgA, lgB, lgY, lgX, lgJ, lgE, lgD, lgQ]

/-- **The backward pass**: from `lgA = jb + k`, `lgB = pb + k`, `lgY = yb + 2Ck`, `Q = 1` and zero
accumulators, `acc_c = Σ_{t<k} (M[pb + t] · Q_t) · Y_c[t]` with `Q_t = sufP J k s (t + 1)`. -/
theorem bwdLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k C jb pb yb sv : ℕ} {Jl : List ℕ}
    (hk : k < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb) (hpb : regs ≤ pb) (hyb : regs ≤ yb)
    (hjb2 : jb + k < 2 ^ 64) (hpb2 : pb + k < 2 ^ 64) (hy2 : yb + 2 * C * k + 2 < 2 ^ 64)
    (hA : rd s.M lgA = toWord (jb + k)) (hB : rd s.M lgB = toWord (pb + k))
    (hY : rd s.M lgY = toWord (yb + 2 * C * k)) (hK : rd s.M lgK = toWord (2 * C))
    (hN : rd s.M lgN2 = toWord k) (hQ : rdB s.M lgQ = 1) (hS : rd s.M lgS = toWord sv)
    (h0 : ∀ c < C, rdF s.M (lgAc + 2 * c) = 0) (hJ : ∀ u < k, rd s.M (jb + u) = jw Jl u) :
    (∀ c < C, rdF (semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) s).M (lgAc + 2 * c) =
      ∑ t ∈ range k, F.smulBase (rdB s.M (pb + t) * sufP Jl k sv (t + 1))
        (rdF s.M (yb + 2 * (C * t + c)))) ∧
    (∀ i, regs ≤ i → rd (semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) s).M := by
  simp only [regs] at hjb hpb hyb
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧
    rd st.M lgA = toWord (jb + (k - j)) ∧ rd st.M lgB = toWord (pb + (k - j)) ∧
    rd st.M lgY = toWord (yb + 2 * C * (k - j)) ∧ rd st.M lgK = toWord (2 * C) ∧
    rd st.M lgS = toWord sv ∧ rdB st.M lgQ = sufP Jl k sv (k - j) ∧
    (∀ c < C, rdF st.M (lgAc + 2 * c) = ∑ t ∈ Ico (k - j) k,
      F.smulBase (rdB s.M (pb + t) * sufP Jl k sv (t + 1)) (rdF s.M (yb + 2 * (C * t + c)))) ∧
    (∀ i, regs ≤ i → rd st.M i = rd s.M i)
  have ef : ∀ i, i ≠ lgC2 → i ≠ cTmp → rd (entryK lgC2 lgN2 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (bwdL C) P s hM (by decide) (by decide) (by decide) hN hk
    ⟨inv_entryK hM (by decide), by rw [ef _ (by decide) (by decide), hA, Nat.sub_zero],
      by rw [ef _ (by decide) (by decide), hB, Nat.sub_zero],
      by rw [ef _ (by decide) (by decide), hY, Nat.sub_zero],
      by rw [ef _ (by decide) (by decide), hK], by rw [ef _ (by decide) (by decide), hS],
      by rw [rdB, ef _ (by decide) (by decide), ← rdB, hQ, Nat.sub_zero, sufP, Finset.Ico_self,
        Finset.prod_empty],
      fun c hc => by
        have q : lgAc + 2 * c ≠ lgC2 ∧ lgAc + 2 * c ≠ cTmp ∧ lgAc + 2 * c + 1 ≠ lgC2 ∧
            lgAc + 2 * c + 1 ≠ cTmp := by simp only [lgAc, lgC2, cTmp]; omega
        rw [rdF_eq (ef _ q.1 q.2.1) (ef _ q.2.2.1 q.2.2.2), h0 c hc, Nat.sub_zero, Finset.Ico_self,
          Finset.sum_empty],
      fun i hi => ef i (by simp only [regs, lgC2] at hi ⊢; omega)
        (by simp only [regs, cTmp] at hi ⊢; omega)⟩ ?_
  · refine ⟨fun c hc => ?_, h.2.2.2.2.2.2.2.2, h.1⟩
    rw [h.2.2.2.2.2.2.2.1 c hc, Nat.sub_self, ← Finset.range_eq_Ico]
  rintro j st hj ⟨hI, hA', hB', hY', hK', hS', hQ', hV, hH⟩
  obtain ⟨t, ht⟩ : ∃ t, k - j = t + 1 := ⟨k - j - 1, by omega⟩
  rw [ht] at hA' hB' hY' hQ' hV
  have htk : t < k := by omega
  have e1 : k - (j + 1) = t := by omega
  dsimp only [P]
  rw [e1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hI2⟩ := bwdL_sem I st hI (C := C) (a := jb + t) (b := pb + t)
    (y := yb + 2 * C * t) hC hA' hB' (hY'.trans (congrArg toWord (by ring))) hK' (by omega)
    (by omega) (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
    (by have : 2 * C * t + 2 * C ≤ 2 * C * k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ htk
        omega)
  have hd : ∀ i, i ≠ lgC2 → rd (decS lgC2 (semXIR I (bwdL C) st)).M i = rd (semXIR I (bwdL C) st).M i :=
    fun i hi => rd_decS (Ne.symm hi) _
  refine ⟨inv_decS hI2 (by decide), by rw [hd _ (by decide), b1], by rw [hd _ (by decide), b2],
    by rw [hd _ (by decide), b3], by rw [hd _ (by decide), b7, hK'],
    by rw [hd _ (by decide), b6, hS'], ?_, fun c hc => ?_, fun i hi => ?_⟩
  · rw [rdB, hd _ (by decide), ← rdB, b4, hQ', hS', hH _ (by simp only [regs]; omega), hJ t htk, sufP,
      sufP, Finset.prod_eq_prod_Ico_succ_bot htk, mul_comm]; rfl
  · have q : lgAc + 2 * c ≠ lgC2 ∧ lgAc + 2 * c + 1 ≠ lgC2 := by simp only [lgAc, lgC2]; omega
    rw [rdF_eq (hd _ q.1) (hd _ q.2), b5 c (by omega), hV c hc, Finset.sum_eq_sum_Ico_succ_bot htk,
      add_comm, rdF_eq (hH _ (by simp only [regs]; omega)) (hH _ (by simp only [regs]; omega)), hQ',
      show yb + 2 * C * t + 2 * c = yb + 2 * (C * t + c) by ring,
      rdB, hH _ (by simp only [regs]; omega), ← rdB]
  · rw [hd _ (by simp only [regs, lgC2] at hi ⊢; omega), b8 i hi, hH i hi]

/-! ## The outputs -/

/-- **Row `c`'s output**: `M[o], M[o + 1] := acc_c`, `lgO += 2k`. -/
theorem stRow_sem (I : Array Word) (s : St) (hM : Inv s.M) {c o k : ℕ} (hc : c < 16)
    (hO : rd s.M lgO = toWord o) (hK : rd s.M lgK = toWord (2 * k)) (ho : regs ≤ o)
    (ho2 : o + 2 * k + 2 < 2 ^ 64) (hos : o + 1 < s.M.size) :
    rd (semXIR I (stRow c) s).M lgO = toWord (o + 2 * k) ∧
    rd (semXIR I (stRow c) s).M o = rd s.M (lgAc + 2 * c) ∧
    rd (semXIR I (stRow c) s).M (o + 1) = rd s.M (lgAc + 2 * c + 1) ∧
    (∀ i, i ≠ lgO → i ≠ cTmp → i ≠ o → i ≠ o + 1 → rd (semXIR I (stRow c) s).M i = rd s.M i) ∧
    Inv (semXIR I (stRow c) s).M := by
  simp only [regs] at ho
  have hA : lgAc + 2 * c + 1 < 256 := by simp only [lgAc]; omega
  simp only [stRow, semXIR_seq, semB]
  have a1 := fun i (hi : i ≠ cTmp) => st_rd I s hM hO (by simp only [regs]; omega) (by omega)
    (by omega) (by decide) (by simp only [lgAc, cTmp]; omega) (v := lgAc + 2 * c) hi
  have hM1 := inv_sem I (P := .store lgO (lgAc + 2 * c)) (by simp [WF, lgO, cTmp]) hM
  have z1 := size_sem I (.store lgO (lgAc + 2 * c)) s
  generalize semXIR I (.store lgO (lgAc + 2 * c)) s = s1 at a1 hM1 z1 ⊢
  obtain ⟨i2, i2f⟩ := incr_sem s1.M hM1 (r := lgO) (x := o) (by decide) (by decide)
    ((a1 _ (by decide)).trans (by rw [if_neg (by simp only [lgO]; omega), hO]))
  have hM2 : Inv (runPrims [.op .add lgO lgO cOne] s1.M) := inv_runPrims (by simp [Prim.dst, lgO]) hM1
  have z2 := size_runPrims [.op .add lgO lgO cOne] s1.M
  generalize runPrims [.op .add lgO lgO cOne] s1.M = M2 at i2 i2f hM2 z2 ⊢
  have a3 := fun i (hi : i ≠ cTmp) => st_rd I ⟨M2, s1.o⟩ hM2 i2 (by simp only [regs]; omega)
    (by omega) (by show o + 1 < M2.size; omega) (by decide) (by simp only [lgAc, cTmp]; omega)
    (v := lgAc + 2 * c + 1) hi
  have hM3 := inv_sem I (P := .store lgO (lgAc + 2 * c + 1)) (s := ⟨M2, s1.o⟩) (by simp [WF, lgO, cTmp]) hM2
  generalize semXIR I (.store lgO (lgAc + 2 * c + 1)) ⟨M2, s1.o⟩ = s3 at a3 hM3 ⊢
  have hs3 : 256 ≤ s3.M.size := hM3.1
  have hO3 : rd s3.M lgO = toWord (o + 1) := by rw [a3 _ (by decide), if_neg (by simp only [lgO]; omega), i2]
  have hK3 : rd s3.M lgK = toWord (2 * k) := by
    rw [a3 _ (by decide), if_neg (by simp only [lgK]; omega), i2f _ (by decide), a1 _ (by decide),
      if_neg (by simp only [lgK]; omega), hK]
  have h1 : rd s3.M cOne = toWord 1 := hM3.2 0 (by decide)
  have hf : ∀ i, i ≠ lgO → rd (runPrims [.op .sub lgO lgO cOne, .op .add lgO lgO lgK] s3.M) i = rd s3.M i :=
    fun i h => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm h) _
  refine ⟨?_, ?_, ?_, fun i h1 h2 h3 h4 => ?_, inv_runPrims (by simp [Prim.dst, lgO]) hM3⟩
  · simp only [runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgO]; omega)) only [rd_set_self, rd_set_ne]
    rw [hO3, h1, sub_toWord (by omega) (by omega), Nat.add_sub_cancel, hK3, add_toWord]
  · rw [hf _ (by simp only [lgO]; omega), a3 _ (by simp only [cTmp]; omega), if_neg (by omega),
      i2f _ (by simp only [lgO]; omega), a1 _ (by simp only [cTmp]; omega), if_pos rfl]
  · rw [hf _ (by simp only [lgO]; omega), a3 _ (by simp only [cTmp]; omega), if_pos rfl,
      i2f _ (by simp only [lgO, lgAc]; omega), a1 _ (by simp only [lgAc, cTmp]; omega),
      if_neg (by simp only [lgAc]; omega)]
  · rw [hf _ h1, a3 _ h2, if_neg h4, i2f _ h1, a1 _ h2, if_neg h3]

theorem wf_stRow (c : ℕ) : WF (stRow c) := by simp [stRow, WF, Prim.dst, lgO, cTmp]

/-- **The `C` outputs**: row `c`'s accumulator at `o + 2kc` (`k ≥ 1`, `C ≤ 16`), `lgO += 2kC`;
the heap outside those cells is kept. -/
theorem stAcc_sem (I : Array Word) : ∀ (C : ℕ) (s : St), Inv s.M → ∀ {o k : ℕ}, C ≤ 16 → 1 ≤ k →
    rd s.M lgO = toWord o → rd s.M lgK = toWord (2 * k) → regs ≤ o → o + 2 * k * C + 2 < 2 ^ 64 →
    o + 2 * k * C ≤ s.M.size →
    rd (semXIR I (stAcc C) s).M lgO = toWord (o + 2 * k * C) ∧
    (∀ c < C, rd (semXIR I (stAcc C) s).M (o + 2 * k * c) = rd s.M (lgAc + 2 * c) ∧
      rd (semXIR I (stAcc C) s).M (o + 2 * k * c + 1) = rd s.M (lgAc + 2 * c + 1)) ∧
    (∀ i, regs ≤ i → (∀ c < C, i ≠ o + 2 * k * c ∧ i ≠ o + 2 * k * c + 1) →
      rd (semXIR I (stAcc C) s).M i = rd s.M i) ∧
    Inv (semXIR I (stAcc C) s).M
  | 0, s, hM, o, k, _, _, hO, _, _, _, _ => by
    have e : semXIR I (stAcc 0) s = s := by rw [stAcc, semB, runPrims_nil]
    rw [e]
    exact ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact hO, fun c hc => absurd hc (Nat.not_lt_zero _),
      fun _ _ _ => rfl, hM⟩
  | C + 1, s, hM, o, k, hC, hk, hO, hK, ho, ho2, hos => by
    have hkC : 2 * k * (C + 1) = 2 * k * C + 2 * k := Nat.mul_succ _ _
    obtain ⟨a1, a2, a3, hM1⟩ := stAcc_sem I C s hM (by omega) hk hO hK ho (by omega) (by omega)
    rw [stAcc, semXIR_seq]
    have r1 : ∀ i, i < regs → i ≠ lgO → i ≠ cTmp → rd (semXIR I (stAcc C) s).M i = rd s.M i :=
      fun i hi h1 h2 => frame I _ s ((wf_stAcc C).2 trivial) hM i hi
        (fun h => (nw_stAcc i h2 h1 C).1 h)
    have z1 := size_sem I (stAcc C) s
    generalize semXIR I (stAcc C) s = s1 at a1 a2 a3 hM1 r1 z1 ⊢
    obtain ⟨b1, b2, b3, b4, hM2⟩ := stRow_sem I s1 hM1 (c := C) (o := o + 2 * k * C) (k := k)
      (by omega) a1 ((r1 _ (by decide) (by decide) (by decide)).trans hK) (by simp only [regs] at ho ⊢; omega)
      (by omega) (by omega)
    have q : ∀ c < C + 1, lgAc + 2 * c ≠ lgO ∧ lgAc + 2 * c ≠ cTmp ∧ lgAc + 2 * c + 1 ≠ lgO ∧
        lgAc + 2 * c + 1 ≠ cTmp ∧ lgAc + 2 * c + 1 < regs := fun c hc => by
      simp only [lgAc, lgO, cTmp, regs]; omega
    simp only [regs] at ho
    refine ⟨b1.trans (congrArg toWord (by rw [Nat.mul_succ]; omega)), fun c hc => ?_,
      fun i hi hne => ?_, hM2⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc' | rfl
      · have hlt : 2 * k * c + 2 ≤ 2 * k * C := by
          have := Nat.mul_le_mul_left (2 * k) (show c + 1 ≤ C by omega); rw [Nat.mul_succ] at this; omega
        rw [b4 _ (by simp only [lgO]; omega) (by simp only [cTmp]; omega) (by omega) (by omega),
          b4 _ (by simp only [lgO]; omega) (by simp only [cTmp]; omega) (by omega) (by omega)]
        exact a2 c hc'
      · obtain ⟨q1, q2, q3, q4, q5⟩ := q c hc
        rw [b2, b3, r1 _ (by omega) q1 q2, r1 _ q5 q3 q4]; exact ⟨rfl, rfl⟩
    · obtain ⟨n1, n2⟩ := hne C (by omega)
      rw [b4 i (by simp only [regs, lgO] at hi ⊢; omega) (by simp only [regs, cTmp] at hi ⊢; omega) n1 n2,
        a3 i hi fun c hc => hne c (by omega)]

/-! ## One target -/

theorem rd_zeros (M : Mem) (hs : regs ≤ M.size) : ∀ (n i : ℕ), lgAc + n ≤ regs →
    rd (runPrims ((List.range n).map fun j => .const (lgAc + j) 0) M) i =
      if lgAc ≤ i ∧ i < lgAc + n then 0 else rd M i
  | 0, i, _ => by simp [runPrims]
  | n + 1, i, hn => by
    rw [List.range_succ, List.map_append, runPrims_append]
    simp only [List.map_cons, List.map_nil, runPrims_cons, runPrims_nil, Prim.run, rd_set, size_runPrims]
    rw [rd_zeros M hs n i (by omega)]
    by_cases h : lgAc + n = i
    · rw [if_pos ⟨h, by simp only [regs] at hs hn; omega⟩, if_pos (by omega)]
    · rw [if_neg (fun e => h e.1)]
      by_cases h2 : lgAc ≤ i ∧ i < lgAc + n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem wf_fwdLoop (k : ℕ) : WF (.loopK lgC2 lgN2 (toWord k) fwdL) :=
  ⟨⟨by decide, by decide, by decide⟩, by decide, by
    simp [fwdL, Writes, mulBC, redC, Prim.dst, lgJ, lgD, lgA, lgB, lgP, lgC2, cTmp], wf_fwdL⟩

theorem wf_bwdLoop (k C : ℕ) : WF (.loopK lgC2 lgN2 (toWord k) (bwdL C)) :=
  ⟨⟨by decide, by decide, by decide⟩, by decide, by
    simp [bwdL, Writes, mulBC, redC, Prim.dst, lgJ, lgD, lgA, lgB, lgY, lgX, lgE, lgQ, lgC2,
      nw_accIR 177 (by decide) (by decide) (by decide) (by decide) (by decide)], wf_bwdL C⟩

/-- Registers `lgS` (174), `lgK` (173) and `lgC1`, `lgN1` (175, 176) survive the backward pass. -/
theorem nw_bwdLoop (k C : ℕ) {i : ℕ} (h1 : 173 ≤ i) (h2 : i ≤ 176) :
    ¬ Writes (.loopK lgC2 lgN2 (toWord k) (bwdL C)) i := by
  have := nw_accIR i (by omega) (by simp only [lgAc]; omega) (by simp only [lgV]; omega)
    (by simp only [lgV1]; omega) (by simp only [lgX]; omega) C
  intro h
  simp [Writes, bwdL, mulBC, redC, Prim.dst, this] at h
  simp only [lgJ, lgD, lgA, lgB, lgY, lgX, lgE, lgQ, lgC2, cTmp] at h
  omega

theorem nw_fwdLoop (k : ℕ) {i : ℕ} (h1 : 173 ≤ i) (h2 : i ≤ 176) :
    ¬ Writes (.loopK lgC2 lgN2 (toWord k) fwdL) i := by
  intro h
  simp [Writes, fwdL, mulBC, redC, Prim.dst] at h
  simp only [lgJ, lgD, lgA, lgB, lgP, lgC2, cTmp] at h
  omega

/-- **One target `s`**: output row `c` at `ob + 2s + 2kc` is
`Σ_{t<k} (P_t · Q_t) · Y_c[t]`; `lgS += 1`; the heap outside the prefix table and these outputs is
kept. -/
theorem tgBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {k C jb pb yb ob sv : ℕ} {Jl : List ℕ}
    (hk1 : 1 ≤ k) (hk : k < 2 ^ 64) (hC : C ≤ 16) (hsv : sv < k) (hjb : regs ≤ jb)
    (hjp : jb + k ≤ pb) (hpy : pb + k ≤ yb) (hyo : yb + 2 * C * k ≤ ob)
    (hos : ob + 2 * k * (C + 1) ≤ s.M.size) (ho2 : ob + 2 * k * (C + 1) + 2 < 2 ^ 64)
    (hS : rd s.M lgS = toWord sv) (hJ : ∀ u < k, rd s.M (jb + u) = jw Jl u) :
    (∀ c < C, rdF (semXIR I (tgBody k C jb pb yb ob) s).M (ob + 2 * sv + 2 * k * c) =
      ∑ t ∈ range k, F.smulBase (preP Jl sv t * sufP Jl k sv (t + 1))
        (rdF s.M (yb + 2 * (C * t + c)))) ∧
    rd (semXIR I (tgBody k C jb pb yb ob) s).M lgS = toWord (sv + 1) ∧
    (∀ i, regs ≤ i → (i < pb ∨ pb + k ≤ i) →
      (∀ c < C, i ≠ ob + 2 * sv + 2 * k * c ∧ i ≠ ob + 2 * sv + 2 * k * c + 1) →
      rd (semXIR I (tgBody k C jb pb yb ob) s).M i = rd s.M i) ∧
    Inv (semXIR I (tgBody k C jb pb yb ob) s).M := by
  have hs : 256 ≤ s.M.size := hM.1
  have hkC : 2 * k * (C + 1) = 2 * k * C + 2 * k := Nat.mul_succ _ _
  have hCk : 2 * C * k = 2 * k * C := by ring
  simp only [regs] at hjb
  simp only [tgBody, semXIR_seq, semB]
  -- the pointers of the forward pass
  have c1 : rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
        .const lgN2 (toWord k)] s.M) lgP = 1 ∧
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
        .const lgN2 (toWord k)] s.M) lgA = toWord jb ∧
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
        .const lgN2 (toWord k)] s.M) lgB = toWord pb ∧
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
        .const lgN2 (toWord k)] s.M) lgN2 = toWord k := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, lgP, lgA, lgB, lgN2]; omega)) only
      [rd_set_self, rd_set_ne]
  have c1f : ∀ i, i ≠ lgP → i ≠ lgA → i ≠ lgB → i ≠ lgN2 →
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
        .const lgN2 (toWord k)] s.M) i = rd s.M i := fun i a b c d =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d⟩) _
  have hM1 : Inv (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
      .const lgN2 (toWord k)] s.M) := inv_runPrims (by simp [Prim.dst, lgP, lgA, lgB, lgN2]) hM
  have z1 := size_runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
      .const lgN2 (toWord k)] s.M
  generalize runPrims [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb),
      .const lgN2 (toWord k)] s.M = M1 at c1 c1f hM1 z1 ⊢
  have H1 : ∀ i, regs ≤ i → rd M1 i = rd s.M i := fun i hi => by
    simp only [regs] at hi
    exact c1f i (by simp only [lgP]; omega) (by simp only [lgA]; omega) (by simp only [lgB]; omega)
      (by simp only [lgN2]; omega)
  -- the forward pass
  have hP1 : rdB M1 lgP = 1 := by rw [rdB, c1.1]; rfl
  have hS1 : rd M1 lgS = toWord sv := by rw [c1f _ (by decide) (by decide) (by decide) (by decide)]; exact hS
  have hJ1 : ∀ u < k, rd M1 (jb + u) = jw Jl u := fun u hu => by
    rw [H1 _ (by simp only [regs]; omega)]; exact hJ u hu
  obtain ⟨f1, f2, f3, f4, hM2⟩ := fwdLoop_sem I ⟨M1, s.o⟩ hM1 (Jl := Jl) (sv := sv) hk
    (by simp only [regs]; omega) hjp (by omega) (by show _ ≤ M1.size; omega) c1.2.1 c1.2.2.1 c1.2.2.2
    hP1 hS1 hJ1
  have r2 : ∀ i, 173 ≤ i → i ≤ 176 →
      rd (semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) ⟨M1, s.o⟩).M i = rd M1 i := fun i h1 h2 =>
    frame I _ _ (wf_fwdLoop k) hM1 i (by simp only [regs]; omega) (nw_fwdLoop k h1 h2)
  have z2 := size_sem I (.loopK lgC2 lgN2 (toWord k) fwdL) ⟨M1, s.o⟩
  dsimp only at f1 f2 f3 f4 z2
  generalize semXIR I (.loopK lgC2 lgN2 (toWord k) fwdL) ⟨M1, s.o⟩ = s2 at f1 f2 f3 f4 hM2 r2 z2 ⊢
  -- the constants and the zero accumulators
  have hs2 : 256 ≤ s2.M.size := hM2.1
  have c3 : rdB (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
        .const lgN2 (toWord k)] ++ zeroPs C) s2.M) lgQ = 1 ∧
      rd (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
        .const lgN2 (toWord k)] ++ zeroPs C) s2.M) lgY = toWord (yb + 2 * C * k) ∧
      rd (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
        .const lgN2 (toWord k)] ++ zeroPs C) s2.M) lgK = toWord (2 * C) ∧
      rd (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
        .const lgN2 (toWord k)] ++ zeroPs C) s2.M) lgN2 = toWord k ∧
      (∀ c < C, rdF (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)),
        .const lgK (toWord (2 * C)), .const lgN2 (toWord k)] ++ zeroPs C) s2.M) (lgAc + 2 * c) = 0) ∧
      (∀ i, i ≠ lgQ → i ≠ lgY → i ≠ lgK → i ≠ lgN2 → (i < lgAc ∨ lgAc + 2 * C ≤ i) →
        rd (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
          .const lgN2 (toWord k)] ++ zeroPs C) s2.M) i = rd s2.M i) := by
    rw [runPrims_append]
    have hz := rd_zeros (runPrims [.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)),
      .const lgK (toWord (2 * C)), .const lgN2 (toWord k)] s2.M) (by simp only [size_runPrims, regs]; omega)
      (2 * C)
    have hf : ∀ i, i ≠ lgQ → i ≠ lgY → i ≠ lgK → i ≠ lgN2 → rd (runPrims [.const lgQ 1,
        .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)), .const lgN2 (toWord k)]
        s2.M) i = rd s2.M i := fun i a b c d =>
      rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d⟩) _
    have hA : lgAc + 2 * C ≤ regs := by simp only [lgAc, regs]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rdB, zeroPs, hz _ hA, if_neg (by simp only [lgQ, lgAc]; omega)]
      simp only [runPrims_cons, runPrims_nil, Prim.run]
      simp (disch := first | decide | (simp only [size_set, lgQ, lgY, lgK, lgN2]; omega)) only
        [rd_set_self, rd_set_ne]
      rfl
    · rw [zeroPs, hz _ hA, if_neg (by simp only [lgY, lgAc]; omega)]
      simp only [runPrims_cons, runPrims_nil, Prim.run]
      simp (disch := first | decide | (simp only [size_set, lgQ, lgY, lgK, lgN2]; omega)) only
        [rd_set_self, rd_set_ne]
    · rw [zeroPs, hz _ hA, if_neg (by simp only [lgK, lgAc]; omega)]
      simp only [runPrims_cons, runPrims_nil, Prim.run]
      simp (disch := first | decide | (simp only [size_set, lgQ, lgY, lgK, lgN2]; omega)) only
        [rd_set_self, rd_set_ne]
    · rw [zeroPs, hz _ hA, if_neg (by simp only [lgN2, lgAc]; omega)]
      simp only [runPrims_cons, runPrims_nil, Prim.run]
      simp (disch := first | decide | (simp only [size_set, lgQ, lgY, lgK, lgN2]; omega)) only
        [rd_set_self]
    · intro c hc
      rw [rdF_mk, zeroPs, hz _ hA, hz _ hA, if_pos (by omega), if_pos (by omega)]; rfl
    · intro i h1 h2 h3 h4 h5
      rw [zeroPs, hz _ hA, if_neg (by omega), hf i h1 h2 h3 h4]
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := c3
  have hM3 : Inv (runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)),
      .const lgK (toWord (2 * C)), .const lgN2 (toWord k)] ++ zeroPs C) s2.M) := by
    refine inv_runPrims (fun p hp => ?_) hM2
    simp only [zeroPs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
      or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl) | ⟨j, -, rfl⟩ <;> simp only [Prim.dst, lgQ, lgY, lgK, lgN2, lgAc] <;>
      omega
  have z3 := size_runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)),
      .const lgK (toWord (2 * C)), .const lgN2 (toWord k)] ++ zeroPs C) s2.M
  generalize runPrims ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
      .const lgN2 (toWord k)] ++ zeroPs C) s2.M = M3 at d1 d2 d3 d4 d5 d6 hM3 z3 ⊢
  have H3 : ∀ i, regs ≤ i → rd M3 i = rd s2.M i := fun i hi => by
    simp only [regs] at hi
    exact d6 i (by simp only [lgQ]; omega) (by simp only [lgY]; omega) (by simp only [lgK]; omega)
      (by simp only [lgN2]; omega) (.inr (by simp only [lgAc]; omega))
  have hS3 : rd M3 lgS = toWord sv := by
    rw [d6 _ (by decide) (by decide) (by decide) (by decide) (.inl (by decide)), r2 _ (by decide) (by decide),
      c1f _ (by decide) (by decide) (by decide) (by decide), hS]
  -- the backward pass
  obtain ⟨g1, g2, hM4⟩ := bwdLoop_sem I ⟨M3, s2.o⟩ hM3 (Jl := Jl) (sv := sv) (jb := jb) (pb := pb)
    (yb := yb) hk hC (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
    (by omega) (by omega) (by omega)
    (by rw [d6 _ (by decide) (by decide) (by decide) (by decide) (.inl (by decide))]; exact f1)
    (by rw [d6 _ (by decide) (by decide) (by decide) (by decide) (.inl (by decide))]; exact f2)
    d2 d3 d4 d1 hS3 d5
    (fun u hu => by
      show rd M3 _ = _
      rw [H3 _ (by simp only [regs]; omega), f4 _ (by simp only [regs]; omega) (.inl (by omega)),
        H1 _ (by simp only [regs]; omega), hJ u hu])
  have r4 : ∀ i, 173 ≤ i → i ≤ 176 →
      rd (semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) ⟨M3, s2.o⟩).M i = rd M3 i := fun i h1 h2 =>
    frame I _ _ (wf_bwdLoop k C) hM3 i (by simp only [regs]; omega) (nw_bwdLoop k C h1 h2)
  have z4 : (semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) ⟨M3, s2.o⟩).M.size = M3.size :=
    size_sem ..
  dsimp only at g1 g2
  generalize semXIR I (.loopK lgC2 lgN2 (toWord k) (bwdL C)) ⟨M3, s2.o⟩ = s4 at g1 g2 hM4 r4 z4 ⊢
  have hS4 : rd s4.M lgS = toWord sv := (r4 _ (by decide) (by decide)).trans hS3
  -- the output pointer
  have hs4 : 256 ≤ s4.M.size := hM4.1
  have c5 : rd (runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
        .op .add lgO lgO lgS] s4.M) lgO = toWord (ob + 2 * sv) ∧
      rd (runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
        .op .add lgO lgO lgS] s4.M) lgK = toWord (2 * k) := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, lgK, lgO, lgS]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hS4, add_toWord, add_toWord]; exact congrArg toWord (by omega)
  have c5f : ∀ i, i ≠ lgK → i ≠ lgO → rd (runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob),
      .op .add lgO lgO lgS, .op .add lgO lgO lgS] s4.M) i = rd s4.M i := fun i a b =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b⟩) _
  have hM5 : Inv (runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
      .op .add lgO lgO lgS] s4.M) := inv_runPrims (by simp [Prim.dst, lgK, lgO]) hM4
  have z5 := size_runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
      .op .add lgO lgO lgS] s4.M
  generalize runPrims [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
      .op .add lgO lgO lgS] s4.M = M5 at c5 c5f hM5 z5 ⊢
  have sz : s.M.size = M5.size := by
    rw [z5, z4, z3, z2, z1]
  -- the outputs
  have hsv2 : 2 * sv + 2 ≤ 2 * k := by omega
  obtain ⟨o1, o2, o3, hM6⟩ := stAcc_sem I C ⟨M5, s4.o⟩ hM5 (o := ob + 2 * sv) (k := k) hC hk1 c5.1 c5.2
    (by simp only [regs] at hs ⊢; omega) (by omega) (by show _ ≤ M5.size; omega)
  have r6 : ∀ i, i < regs → i ≠ lgO → i ≠ cTmp →
      rd (semXIR I (stAcc C) ⟨M5, s4.o⟩).M i = rd M5 i := fun i hi h1 h2 =>
    frame I _ _ ((wf_stAcc C).2 trivial) hM5 i hi (fun h => (nw_stAcc i h2 h1 C).1 h)
  generalize semXIR I (stAcc C) ⟨M5, s4.o⟩ = s6 at o1 o2 o3 hM6 r6 ⊢
  -- `lgS += 1`
  obtain ⟨i7, i7f⟩ := incr_sem s6.M hM6 (r := lgS) (x := sv) (by decide) (by decide)
    (by rw [r6 _ (by decide) (by decide) (by decide), c5f _ (by decide) (by decide), hS4])
  have hM7 : Inv (runPrims [.op .add lgS lgS cOne] s6.M) := inv_runPrims (by simp [Prim.dst, lgS]) hM6
  generalize runPrims [.op .add lgS lgS cOne] s6.M = M7 at i7 i7f hM7 ⊢
  refine ⟨fun c hc => ?_, i7, fun i hi hp hne => ?_, hM7⟩
  · have q : lgAc + 2 * c + 1 < regs ∧ lgAc + 2 * c ≠ lgO ∧ lgAc + 2 * c ≠ cTmp ∧
        lgAc + 2 * c + 1 ≠ lgO ∧ lgAc + 2 * c + 1 ≠ cTmp ∧ lgAc + 2 * c ≠ lgK ∧
        lgAc + 2 * c + 1 ≠ lgK := by simp only [lgAc, lgO, cTmp, regs, lgK]; omega
    have hc2 : 2 * k * c + 2 ≤ 2 * k * C := by
      have := Nat.mul_le_mul_left (2 * k) (show c + 1 ≤ C by omega); rw [Nat.mul_succ] at this; omega
    rw [rdF_mk, i7f (ob + 2 * sv + 2 * k * c) (by simp only [lgS]; omega),
      i7f (ob + 2 * sv + 2 * k * c + 1) (by simp only [lgS]; omega), (o2 c hc).1, (o2 c hc).2,
      c5f _ q.2.2.2.2.2.1 q.2.1, c5f _ q.2.2.2.2.2.2 q.2.2.2.1, ← rdF_mk, g1 c hc]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.1 ht
    have hCt : C * t + c + 1 ≤ C * k := by
      have := Nat.mul_le_mul_left C (show t + 1 ≤ k by omega); rw [Nat.mul_succ] at this; omega
    rw [rdB, H3 _ (by simp only [regs]; omega), ← rdB, f3 t ht',
      rdF_eq (H3 _ (by simp only [regs]; omega)) (H3 _ (by simp only [regs]; omega)),
      rdF_eq (f4 _ (by simp only [regs]; omega) (.inr (by omega)))
        (f4 _ (by simp only [regs]; omega) (.inr (by omega))),
      rdF_eq (H1 _ (by simp only [regs]; omega)) (H1 _ (by simp only [regs]; omega))]
  · simp only [regs] at hi
    rw [i7f _ (by simp only [lgS]; omega), o3 i (by simp only [regs]; omega) hne,
      c5f _ (by simp only [lgK]; omega) (by simp only [lgO]; omega), g2 i (by simp only [regs]; omega),
      H3 i (by simp only [regs]; omega), f4 i (by simp only [regs]; omega) hp,
      H1 i (by simp only [regs]; omega)]

/-! ## The targets, and the interpolation -/

/-- Distinct targets' output cells are distinct (`a, b < k`; offsets `e, e' < 2`). -/
theorem out_ne {k a b c d e e' : ℕ} (ha : a < k) (hb : b < k) (hab : a ≠ b) (he : e < 2) (he' : e' < 2)
    (o : ℕ) : o + 2 * a + 2 * k * c + e ≠ o + 2 * b + 2 * k * d + e' := by
  intro H
  rw [Nat.mul_assoc 2 k c, Nat.mul_assoc 2 k d] at H
  have h1 : a + k * c = b + k * d := by omega
  have h2 := congrArg (· % k) h1
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  exact hab h2

/-- The output cells of a target lie in `[ob, ob + 2kC)`. -/
theorem outC_lt {k a c C : ℕ} (ha : a < k) (hc : c < C) (o : ℕ) : o + 2 * a + 2 * k * c + 1 < o + 2 * k * C := by
  have := Nat.mul_le_mul_left (2 * k) (show c + 1 ≤ C by omega)
  rw [Nat.mul_succ] at this
  omega

/-- **The target loop**: for `s < k`, `c < C`, output row `c` at `ob + 2s + 2kc` is
`Σ_{t<k} (P_t Q_t) · Y_c[t]`; the heap outside the prefix table and `[ob, ob + 2kC)` is kept. -/
theorem tgIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k C jb pb yb ob : ℕ} {Jl : List ℕ}
    (hk1 : 1 ≤ k) (hk : k < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb)
    (hjp : jb + k ≤ pb) (hpy : pb + k ≤ yb) (hyo : yb + 2 * C * k ≤ ob)
    (hos : ob + 2 * k * (C + 1) ≤ s.M.size) (ho2 : ob + 2 * k * (C + 1) + 2 < 2 ^ 64)
    (hJ : ∀ u < k, rd s.M (jb + u) = jw Jl u) :
    (∀ sv < k, ∀ c < C, rdF (semXIR I (tgIR k C jb pb yb ob) s).M (ob + 2 * sv + 2 * k * c) =
      ∑ t ∈ range k, F.smulBase (preP Jl sv t * sufP Jl k sv (t + 1))
        (rdF s.M (yb + 2 * (C * t + c)))) ∧
    (∀ i, regs ≤ i → (i < pb ∨ pb + k ≤ i) → (i < ob ∨ ob + 2 * k * C ≤ i) →
      rd (semXIR I (tgIR k C jb pb yb ob) s).M i = rd s.M i) ∧
    Inv (semXIR I (tgIR k C jb pb yb ob) s).M := by
  have hs : 256 ≤ s.M.size := hM.1
  simp only [regs] at hjb
  rw [tgIR, semXIR_seq, semB]
  have c1 : rd (runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M) lgS = toWord 0 ∧
      rd (runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M) lgN1 = toWord k := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, lgS, lgN1]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals rfl
  have c1f : ∀ i, regs ≤ i → rd (runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M) i = rd s.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp only [regs] at hi; simp [Prim.dst, lgS, lgN1]; omega) _
  have hM1 : Inv (runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M) :=
    inv_runPrims (by simp [Prim.dst, lgS, lgN1]) hM
  have z1 := size_runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M
  generalize runPrims [.const lgS 0, .const lgN1 (toWord k)] s.M = M1 at c1 c1f hM1 z1 ⊢
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M lgS = toWord j ∧
    (∀ sv < j, ∀ c < C, rdF st.M (ob + 2 * sv + 2 * k * c) =
      ∑ t ∈ range k, F.smulBase (preP Jl sv t * sufP Jl k sv (t + 1))
        (rdF s.M (yb + 2 * (C * t + c)))) ∧
    (∀ i, regs ≤ i → (i < pb ∨ pb + k ≤ i) → (i < ob ∨ ob + 2 * k * C ≤ i) → rd st.M i = rd s.M i)
  have ef : ∀ i, i ≠ lgC1 → i ≠ cTmp → rd (entryK lgC1 lgN1 (toWord k) M1) i = rd M1 i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (tgBody k C jb pb yb ob) P ⟨M1, s.o⟩ hM1 (by decide) (by decide) (by decide)
    c1.2 hk ⟨inv_entryK hM1 (by decide), by rw [size_entryK, z1],
      by rw [ef _ (by decide) (by decide), c1.1],
      fun sv hsv => absurd hsv (Nat.not_lt_zero _),
      fun i hi _ _ => (ef i (by simp only [regs, lgC1] at hi ⊢; omega)
        (by simp only [regs, cTmp] at hi ⊢; omega)).trans (c1f i hi)⟩ ?_
  · exact ⟨h.2.2.2.1, h.2.2.2.2, h.1⟩
  rintro j st hj ⟨hI, hz, hS', hV, hH⟩
  obtain ⟨b1, b2, b3, hI2⟩ := tgBody_sem I st hI (Jl := Jl) hk1 hk hC hj (by simp only [regs]; omega)
    hjp hpy hyo (by rw [hz]; exact hos) ho2 hS'
    (fun u hu => by rw [hH _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)), hJ u hu])
  have hd : ∀ i, regs ≤ i → rd (decS lgC1 (semXIR I (tgBody k C jb pb yb ob) st)).M i =
      rd (semXIR I (tgBody k C jb pb yb ob) st).M i :=
    fun i hi => rd_decS (by simp only [regs, lgC1] at hi ⊢; omega) _
  have hY : ∀ t < k, ∀ c < C, rdF st.M (yb + 2 * (C * t + c)) = rdF s.M (yb + 2 * (C * t + c)) :=
    fun t ht c hc => by
      have : C * t + c + 1 ≤ C * k := by
        have := Nat.mul_le_mul_left C (show t + 1 ≤ k by omega); rw [Nat.mul_succ] at this; omega
      have e2 : 2 * C * k = 2 * (C * k) := Nat.mul_assoc ..
      exact rdF_eq (hH _ (by simp only [regs]; omega) (.inr (by omega)) (.inl (by omega)))
        (hH _ (by simp only [regs]; omega) (.inr (by omega)) (.inl (by omega)))
  refine ⟨inv_decS hI2 (by decide), by rw [size_decS, size_sem, hz], by rw [rd_decS (by decide), b2],
    fun sv hsv c hc => ?_, fun i hi hp ho => ?_⟩
  · have hlt := outC_lt (k := k) (a := sv) (c := c) (C := C) (by omega) hc ob
    have hge : regs ≤ ob + 2 * sv + 2 * k * c := by simp only [regs]; omega
    rw [rdF_eq (hd _ hge) (hd _ (by simp only [regs] at hge ⊢; omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hsv with hsv | rfl
    · have hne : ∀ c' < C, ∀ e < 2, ob + 2 * sv + 2 * k * c + e ≠ ob + 2 * j + 2 * k * c' ∧
          ob + 2 * sv + 2 * k * c + e ≠ ob + 2 * j + 2 * k * c' + 1 := fun c' _ e he =>
        ⟨fun H => out_ne (e' := 0) (by omega) hj (by omega) he (by omega) ob (H.trans rfl),
          out_ne (by omega) hj (by omega) he (by omega) ob⟩
      rw [rdF_eq (b3 _ hge (.inr (by omega)) fun c' hc' => (hne c' hc' 0 (by omega)))
        (b3 _ (by simp only [regs] at hge ⊢; omega) (.inr (by omega))
          fun c' hc' => (hne c' hc' 1 (by omega)))]
      exact hV sv hsv c hc
    · rw [b1 c hc]
      exact Finset.sum_congr rfl fun t ht => by rw [hY t (Finset.mem_range.1 ht) c hc]
  · rw [hd i hi, b3 i hi hp fun c hc => ⟨fun e => by
        have := outC_lt (k := k) (a := j) (c := c) (C := C) hj hc ob; omega, fun e => by
        have := outC_lt (k := k) (a := j) (c := c) (C := C) hj hc ob; omega⟩,
      hH i hi hp ho]

/-- **The interpolation of rows `c₀ … c₀ + C − 1`** (`lagIR`): on the layout
`regs ≤ jb`, `jb + k ≤ pb`, `pb + k ≤ yb`, `yb + 2Ck ≤ ob`, `yb + 2Ck ≤ cb`, output row `c` at target
`s < k` (cell `ob + 2s + 2kc`) is `lagVal J k s y_{c₀+c}` with `y_c(j)` the `F` element at
`cb + cs·j + 2(c₀ + c)`. The heap outside `[pb, ob + 2kC)` is kept. -/
theorem lagIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k C c0 jb pb yb ob cb cs : ℕ}
    {Jl : List ℕ} (hk1 : 1 ≤ k) (hk : k < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb)
    (hjp : jb + k ≤ pb) (hpy : pb + k ≤ yb) (hyo : yb + 2 * C * k ≤ ob) (hcb : yb + 2 * C * k ≤ cb)
    (hos : ob + 2 * k * (C + 1) ≤ s.M.size) (ho2 : ob + 2 * k * (C + 1) + 2 < 2 ^ 64)
    (hcb2 : ∀ t < k, cb + cs * Jl.getD t 0 + 2 * c0 + 2 * C + 2 < 2 ^ 64)
    (hJ : ∀ u < k, rd s.M (jb + u) = jw Jl u) :
    (∀ sv < k, ∀ c < C, rdF (semXIR I (lagIR k C c0 jb pb yb ob cb cs) s).M (ob + 2 * sv + 2 * k * c) =
      lagVal Jl k sv fun j => rdF s.M (cb + cs * j + 2 * c0 + 2 * c)) ∧
    (∀ i, regs ≤ i → (i < pb ∨ ob + 2 * k * C ≤ i) →
      rd (semXIR I (lagIR k C c0 jb pb yb ob cb cs) s).M i = rd s.M i) ∧
    Inv (semXIR I (lagIR k C c0 jb pb yb ob cb cs) s).M := by
  have hCk : 2 * C * k = 2 * k * C := by ring
  rw [lagIR, semXIR_seq]
  obtain ⟨y1, y2, hM1⟩ := yTab_sem I s hM (J := fun t => Jl.getD t 0) (cb := cb) (cs := cs) (c0 := c0)
    hk (by omega) hjb (by omega) (by omega) (by omega) hcb hcb2 hJ
  have z1 := size_sem I (yTabIR k C jb yb cb cs c0) s
  generalize semXIR I (yTabIR k C jb yb cb cs c0) s = s1 at y1 y2 hM1 z1 ⊢
  simp only [regs] at hjb
  obtain ⟨t1, t2, hM2⟩ := tgIR_sem I s1 hM1 (Jl := Jl) (C := C) (yb := yb) hk1 hk hC
    (by simp only [regs]; omega) hjp hpy hyo (by rw [z1]; exact hos) ho2
    (fun u hu => by rw [y2 _ (by simp only [regs]; omega) (.inl (by omega)), hJ u hu])
  refine ⟨fun sv hsv c hc => ?_, fun i hi hi2 => ?_, hM2⟩
  · rw [t1 sv hsv c hc, lagVal]
    refine Finset.sum_congr rfl fun t ht => ?_
    have h := y1 t (Finset.mem_range.1 ht) c hc
    rw [lagTerm, yv, rdF_mk, ← rdB, ← rdB, h.1, h.2]
    show F.smulBase _ ⟨_, _⟩ = F.smulBase _ ⟨_, _⟩
    rw [mul_comm (rdB s.M _), mul_comm (rdB s.M _)]
    rfl
  · rw [t2 i hi (by omega) (by omega), y2 i hi (by omega)]

/-- **`lagIR` interpolates**: with `J` listed without repeats below `2^20` and `k = |J|`, output row
`c` at target `s` is `interpF D J y_{c₀+c} s`. -/
theorem lagIR_interp (I : Array Word) (s : St) (hM : Inv s.M) {C c0 jb pb yb ob cb cs : ℕ}
    {Jl : List ℕ} (hnd : Jl.Nodup) (hJn : ∀ j ∈ Jl, j < nMax) (hk1 : 1 ≤ Jl.length)
    (hk : Jl.length < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb)
    (hjp : jb + Jl.length ≤ pb) (hpy : pb + Jl.length ≤ yb) (hyo : yb + 2 * C * Jl.length ≤ ob)
    (hcb : yb + 2 * C * Jl.length ≤ cb) (hos : ob + 2 * Jl.length * (C + 1) ≤ s.M.size)
    (ho2 : ob + 2 * Jl.length * (C + 1) + 2 < 2 ^ 64)
    (hcb2 : ∀ t < Jl.length, cb + cs * Jl.getD t 0 + 2 * c0 + 2 * C + 2 < 2 ^ 64)
    (hJ : ∀ u < Jl.length, rd s.M (jb + u) = jw Jl u) :
    ∀ sv < Jl.length, ∀ c < C,
      rdF (semXIR I (lagIR Jl.length C c0 jb pb yb ob cb cs) s).M (ob + 2 * sv + 2 * Jl.length * c) =
        interpF D Jl.toFinset (fun j => rdF s.M (cb + cs * j + 2 * c0 + 2 * c)) sv :=
  fun sv hsv c hc => by
    rw [(lagIR_sem I s hM hk1 hk hC hjb hjp hpy hyo hcb hos ho2 hcb2 hJ).1 sv hsv c hc, lagVal_eq hnd hJn]

/-! ## Controls -/

/-- (+) **`lagIR` returns the data at a listed position**: a target `s ∈ J` gets row `c₀ + c`'s
value `y(s)`. -/
theorem lagIR_node_ctl (I : Array Word) (s : St) (hM : Inv s.M) {C c0 jb pb yb ob cb cs : ℕ}
    {Jl : List ℕ} (hnd : Jl.Nodup) (hJn : ∀ j ∈ Jl, j < nMax) (hk1 : 1 ≤ Jl.length)
    (hk : Jl.length < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb)
    (hjp : jb + Jl.length ≤ pb) (hpy : pb + Jl.length ≤ yb) (hyo : yb + 2 * C * Jl.length ≤ ob)
    (hcb : yb + 2 * C * Jl.length ≤ cb) (hos : ob + 2 * Jl.length * (C + 1) ≤ s.M.size)
    (ho2 : ob + 2 * Jl.length * (C + 1) + 2 < 2 ^ 64)
    (hcb2 : ∀ t < Jl.length, cb + cs * Jl.getD t 0 + 2 * c0 + 2 * C + 2 < 2 ^ 64)
    (hJ : ∀ u < Jl.length, rd s.M (jb + u) = jw Jl u) {sv c : ℕ} (hsv : sv < Jl.length)
    (hsJ : sv ∈ Jl) (hc : c < C) :
    rdF (semXIR I (lagIR Jl.length C c0 jb pb yb ob cb cs) s).M (ob + 2 * sv + 2 * Jl.length * c) =
      rdF s.M (cb + cs * sv + 2 * c0 + 2 * c) := by
  rw [lagIR_interp I s hM hnd hJn hk1 hk hC hjb hjp hpy hyo hcb hos ho2 hcb2 hJ sv hsv c hc]
  exact interpF_self (fun a ha b hb h => D_injOn_nMax (hJn a (List.mem_toFinset.1 ha))
    (hJn b (List.mem_toFinset.1 hb)) h) _ (List.mem_toFinset.2 hsJ)

/-- (−) **`lagIR` reads its own row window**: where rows `c₀ + c` and `c₀ + c + 1` differ at a
listed target, output row `c` is not row `c₀ + c + 1`'s value. -/
theorem lagIR_row_ctl (I : Array Word) (s : St) (hM : Inv s.M) {C c0 jb pb yb ob cb cs : ℕ}
    {Jl : List ℕ} (hnd : Jl.Nodup) (hJn : ∀ j ∈ Jl, j < nMax) (hk1 : 1 ≤ Jl.length)
    (hk : Jl.length < 2 ^ 64) (hC : C ≤ 16) (hjb : regs ≤ jb)
    (hjp : jb + Jl.length ≤ pb) (hpy : pb + Jl.length ≤ yb) (hyo : yb + 2 * C * Jl.length ≤ ob)
    (hcb : yb + 2 * C * Jl.length ≤ cb) (hos : ob + 2 * Jl.length * (C + 1) ≤ s.M.size)
    (ho2 : ob + 2 * Jl.length * (C + 1) + 2 < 2 ^ 64)
    (hcb2 : ∀ t < Jl.length, cb + cs * Jl.getD t 0 + 2 * c0 + 2 * C + 2 < 2 ^ 64)
    (hJ : ∀ u < Jl.length, rd s.M (jb + u) = jw Jl u) {sv c : ℕ} (hsv : sv < Jl.length)
    (hsJ : sv ∈ Jl) (hc : c < C)
    (hne : rdF s.M (cb + cs * sv + 2 * c0 + 2 * c) ≠ rdF s.M (cb + cs * sv + 2 * c0 + 2 * (c + 1))) :
    rdF (semXIR I (lagIR Jl.length C c0 jb pb yb ob cb cs) s).M (ob + 2 * sv + 2 * Jl.length * c) ≠
      rdF s.M (cb + cs * sv + 2 * c0 + 2 * (c + 1)) := by
  rw [lagIR_node_ctl I s hM hnd hJn hk1 hk hC hjb hjp hpy hyo hcb hos ho2 hcb2 hJ hsv hsJ hc]
  exact hne

end FR.X
