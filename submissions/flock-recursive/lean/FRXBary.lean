-- New for `flock-recursive` (BLUEPRINT §6.2 step 4; stage S-H2, track L-ext).
import FRXBaryDefs
import FRXBfly

/-!
# The barycentric interpolation on the machine: the semantics

Bottom-up: the address block, a generic `loopK` run, `D(x)` by `alphaIR`, the tables `DJ` and `W`,
one target's `E` row, one coordinate, one target, and **`baryIR_sem`**: on the layout `BaryLay`,
`out[c][s] = baryVal J k s y_c` for `s < k`, `c < C` (= `interpF D J y_c s` by `baryVal_eq`).
-/

namespace FR.X

open RecursionFast FR Finset

attribute [local irreducible] entryK storeM

/-! ## Helpers -/

/-- **A generic `loopK` run**: an invariant `P` preserved by the body for `j < K` holds after the
loop. -/
theorem loopK_run (I : Array Word) {c n K : ℕ} (b : XIR) (P : ℕ → St → Prop) (s : St)
    (hM : Inv s.M) (hc : 4 < c) (hcr : c < regs) (hn : n ≠ c) (hN : rd s.M n = toWord K)
    (hK : K < 2 ^ 64) (h0 : P 0 ⟨entryK c n (toWord K) s.M, s.o⟩)
    (hstep : ∀ j s, j < K → P j s → P (j + 1) (decS c (semXIR I b s))) :
    P K (semXIR I (.loopK c n (toWord K) b) s) := by
  rw [loopK_eq I b s hM hc hcr hn hN, toNat_toWord hK]
  simpa using iterL_ind P hstep K 0 _ (by omega) h0

theorem toWord_zero' : toWord 0 = (0 : Word) := rfl

theorem toWord_mul' (a b : ℕ) : toWord a * toWord b = toWord (a * b) := (BitVec.ofNat_mul a b).symm

/-- **The address block** `d := b + m · M[i]`. -/
theorem addrPs_sem (M : Mem) (hs : regs ≤ M.size) {d i b m x : ℕ} (hd : d < regs) (hdK : d ≠ bK)
    (hi : i ≠ bK) (hx : rd M i = toWord x) :
    rd (runPrims (addrPs d i b m) M) d = toWord (b + m * x) ∧
    ∀ j, j ≠ d → j ≠ bK → rd (runPrims (addrPs d i b m) M) j = rd M j := by
  have hK : bK < M.size := by simp only [regs] at hs; simp only [bK]; omega
  have hd' : d < M.size := by simp only [regs] at hs hd; omega
  refine ⟨?_, fun j h1 h2 => rd_runPrims_of_not_writes (by
    simp only [addrPs, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst] <;> omega) _⟩
  simp only [addrPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | exact hdK | exact hdK.symm | exact hi.symm | exact hK | exact hd' |
    (simp only [size_set]; first | exact hd' | exact hK)) only [rd_set_self, rd_set_ne, hx]
  rw [mul_toWord, add_toWord, Nat.add_comm, Nat.mul_comm]

/-- `Σ_{i<20} [bit_i x] D(2^i) = D x` (`x < 2^20`): `alphaIR` on the basis table's row 0. -/
theorem alpha_D {x : ℕ} (hx : x < nMax) :
    ∑ i ∈ range 20, (if x.testBit i then (wRow D logNMax 0).getD i 0 else 0) = D x := by
  have h := wAtD_eq (v := 0) (j := x) (by decide) hx
  rw [normW_zero_eval, show D 0 = 0 by decide, show D 1 = 1 by decide, sub_zero, sub_zero,
    div_one] at h
  exact h

/-- **`D(x)` by `alphaIR`** from the basis table's row 0 at `tb`. -/
theorem alphaD_sem (I : Array Word) (s : St) (hM : Inv s.M) {x tb : ℕ} (hx : x < nMax)
    (htb : regs ≤ tb) (htb2 : tb + 40 < 2 ^ 64) (hBs : rd s.M rBs = toWord x)
    (hTr : rd s.M rTr = toWord tb)
    (hT : ∀ i < 20, rdF s.M (tb + 2 * i) = (wRow D logNMax 0).getD i 0) :
    rdF (semXIR I alphaIR s).M fAl = D x := by
  rw [alphaIR_sem I s hM (lt_of_lt_of_le hx (by decide)) htb htb2 hBs hTr hT]
  exact alpha_D hx

/-- A load: `d := M[M[a]]`. -/
theorem bload_sem (I : Array Word) (s : St) (hM : Inv s.M) {d a x : ℕ} (hd : d < regs)
    (ha : rd s.M a = toWord x) (hx : x < 2 ^ 64) :
    rd (semXIR I (.load d a) s).M d = rd s.M x ∧
    ∀ i, i ≠ d → rd (semXIR I (.load d a) s).M i = rd s.M i := by
  have hs := hM.1
  refine ⟨?_, fun i hi => rd_set_ne (Ne.symm hi)⟩
  show rd (s.M.setIfInBounds d _) d = _
  rw [rd_set_self (by simp only [regs] at hs hd; omega), ha, toNat_toWord hx]

/-- `r += 1`. -/
theorem incr_sem (M : Mem) (hM : Inv M) {r x : ℕ} (hr : r < regs) (hr4 : 4 ≤ r)
    (hx : rd M r = toWord x) :
    rd (runPrims [.op .add r r cOne] M) r = toWord (x + 1) ∧
    ∀ i, i ≠ r → rd (runPrims [.op .add r r cOne] M) i = rd M i := by
  have hs := hM.1
  have h1 : rd M cOne = 1 := hM.2 0 (by decide)
  refine ⟨?_, fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _⟩
  simp only [runPrims, List.foldl, Prim.run]
  rw [rd_set_self (by simp only [regs] at hs hr; omega), hx, h1, add_one_toWord]

/-! ## The table `DJ` -/

/-- **One entry of `DJ`**: `DJ[t] := D(J_t)`. -/
theorem djBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {jb djb tb t x : ℕ}
    (hjb : regs ≤ jb) (hdjb : regs ≤ djb) (htb : regs ≤ tb) (hsz : djb + 2 * t + 1 < s.M.size)
    (hdj2 : djb + 2 * t + 1 < 2 ^ 64) (hjb2 : jb + t < 2 ^ 64) (htb2 : tb + 40 < 2 ^ 64)
    (hT0 : rd s.M bT = toWord t) (hJ : rd s.M (jb + t) = toWord x) (hx : x < nMax)
    (hT : ∀ i < 20, rdF s.M (tb + 2 * i) = (wRow D logNMax 0).getD i 0) :
    rdF (semXIR I (djBody jb djb tb) s).M (djb + 2 * t) = D x ∧
    rd (semXIR I (djBody jb djb tb) s).M bT = toWord (t + 1) ∧
    (∀ y, regs ≤ y → y ≠ djb + 2 * t → y ≠ djb + 2 * t + 1 →
      rd (semXIR I (djBody jb djb tb) s).M y = rd s.M y) ∧
    Inv (semXIR I (djBody jb djb tb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hjb hdjb htb
  rw [djBody, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq]
  -- `bA := jb + t`
  obtain ⟨a1, a1f⟩ := addrPs_sem s.M hM.1 (d := bA) (i := bT) (b := jb) (m := 1) (by decide)
    (by decide) (by decide) hT0
  have hM1 : Inv (runPrims (addrPs bA bT jb 1) s.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM
  have z1 := size_runPrims (addrPs bA bT jb 1) s.M
  have e1 : semXIR I (.blk (addrPs bA bT jb 1)) s = ⟨runPrims (addrPs bA bT jb 1) s.M, s.o⟩ := rfl
  rw [e1]
  have h1 : ∀ y, regs ≤ y → rd (runPrims (addrPs bA bT jb 1) s.M) y = rd s.M y := fun y hy =>
    a1f y (by simp only [regs] at hy; simp only [bA]; omega) (by simp only [regs] at hy; simp only [bK]; omega)
  have t1 : rd (runPrims (addrPs bA bT jb 1) s.M) bT = toWord t := (a1f _ (by decide) (by decide)).trans hT0
  generalize runPrims (addrPs bA bT jb 1) s.M = M1 at a1 a1f hM1 z1 h1 t1
  -- `rBs := J_t`
  obtain ⟨l2, l2f⟩ := bload_sem I ⟨M1, s.o⟩ hM1 (d := rBs) (a := bA) (x := jb + 1 * t) (by decide)
    a1 (by omega)
  have hM2 := inv_sem I (P := .load rBs bA) (s := ⟨M1, s.o⟩) (by simp +decide only [WF, rBs]) hM1
  have z2 := size_sem I (.load rBs bA) ⟨M1, s.o⟩
  have h2 : ∀ y, regs ≤ y → rd (semXIR I (.load rBs bA) ⟨M1, s.o⟩).M y = rd s.M y := fun y hy =>
    (l2f y (by simp only [regs] at hy; simp only [rBs]; omega)).trans (h1 y hy)
  have t2 : rd (semXIR I (.load rBs bA) ⟨M1, s.o⟩).M bT = toWord t := (l2f _ (by decide)).trans t1
  rw [h1 _ (by simp only [regs]; omega), Nat.one_mul, hJ] at l2
  generalize semXIR I (.load rBs bA) ⟨M1, s.o⟩ = s2 at l2 l2f hM2 z2 h2 t2
  -- `rTr := tb`
  have hM3 := inv_sem I (P := .blk [.const rTr (toWord tb)]) (s := s2) (by simp +decide only [WF,
    Prim.dst, rTr, List.mem_cons, List.mem_nil_iff, forall_eq, or_false])
    hM2
  have z3 := size_sem I (.blk [.const rTr (toWord tb)]) s2
  have hs2 := hM2.1
  simp only [regs] at hs2
  have r3 : rd (semXIR I (.blk [.const rTr (toWord tb)]) s2).M rTr = toWord tb := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [rTr]; omega)]
  have f3 : ∀ i, i ≠ rTr → rd (semXIR I (.blk [.const rTr (toWord tb)]) s2).M i = rd s2.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  generalize semXIR I (.blk [.const rTr (toWord tb)]) s2 = s3 at hM3 z3 r3 f3
  -- `fAl := D(J_t)`
  have b3 : rd s3.M rBs = toWord x := (f3 _ (by decide)).trans l2
  have T3 : ∀ i < 20, rdF s3.M (tb + 2 * i) = (wRow D logNMax 0).getD i 0 := fun i hi => by
    rw [rdF_eq (f3 _ (by simp only [rTr]; omega)) (f3 _ (by simp only [rTr]; omega)),
      rdF_eq (h2 _ (by simp only [regs]; omega)) (h2 _ (by simp only [regs]; omega)), hT i hi]
  have d4 := alphaD_sem I s3 hM3 hx (by simp only [regs]; omega) htb2 b3 r3 T3
  have hM4 := inv_sem I wf_alphaIR hM3
  have z4 := size_sem I alphaIR s3
  have h4 : ∀ y, regs ≤ y → rd (semXIR I alphaIR s3).M y = rd s.M y := fun y hy => by
    rw [hframeK I alphaIR s3 loK_alphaIR y hy, f3 _ (by simp only [regs] at hy; simp only [rTr]; omega),
      h2 y hy]
  have t4 : rd (semXIR I alphaIR s3).M bT = toWord t := by
    rw [frame I alphaIR s3 wf_alphaIR hM3 bT (by decide) (by
      simp +decide only [alphaIR, alphaBody, ldF, Writes, Prim.dst, bT, rBit, uT1, fG, fAl, rTa,
        rTa1, uI, rC2, rN2, cTmp, or_false]), f3 _ (by decide), t2]
  generalize semXIR I alphaIR s3 = s4 at d4 hM4 z4 h4 t4
  -- `bA := djb + 2t`
  obtain ⟨a5, a5f⟩ := addrPs_sem s4.M hM4.1 (d := bA) (i := bT) (b := djb) (m := 2) (by decide)
    (by decide) (by decide) t4
  have hM5 : Inv (runPrims (addrPs bA bT djb 2) s4.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM4
  have z5 := size_runPrims (addrPs bA bT djb 2) s4.M
  have e5 : semXIR I (.blk (addrPs bA bT djb 2)) s4 = ⟨runPrims (addrPs bA bT djb 2) s4.M, s4.o⟩ :=
    rfl
  rw [e5]
  have d5 : rdF (runPrims (addrPs bA bT djb 2) s4.M) fAl = D x := by
    rw [rdF_eq (a5f _ (by decide) (by decide)) (a5f _ (by decide) (by decide)), d4]
  have t5 : rd (runPrims (addrPs bA bT djb 2) s4.M) bT = toWord t := (a5f _ (by decide) (by decide)).trans t4
  have h5 : ∀ y, regs ≤ y → rd (runPrims (addrPs bA bT djb 2) s4.M) y = rd s.M y := fun y hy =>
    (a5f y (by simp only [regs] at hy; simp only [bA]; omega)
      (by simp only [regs] at hy; simp only [bK]; omega)).trans (h4 y hy)
  generalize runPrims (addrPs bA bT djb 2) s4.M = M5 at a5 a5f hM5 z5 d5 t5 h5
  -- `DJ[t] := fAl`
  have hz : djb + 2 * t + 1 < M5.size := by rw [z5, z4, z3, z2]; show _ < M1.size; rw [z1]; exact hsz
  obtain ⟨g1, g2, hM6⟩ := stF_sem I ⟨M5, s4.o⟩ hM5 (p := bA) (p1 := bA1) (v := fAl)
    (x := djb + 2 * t) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) a5 (by simp only [regs]; omega) hdj2 hz
  have z6 := size_sem I (stF bA bA1 fAl) ⟨M5, s4.o⟩
  have t6 : rd (semXIR I (stF bA bA1 fAl) ⟨M5, s4.o⟩).M bT = toWord t := by
    rw [g2 _ (by simp only [bT]; omega) (by simp only [bT]; omega) (by decide) (by decide), t5]
  generalize semXIR I (stF bA bA1 fAl) ⟨M5, s4.o⟩ = s6 at g1 g2 hM6 z6 t6
  -- `t += 1`
  obtain ⟨i7, i7f⟩ := incr_sem s6.M hM6 (r := bT) (x := t) (by decide) (by decide) t6
  have e7 : semXIR I (.blk [.op .add bT bT cOne]) s6 = ⟨runPrims [.op .add bT bT cOne] s6.M, s6.o⟩ :=
    rfl
  rw [e7]
  refine ⟨?_, i7, fun y hy h1' h2' => ?_, inv_runPrims (by simp [Prim.dst, bT]) hM6⟩
  · rw [rdF_eq (i7f _ (by simp only [bT]; omega)) (i7f _ (by simp only [bT]; omega)), g1, d5]
  · simp only [regs] at hy
    rw [i7f _ (by simp only [bT]; omega), g2 y h1' h2' (by simp only [bA1]; omega)
      (by simp only [cTmp]; omega), h5 y (by simp only [regs]; omega)]

/-- The two constants before a loop: `r := v`, `n := K`. -/
theorem pre2_sem (M : Mem) (hM : Inv M) {r n : ℕ} (v K : Word) (hr : r < regs) (hn : n < regs)
    (hrn : r ≠ n) (hr4 : 4 ≤ r) (hn4 : 4 ≤ n) :
    rd (runPrims [.const r v, .const n K] M) r = v ∧ rd (runPrims [.const r v, .const n K] M) n = K ∧
    (∀ i, i ≠ r → i ≠ n → rd (runPrims [.const r v, .const n K] M) i = rd M i) ∧
    Inv (runPrims [.const r v, .const n K] M) := by
  have hs := hM.1
  simp only [regs] at hs hr hn
  refine ⟨?_, ?_, fun i h1 h2 => rd_runPrims_of_not_writes (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl) <;> simp only [Prim.dst] <;> omega) _,
    inv_runPrims (by simp [Prim.dst]; omega) hM⟩
  · simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne hrn.symm, rd_set_self (by omega)]
  · simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set]; omega)]

/-- **The table `DJ`**: `DJ[t] = D(J_t)` at `djb + 2t` for `t < k`; nothing else on the heap
changes. -/
theorem djIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb djb tb : ℕ} {J : ℕ → ℕ}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (hdjb : regs ≤ djb) (htb : regs ≤ tb)
    (hsz : djb + 2 * k ≤ s.M.size) (hdj2 : djb + 2 * k < 2 ^ 64) (hjb2 : jb + k < 2 ^ 64)
    (htb2 : tb + 40 < 2 ^ 64) (hdJ : jb + k ≤ djb ∨ djb + 2 * k ≤ jb)
    (hdT : tb + 40 ≤ djb ∨ djb + 2 * k ≤ tb)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (J t)) (hJn : ∀ t < k, J t < nMax)
    (hT : ∀ i < 20, rdF s.M (tb + 2 * i) = (wRow D logNMax 0).getD i 0) :
    (∀ t < k, rdF (semXIR I (djIR k jb djb tb) s).M (djb + 2 * t) = D (J t)) ∧
    (∀ y, regs ≤ y → (y < djb ∨ djb + 2 * k ≤ y) →
      rd (semXIR I (djIR k jb djb tb) s).M y = rd s.M y) ∧
    Inv (semXIR I (djIR k jb djb tb) s).M := by
  rw [djIR, semXIR_seq]
  obtain ⟨p1, p2, p3, hM1⟩ := pre2_sem s.M hM (r := bT) (n := bN1) 0 (toWord k)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have e1 : semXIR I (.blk [.const bT 0, .const bN1 (toWord k)]) s =
      ⟨runPrims [.const bT 0, .const bN1 (toWord k)] s.M, s.o⟩ := rfl
  rw [e1]
  have z1 := size_runPrims [.const bT 0, .const bN1 (toWord k)] s.M
  replace p1 := p1.trans toWord_zero'.symm
  generalize runPrims [.const bT 0, .const bN1 (toWord k)] s.M = M1 at p1 p2 p3 hM1 z1
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bT = toWord j ∧
    (∀ t < j, rdF st.M (djb + 2 * t) = D (J t)) ∧
    (∀ y, regs ≤ y → (y < djb ∨ djb + 2 * j ≤ y) → rd st.M y = rd s.M y)
  have hfin := loopK_run I (c := bC1) (n := bN1) (K := k) (djBody jb djb tb) P ⟨M1, s.o⟩ hM1
    (by decide) (by decide) (by decide) p2 hk ?_ ?_
  · exact ⟨hfin.2.2.2.1, fun y hy hy2 => hfin.2.2.2.2 y hy hy2, hfin.1⟩
  · refine ⟨inv_of_frame hM1 (size_entryK ..) fun i hi => entryK_frame _ (by simp only [bC1]; omega)
      (by simp only [cTmp]; omega), by rw [size_entryK, z1], ?_, fun t ht => absurd ht (Nat.not_lt_zero _),
      fun y hy _ => ?_⟩
    · rw [entryK_frame _ (by decide) (by decide), p1]
    · simp only [regs] at hy
      rw [entryK_frame _ (by simp only [bC1]; omega) (by simp only [cTmp]; omega),
        p3 _ (by simp only [bT]; omega) (by simp only [bN1]; omega)]
  · rintro j st hj ⟨hM', hz, hT', hD, hH⟩
    have hJ' : rd st.M (jb + j) = toWord (J j) := by
      rw [hH _ (by simp only [regs] at hjb ⊢; omega) (by omega), hJ j hj]
    have hT'' : ∀ i < 20, rdF st.M (tb + 2 * i) = (wRow D logNMax 0).getD i 0 := fun i hi => by
      rw [rdF_eq (hH _ (by simp only [regs] at htb ⊢; omega) (by omega))
        (hH _ (by simp only [regs] at htb ⊢; omega) (by omega)), hT i hi]
    obtain ⟨b1, b2, b3, hM2⟩ := djBody_sem I st hM' (t := j) hjb hdjb htb (by omega) (by omega)
      (by omega) htb2 hT' hJ' (hJn j hj) hT''
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz], ?_, fun t ht => ?_,
      fun y hy hy2 => ?_⟩
    · rw [rd_decS (by decide), b2]
    · rw [rdF_decS _ (by simp only [bC1, regs] at hdjb ⊢; omega)
        (by simp only [bC1, regs] at hdjb ⊢; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [rdF_eq (b3 _ (by simp only [regs] at hdjb ⊢; omega) (by omega) (by omega))
          (b3 _ (by simp only [regs] at hdjb ⊢; omega) (by omega) (by omega)), hD t ht]
      · exact b1
    · rw [rd_decS (by simp only [bC1, regs] at hy ⊢; omega), b3 y hy (by omega) (by omega),
        hH y hy (by omega)]

/-! ## The table `W` -/

theorem F_one_w : (⟨wB 1, wB 0⟩ : F) = 1 := rfl

theorem lo_mulF {d a b : ℕ} (h : d + 1 < regs) : Lo (mulF d a b) := fun p hp => by
  have := mulFC_dst d a b p hp; simp only [regs] at h ⊢; omega
theorem lo_addF {d a b : ℕ} (h : d + 1 < regs) : Lo (addF d a b) := fun p hp => by
  have := addFC_dst d a b p hp; simp only [regs] at h ⊢; omega
theorem lo_invF {d a : ℕ} (h : d + 1 < regs) : Lo (invF d a) := fun p hp => by
  have := invFC_dst d a p hp; simp only [regs] at h ⊢; omega

theorem lo_wInner (djb : ℕ) : Lo (wInner djb) :=
  ⟨by simp +decide only [Lo, addrPs, Prim.dst, bA, bK, regs, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], ⟨by simp +decide only [
    Lo, ldF, Prim.dst, fX, bA1, regs, and_true],
    lo_addF (by decide), by simp +decide only [Lo, Prim.dst, bZ, regs], ⟨by simp +decide only [Lo], lo_mulF (by decide)⟩,
    by simp +decide only [Lo, Prim.dst, bM, regs]⟩⟩

theorem wf_wInner (djb : ℕ) : WF (wInner djb) := by
  simp +decide only [wInner, addrPs, ldF, WF, Prim.dst, wfF_mul, wfF_add, bA, bK, bA1, fX, fDd, bZ,
    bM, fPr, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

/-- **One factor** of `W[t]`: `fPr *= (m = t ? 1 : DJ[t] + DJ[m])`. -/
theorem wInner_sem (I : Array Word) (s : St) (hM : Inv s.M) {djb m t : ℕ} {dt : F}
    (hdjb : regs ≤ djb) (hm : m < 2 ^ 64) (ht : t < 2 ^ 64) (hdj2 : djb + 2 * m + 1 < 2 ^ 64)
    (hBm : rd s.M bM = toWord m) (hBt : rd s.M bT = toWord t) (hDs : rdF s.M fDs = dt) :
    rdF (semXIR I (wInner djb) s).M fPr =
      rdF s.M fPr * (if m = t then 1 else dt + rdF s.M (djb + 2 * m)) ∧
    rd (semXIR I (wInner djb) s).M bM = toWord (m + 1) ∧
    rd (semXIR I (wInner djb) s).M bT = toWord t ∧ rdF (semXIR I (wInner djb) s).M fDs = dt ∧
    Inv (semXIR I (wInner djb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdjb
  rw [wInner, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq]
  obtain ⟨a1, a1f⟩ := addrPs_sem s.M hM.1 (d := bA) (i := bM) (b := djb) (m := 2) (by decide)
    (by decide) (by decide) hBm
  have hM1 : Inv (runPrims (addrPs bA bM djb 2) s.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM
  have e1 : semXIR I (.blk (addrPs bA bM djb 2)) s = ⟨runPrims (addrPs bA bM djb 2) s.M, s.o⟩ := rfl
  rw [e1]
  have h1 : ∀ y, regs ≤ y → rd (runPrims (addrPs bA bM djb 2) s.M) y = rd s.M y := fun y hy =>
    a1f y (by simp only [regs] at hy; simp only [bA]; omega)
      (by simp only [regs] at hy; simp only [bK]; omega)
  have k1 : ∀ r, r ≠ bA → r ≠ bK → rd (runPrims (addrPs bA bM djb 2) s.M) r = rd s.M r := a1f
  generalize runPrims (addrPs bA bM djb 2) s.M = M1 at a1 a1f hM1 h1 k1
  obtain ⟨l1, l2, l3⟩ := ldF_sem I ⟨M1, s.o⟩ hM1 (d := fX) (p := bA) (p1 := bA1)
    (x := djb + 2 * m) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a1
    (by simp only [regs]; omega) hdj2
  have hM2 := inv_sem I (P := ldF fX bA bA1) (s := ⟨M1, s.o⟩)
    (by simp +decide only [ldF, WF, Prim.dst, fX, bA1, and_true]) hM1
  have kk : ∀ r, r ≠ fX → r ≠ fX + 1 → r ≠ bA1 → r ≠ bA → r ≠ bK →
      rd (semXIR I (ldF fX bA bA1) ⟨M1, s.o⟩).M r = rd s.M r := fun r a b c d e =>
    (l3 r a b c).trans (k1 r d e)
  rw [rdF_eq (h1 _ (by simp only [regs]; omega)) (h1 _ (by simp only [regs]; omega))] at l1
  generalize semXIR I (ldF fX bA bA1) ⟨M1, s.o⟩ = s2 at l1 l2 l3 hM2 kk
  have ds2 : rdF s2.M fDs = dt := by
    rw [rdF_eq (kk _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (kk _ (by decide) (by decide) (by decide) (by decide) (by decide)), hDs]
  have d3 := addF_sem (I := I) (s := s2) hM2 (d := fDd) (a := fDs) (b := fX) (by decide)
    (by decide) (by decide)
  have hM3 := inv_sem I (wf_addF fDd fDs fX (by decide)) hM2
  have k3 : ∀ r, r ≠ fDd → r ≠ fDd + 1 → rd (semXIR I (addF fDd fDs fX) s2).M r = rd s2.M r :=
    fun r a b => addFC_frame _ _ _ a b _
  generalize semXIR I (addF fDd fDs fX) s2 = s3 at d3 hM3 k3
  have hs3 := hM3.1
  simp only [regs] at hs3
  have z4 : rd (semXIR I (.blk [.op .eq bZ bM bT]) s3).M bZ = bW (decide (m = t)) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [bZ]; omega), k3 _ (by decide) (by decide),
      kk _ (by decide) (by decide) (by decide) (by decide) (by decide), hBm,
      k3 _ (by decide) (by decide), kk _ (by decide) (by decide) (by decide) (by decide)
        (by decide), hBt, eqW_toWord hm ht]
  have k4 : ∀ r, r ≠ bZ → rd (semXIR I (.blk [.op .eq bZ bM bT]) s3).M r = rd s3.M r :=
    fun r hr => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hr) _
  have hM4 := inv_sem I (P := .blk [.op .eq bZ bM bT]) (s := s3) (by simp +decide only [WF,
    Prim.dst, bZ]) hM3
  generalize semXIR I (.blk [.op .eq bZ bM bT]) s3 = s4 at z4 k4 hM4
  -- the conditional product
  have p5 : rdF (semXIR I (.ite bZ (.blk []) (mulF fPr fPr fDd)) s4).M fPr =
      rdF s.M fPr * (if m = t then 1 else dt + rdF s.M (djb + 2 * m)) := by
    have ePr : rdF s4.M fPr = rdF s.M fPr := by
      rw [rdF_eq (k4 _ (by decide)) (k4 _ (by decide)), rdF_eq (k3 _ (by decide) (by decide))
        (k3 _ (by decide) (by decide)), rdF_eq (kk _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) (kk _ (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [semXIR_ite, z4]
    by_cases hmt : m = t
    · rw [decide_eq_true hmt, if_neg bW_ne_zero, if_pos hmt, mul_one]
      exact ePr
    · rw [decide_eq_false hmt, bW_false, if_pos rfl, if_neg hmt,
        mulF_sem hM4 (by decide) (by decide) (by decide) (by decide), ePr,
        rdF_eq (k4 _ (by decide)) (k4 _ (by decide)), d3, l1, ds2]
  have k5 : ∀ r, 15 ≤ r → r ≠ fPr → r ≠ fPr + 1 →
      rd (semXIR I (.ite bZ (.blk []) (mulF fPr fPr fDd)) s4).M r = rd s4.M r := fun r h0 h1 h2 => by
    rw [semXIR_ite]
    split_ifs
    · rw [mulF, sem_blk]; exact mulFC_frame _ _ _ (.inr h0) h1 h2 _
    · rfl
  have hM5 := inv_sem I (P := .ite bZ (.blk []) (mulF fPr fPr fDd)) (s := s4)
    ⟨by simp +decide only [WF], wf_mulF _ _ _ (by decide)⟩ hM4
  generalize semXIR I (.ite bZ (.blk []) (mulF fPr fPr fDd)) s4 = s5 at p5 k5 hM5
  have m5 : rd s5.M bM = toWord m := by
    rw [k5 _ (by decide) (by decide) (by decide), k4 _ (by decide), k3 _ (by decide) (by decide),
      kk _ (by decide) (by decide) (by decide) (by decide) (by decide), hBm]
  obtain ⟨i6, i6f⟩ := incr_sem s5.M hM5 (r := bM) (x := m) (by decide) (by decide) m5
  have e6 : semXIR I (.blk [.op .add bM bM cOne]) s5 = ⟨runPrims [.op .add bM bM cOne] s5.M, s5.o⟩ :=
    rfl
  rw [e6]
  refine ⟨by rw [rdF_eq (i6f _ (by decide)) (i6f _ (by decide)), p5], i6, ?_, ?_,
    inv_runPrims (by simp [Prim.dst, bM]) hM5⟩
  · rw [i6f _ (by decide), k5 _ (by decide) (by decide) (by decide), k4 _ (by decide),
      k3 _ (by decide) (by decide), kk _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hBt]
  · rw [rdF_eq (i6f _ (by decide)) (i6f _ (by decide)),
      rdF_eq (k5 _ (by decide) (by decide) (by decide)) (k5 _ (by decide) (by decide) (by decide)),
      rdF_eq (k4 _ (by decide)) (k4 _ (by decide)),
      rdF_eq (k3 _ (by decide) (by decide)) (k3 _ (by decide) (by decide)),
      rdF_eq (kk _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (kk _ (by decide) (by decide) (by decide) (by decide) (by decide)), hDs]

/-- The constants before `W[t]`'s product: `fPr := 1`, `m := 0`, `bN2 := k`. -/
theorem preW_sem (M : Mem) (hM : Inv M) (k : ℕ) :
    rdF (runPrims [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)] M) fPr = 1 ∧
    rd (runPrims [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)] M) bM =
      toWord 0 ∧
    rd (runPrims [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)] M) bN2 =
      toWord k ∧
    (∀ i, i ≠ fPr → i ≠ fPr + 1 → i ≠ bM → i ≠ bN2 →
      rd (runPrims [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)] M) i =
        rd M i) ∧
    Inv (runPrims [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)] M) := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, ?_, ?_, fun i h1 h2 h3 h4 => rd_runPrims_of_not_writes (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst] <;> omega) _,
    inv_runPrims (by simp [Prim.dst, fPr, bM, bN2]) hM⟩
  · simp only [runPrims, List.foldl, Prim.run, rdF, rdB]
    simp (disch := first | decide | (simp only [size_set, fPr, bM, bN2]; omega) |
      (simp only [fPr, bM, bN2]; omega)) only [rd_set_self, rd_set_ne]
    rfl
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, fPr, bM, bN2]; omega) |
      (simp only [fPr, bM, bN2]; omega)) only [rd_set_self, rd_set_ne]
    rfl
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, fPr, bM, bN2]; omega) |
      (simp only [fPr, bM, bN2]; omega)) only [rd_set_self, rd_set_ne]

/-- **One entry of `W`**: `W[t] := (Π_{m < k} (m = t ? 1 : G t + G m))⁻¹`, `G` the table `DJ`. -/
theorem wtBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {k djb wb t : ℕ} {G : ℕ → F}
    (hk : k < 2 ^ 64) (ht : t < k) (hdjb : regs ≤ djb) (hwb : regs ≤ wb)
    (hdj2 : djb + 2 * k < 2 ^ 64) (hwb2 : wb + 2 * k < 2 ^ 64) (hsz : wb + 2 * k ≤ s.M.size)
    (hG : ∀ m < k, rdF s.M (djb + 2 * m) = G m) (hBt : rd s.M bT = toWord t) :
    rdF (semXIR I (wtBody k djb wb) s).M (wb + 2 * t) =
      (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹ ∧
    rd (semXIR I (wtBody k djb wb) s).M bT = toWord (t + 1) ∧
    (∀ y, regs ≤ y → y ≠ wb + 2 * t → y ≠ wb + 2 * t + 1 →
      rd (semXIR I (wtBody k djb wb) s).M y = rd s.M y) ∧
    Inv (semXIR I (wtBody k djb wb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdjb hwb
  rw [wtBody, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq]
  -- `fDs := DJ[t]`
  obtain ⟨a1, a1f⟩ := addrPs_sem s.M hM.1 (d := bA) (i := bT) (b := djb) (m := 2) (by decide)
    (by decide) (by decide) hBt
  have hM1 : Inv (runPrims (addrPs bA bT djb 2) s.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM
  have e1 : semXIR I (.blk (addrPs bA bT djb 2)) s = ⟨runPrims (addrPs bA bT djb 2) s.M, s.o⟩ := rfl
  rw [e1]
  have z1 := size_runPrims (addrPs bA bT djb 2) s.M
  generalize runPrims (addrPs bA bT djb 2) s.M = M1 at a1 a1f hM1 z1
  obtain ⟨l1, -, l3⟩ := ldF_sem I ⟨M1, s.o⟩ hM1 (d := fDs) (p := bA) (p1 := bA1)
    (x := djb + 2 * t) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a1
    (by simp only [regs]; omega) (by omega)
  have hM2 := inv_sem I (P := ldF fDs bA bA1) (s := ⟨M1, s.o⟩)
    (by simp +decide only [ldF, WF, Prim.dst, fDs, bA1, and_true]) hM1
  have z2 := size_sem I (ldF fDs bA bA1) ⟨M1, s.o⟩
  have k2 : ∀ r, r ≠ fDs → r ≠ fDs + 1 → r ≠ bA1 → r ≠ bA → r ≠ bK →
      rd (semXIR I (ldF fDs bA bA1) ⟨M1, s.o⟩).M r = rd s.M r := fun r a b c d e =>
    (l3 r a b c).trans (a1f r d e)
  have gt : rdF (semXIR I (ldF fDs bA bA1) ⟨M1, s.o⟩).M fDs = G t := by
    rw [l1, rdF_eq (a1f _ (by simp only [bA]; omega) (by simp only [bK]; omega))
      (a1f _ (by simp only [bA]; omega) (by simp only [bK]; omega)), hG t ht]
  generalize semXIR I (ldF fDs bA bA1) ⟨M1, s.o⟩ = s2 at l1 l3 hM2 z2 k2 gt
  -- the product
  obtain ⟨q1, q2, q3, q4, hM3⟩ := preW_sem s2.M hM2 k
  have e3 : semXIR I (.blk [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)])
      s2 = ⟨runPrims [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)] s2.M,
        s2.o⟩ := rfl
  rw [e3]
  have z3 := size_runPrims [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)]
    s2.M
  generalize runPrims [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)] s2.M =
    M3 at q1 q2 q3 q4 hM3 z3
  have k3 : ∀ r, r ≠ fPr → r ≠ fPr + 1 → r ≠ bM → r ≠ bN2 → r ≠ fDs → r ≠ fDs + 1 → r ≠ bA1 →
      r ≠ bA → r ≠ bK → rd M3 r = rd s.M r := fun r a b c d e f g h i =>
    (q4 r a b c d).trans (k2 r e f g h i)
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧
    rdF st.M fPr = (∏ m ∈ range j, if m = t then 1 else G t + G m) ∧ rd st.M bM = toWord j ∧
    rd st.M bT = toWord t ∧ rdF st.M fDs = G t ∧ ∀ y, regs ≤ y → rd st.M y = rd s.M y
  have hQ := loopK_run I (c := bC2) (n := bN2) (K := k) (wInner djb) Q ⟨M3, s2.o⟩ hM3
    (by decide) (by decide) (by decide) q3 hk ?_ ?_
  rotate_left
  · have ef : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord k) M3) i = rd M3 i :=
      fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
    refine ⟨inv_of_frame hM3 (size_entryK ..) fun i hi => ef i (by simp only [bC2]; omega)
      (by simp only [cTmp]; omega), by rw [size_entryK, z3, z2, z1], ?_, ?_, ?_, ?_,
      fun y hy => ?_⟩
    · rw [rdF_eq (ef _ (by decide) (by decide)) (ef _ (by decide) (by decide)), q1, prod_range_zero]
    · rw [ef _ (by decide) (by decide), q2]
    · rw [ef _ (by decide) (by decide), q4 _ (by decide) (by decide) (by decide) (by decide),
        k2 _ (by decide) (by decide) (by decide) (by decide) (by decide), hBt]
    · rw [rdF_eq (ef _ (by decide) (by decide)) (ef _ (by decide) (by decide)),
        rdF_eq (q4 _ (by decide) (by decide) (by decide) (by decide))
          (q4 _ (by decide) (by decide) (by decide) (by decide)), gt]
    · simp only [regs] at hy
      rw [ef _ (by simp only [bC2]; omega) (by simp only [cTmp]; omega),
        k3 _ (by simp only [fPr]; omega) (by simp only [fPr]; omega) (by simp only [bM]; omega)
          (by simp only [bN2]; omega) (by simp only [fDs]; omega) (by simp only [fDs]; omega)
          (by simp only [bA1]; omega) (by simp only [bA]; omega) (by simp only [bK]; omega)]
  · rintro j st hj ⟨hM', hz, hP, hm, hb, hd, hH⟩
    obtain ⟨w1, w2, w3, w4, hM''⟩ := wInner_sem I st hM' (djb := djb) (m := j) (t := t) (dt := G t)
      (by simp only [regs]; omega) (by omega) (by omega) (by omega) hm hb hd
    have hrs : ∀ y, regs ≤ y → rd (semXIR I (wInner djb) st).M y = rd st.M y :=
      fun y hy => hframe I _ st (lo_wInner djb) y hy
    refine ⟨inv_decS hM'' (by decide), by rw [size_decS, size_sem, hz], ?_, ?_, ?_, ?_,
      fun y hy => ?_⟩
    · rw [rdF_decS _ (by decide) (by decide), w1, hP, prod_range_succ,
        rdF_eq (hH _ (by simp only [regs]; omega)) (hH _ (by simp only [regs]; omega)), hG j hj]
    · rw [rd_decS (by decide), w2]
    · rw [rd_decS (by decide), w3]
    · rw [rdF_decS _ (by decide) (by decide), w4]
    · rw [rd_decS (by simp only [bC2, regs] at hy ⊢; omega), hrs y hy, hH y hy]
  obtain ⟨Q1, Qz, Q2, -, Q4, -, Q6⟩ := hQ
  generalize semXIR I (.loopK bC2 bN2 (toWord k) (wInner djb)) ⟨M3, s2.o⟩ = s4 at Q1 Qz Q2 Q4 Q6
  -- the inverse
  have v5 := invF_sem (I := I) (s := s4) Q1 (d := fIv) (a := fPr) (by decide) (by decide)
    (by decide)
  have hM5 := inv_sem I (wf_invF fIv fPr (by decide)) Q1
  have k5 : ∀ r, 19 ≤ r → r ≠ fIv → r ≠ fIv + 1 → rd (semXIR I (invF fIv fPr) s4).M r = rd s4.M r :=
    fun r h0 h1 h2 => by rw [invF, sem_blk]; exact invFC_frame _ _ (.inr h0) h1 h2 _
  have z5 := size_sem I (invF fIv fPr) s4
  rw [Q2] at v5
  generalize semXIR I (invF fIv fPr) s4 = s5 at v5 hM5 k5 z5
  -- `bA := wb + 2t`
  have t5 : rd s5.M bT = toWord t := (k5 _ (by decide) (by decide) (by decide)).trans Q4
  obtain ⟨a6, a6f⟩ := addrPs_sem s5.M hM5.1 (d := bA) (i := bT) (b := wb) (m := 2) (by decide)
    (by decide) (by decide) t5
  have hM6 : Inv (runPrims (addrPs bA bT wb 2) s5.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM5
  have e6 : semXIR I (.blk (addrPs bA bT wb 2)) s5 = ⟨runPrims (addrPs bA bT wb 2) s5.M, s5.o⟩ := rfl
  rw [e6]
  have z6 := size_runPrims (addrPs bA bT wb 2) s5.M
  have v6 : rdF (runPrims (addrPs bA bT wb 2) s5.M) fIv =
      (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹ := by
    rw [rdF_eq (a6f _ (by decide) (by decide)) (a6f _ (by decide) (by decide)), v5]
  generalize runPrims (addrPs bA bT wb 2) s5.M = M6 at a6 a6f hM6 z6 v6
  -- `W[t] := fIv`
  have hz : wb + 2 * t + 1 < M6.size := by rw [z6, z5, Qz]; omega
  obtain ⟨g1, g2, hM7⟩ := stF_sem I ⟨M6, s5.o⟩ hM6 (p := bA) (p1 := bA1) (v := fIv)
    (x := wb + 2 * t) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) a6 (by simp only [regs]; omega) (by omega) hz
  have t7 : rd (semXIR I (stF bA bA1 fIv) ⟨M6, s5.o⟩).M bT = toWord t := by
    rw [g2 _ (by simp only [bT]; omega) (by simp only [bT]; omega) (by decide) (by decide),
      a6f _ (by decide) (by decide), t5]
  generalize semXIR I (stF bA bA1 fIv) ⟨M6, s5.o⟩ = s7 at g1 g2 hM7 t7
  obtain ⟨i8, i8f⟩ := incr_sem s7.M hM7 (r := bT) (x := t) (by decide) (by decide) t7
  have e8 : semXIR I (.blk [.op .add bT bT cOne]) s7 = ⟨runPrims [.op .add bT bT cOne] s7.M, s7.o⟩ :=
    rfl
  rw [e8]
  refine ⟨?_, i8, fun y hy h1' h2' => ?_, inv_runPrims (by simp [Prim.dst, bT]) hM7⟩
  · rw [rdF_eq (i8f _ (by simp only [bT]; omega)) (i8f _ (by simp only [bT]; omega)), g1, v6]
  · simp only [regs] at hy
    rw [i8f _ (by simp only [bT]; omega), g2 y h1' h2' (by simp only [bA1]; omega)
      (by simp only [cTmp]; omega), a6f _ (by simp only [bA]; omega) (by simp only [bK]; omega),
      k5 _ (by omega) (by simp only [fIv]; omega) (by simp only [fIv]; omega),
      Q6 y (by simp only [regs]; omega)]

/-- **The table `W`**: `W[t] = (Π_{m<k} (m = t ? 1 : G t + G m))⁻¹` at `wb + 2t`, `G` the table
`DJ` at `djb`; nothing else on the heap changes. -/
theorem wtIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k djb wb : ℕ} {G : ℕ → F}
    (hk : k < 2 ^ 64) (hdjb : regs ≤ djb) (hwb : regs ≤ wb) (hdj2 : djb + 2 * k < 2 ^ 64)
    (hwb2 : wb + 2 * k < 2 ^ 64) (hsz : wb + 2 * k ≤ s.M.size)
    (hdW : djb + 2 * k ≤ wb ∨ wb + 2 * k ≤ djb) (hG : ∀ m < k, rdF s.M (djb + 2 * m) = G m) :
    (∀ t < k, rdF (semXIR I (wtIR k djb wb) s).M (wb + 2 * t) =
      (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + 2 * k ≤ y) →
      rd (semXIR I (wtIR k djb wb) s).M y = rd s.M y) ∧
    Inv (semXIR I (wtIR k djb wb) s).M := by
  rw [wtIR, semXIR_seq]
  obtain ⟨p1, p2, p3, hM1⟩ := pre2_sem s.M hM (r := bT) (n := bN1) 0 (toWord k)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have e1 : semXIR I (.blk [.const bT 0, .const bN1 (toWord k)]) s =
      ⟨runPrims [.const bT 0, .const bN1 (toWord k)] s.M, s.o⟩ := rfl
  rw [e1]
  have z1 := size_runPrims [.const bT 0, .const bN1 (toWord k)] s.M
  replace p1 := p1.trans toWord_zero'.symm
  generalize runPrims [.const bT 0, .const bN1 (toWord k)] s.M = M1 at p1 p2 p3 hM1 z1
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bT = toWord j ∧
    (∀ t < j, rdF st.M (wb + 2 * t) = (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + 2 * j ≤ y) → rd st.M y = rd s.M y)
  have hfin := loopK_run I (c := bC1) (n := bN1) (K := k) (wtBody k djb wb) P ⟨M1, s.o⟩ hM1
    (by decide) (by decide) (by decide) p2 hk ?_ ?_
  · exact ⟨hfin.2.2.2.1, fun y hy hy2 => hfin.2.2.2.2 y hy hy2, hfin.1⟩
  · refine ⟨inv_of_frame hM1 (size_entryK ..) fun i hi => entryK_frame _ (by simp only [bC1]; omega)
      (by simp only [cTmp]; omega), by rw [size_entryK, z1], ?_,
      fun t ht => absurd ht (Nat.not_lt_zero _), fun y hy _ => ?_⟩
    · rw [entryK_frame _ (by decide) (by decide), p1]
    · simp only [regs] at hy
      rw [entryK_frame _ (by simp only [bC1]; omega) (by simp only [cTmp]; omega),
        p3 _ (by simp only [bT]; omega) (by simp only [bN1]; omega)]
  · rintro j st hj ⟨hM', hz, hT', hW, hH⟩
    have hG' : ∀ m < k, rdF st.M (djb + 2 * m) = G m := fun m hm => by
      rw [rdF_eq (hH _ (by simp only [regs] at hdjb ⊢; omega) (by omega))
        (hH _ (by simp only [regs] at hdjb ⊢; omega) (by omega)), hG m hm]
    obtain ⟨b1, b2, b3, hM2⟩ := wtBody_sem I st hM' hk hj hdjb hwb hdj2 hwb2 (by omega) hG' hT'
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz], ?_, fun t ht => ?_,
      fun y hy hy2 => ?_⟩
    · rw [rd_decS (by decide), b2]
    · rw [rdF_decS _ (by simp only [bC1, regs] at hwb ⊢; omega)
        (by simp only [bC1, regs] at hwb ⊢; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [rdF_eq (b3 _ (by simp only [regs] at hwb ⊢; omega) (by omega) (by omega))
          (b3 _ (by simp only [regs] at hwb ⊢; omega) (by omega) (by omega)), hW t ht]
      · exact b1
    · rw [rd_decS (by simp only [bC1, regs] at hy ⊢; omega), b3 y hy (by omega) (by omega),
        hH y hy (by omega)]

/-! ## One target's `E` row -/

/-- `rd` frame of the field routines on registers at or above `19` other than the result. -/
theorem fr_mulF {I : Array Word} {s : St} {d a b r : ℕ} (h0 : 15 ≤ r) (h1 : r ≠ d) (h2 : r ≠ d + 1) :
    rd (semXIR I (mulF d a b) s).M r = rd s.M r := by
  rw [mulF, sem_blk]; exact mulFC_frame _ _ _ (.inr h0) h1 h2 _
theorem fr_addF {I : Array Word} {s : St} {d a b r : ℕ} (h1 : r ≠ d) (h2 : r ≠ d + 1) :
    rd (semXIR I (addF d a b) s).M r = rd s.M r := addFC_frame _ _ _ h1 h2 _
theorem fr_invF {I : Array Word} {s : St} {d a r : ℕ} (h0 : 19 ≤ r) (h1 : r ≠ d) (h2 : r ≠ d + 1) :
    rd (semXIR I (invF d a) s).M r = rd s.M r := by
  rw [invF, sem_blk]; exact invFC_frame _ _ (.inr h0) h1 h2 _

/-- **One entry of the `E` row**: `E[t] := W[t] · (D(s) + DJ[t])⁻¹`, `ℓ *= D(s) + DJ[t]`. -/
theorem eBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {djb wb eb t : ℕ} {ds lp g w : F}
    (hdjb : regs ≤ djb) (hwb : regs ≤ wb) (heb : regs ≤ eb) (hdj2 : djb + 2 * t + 1 < 2 ^ 64)
    (hwb2 : wb + 2 * t + 1 < 2 ^ 64) (heb2 : eb + 2 * t + 1 < 2 ^ 64)
    (hsz : eb + 2 * t + 1 < s.M.size) (hBt : rd s.M bT = toWord t) (hDs : rdF s.M fDs = ds)
    (hLp : rdF s.M fLp = lp) (hG : rdF s.M (djb + 2 * t) = g) (hW : rdF s.M (wb + 2 * t) = w) :
    rdF (semXIR I (eBody djb wb eb) s).M (eb + 2 * t) = w * (ds + g)⁻¹ ∧
    rdF (semXIR I (eBody djb wb eb) s).M fLp = lp * (ds + g) ∧
    rd (semXIR I (eBody djb wb eb) s).M bT = toWord (t + 1) ∧
    rdF (semXIR I (eBody djb wb eb) s).M fDs = ds ∧
    (∀ y, regs ≤ y → y ≠ eb + 2 * t → y ≠ eb + 2 * t + 1 →
      rd (semXIR I (eBody djb wb eb) s).M y = rd s.M y) ∧
    Inv (semXIR I (eBody djb wb eb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdjb hwb heb
  rw [eBody]
  simp only [semXIR_seq]
  -- `fX := DJ[t]`
  obtain ⟨a1, a1f⟩ := addrPs_sem s.M hM.1 (d := bA) (i := bT) (b := djb) (m := 2) (by decide)
    (by decide) (by decide) hBt
  have hM1 : Inv (runPrims (addrPs bA bT djb 2) s.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM
  have e1 : semXIR I (.blk (addrPs bA bT djb 2)) s = ⟨runPrims (addrPs bA bT djb 2) s.M, s.o⟩ := rfl
  rw [e1]
  have z1 := size_runPrims (addrPs bA bT djb 2) s.M
  generalize runPrims (addrPs bA bT djb 2) s.M = M1 at a1 a1f hM1 z1
  have hH1 : ∀ y, regs ≤ y → rd M1 y = rd s.M y := fun y hy =>
    a1f y (by simp only [regs] at hy; simp only [bA]; omega)
      (by simp only [regs] at hy; simp only [bK]; omega)
  obtain ⟨l1, -, l3⟩ := ldF_sem I ⟨M1, s.o⟩ hM1 (d := fX) (p := bA) (p1 := bA1)
    (x := djb + 2 * t) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a1
    (by simp only [regs]; omega) hdj2
  rw [rdF_eq (hH1 _ (by simp only [regs]; omega)) (hH1 _ (by simp only [regs]; omega)), hG] at l1
  have hM2 := inv_sem I (P := ldF fX bA bA1) (s := ⟨M1, s.o⟩)
    (by simp +decide only [ldF, WF, Prim.dst, fX, bA1, and_true]) hM1
  have z2 := size_sem I (ldF fX bA bA1) ⟨M1, s.o⟩
  have k2 : ∀ r, r ≠ fX → r ≠ fX + 1 → r ≠ bA1 → r ≠ bA → r ≠ bK →
      rd (semXIR I (ldF fX bA bA1) ⟨M1, s.o⟩).M r = rd s.M r := fun r a b c d e =>
    (l3 r a b c).trans (a1f r d e)
  generalize semXIR I (ldF fX bA bA1) ⟨M1, s.o⟩ = s2 at l1 l3 hM2 z2 k2
  -- `fDd := D(s) + DJ[t]`, `ℓ *= fDd`, `fIv := fDd⁻¹`
  have d3 := addF_sem (I := I) (s := s2) hM2 (d := fDd) (a := fDs) (b := fX) (by decide)
    (by decide) (by decide)
  rw [l1, rdF_eq (k2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)), hDs] at d3
  have hM3 := inv_sem I (wf_addF fDd fDs fX (by decide)) hM2
  have z3 := size_sem I (addF fDd fDs fX) s2
  have k3 : ∀ r, r ≠ fDd → r ≠ fDd + 1 → r ≠ fX → r ≠ fX + 1 → r ≠ bA1 → r ≠ bA → r ≠ bK →
      rd (semXIR I (addF fDd fDs fX) s2).M r = rd s.M r := fun r a b c d e f g =>
    (fr_addF a b).trans (k2 r c d e f g)
  generalize semXIR I (addF fDd fDs fX) s2 = s3 at d3 hM3 z3 k3
  have m4 := mulF_sem (I := I) (s := s3) hM3 (d := fLp) (a := fLp) (b := fDd) (by decide)
    (by decide) (by decide) (by decide)
  rw [d3, rdF_eq (k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) (k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)), hLp] at m4
  have hM4 := inv_sem I (wf_mulF fLp fLp fDd (by decide)) hM3
  have z4 := size_sem I (mulF fLp fLp fDd) s3
  have k4 : ∀ r, 15 ≤ r → r ≠ fLp → r ≠ fLp + 1 →
      rd (semXIR I (mulF fLp fLp fDd) s3).M r = rd s3.M r := fun r h0 a b => fr_mulF h0 a b
  have dd4 : rdF (semXIR I (mulF fLp fLp fDd) s3).M fDd = ds + g := by
    rw [rdF_eq (k4 _ (by decide) (by decide) (by decide)) (k4 _ (by decide) (by decide)
      (by decide)), d3]
  generalize semXIR I (mulF fLp fLp fDd) s3 = s4 at m4 hM4 z4 k4 dd4
  have v5 := invF_sem (I := I) (s := s4) hM4 (d := fIv) (a := fDd) (by decide) (by decide)
    (by decide)
  rw [dd4] at v5
  have hM5 := inv_sem I (wf_invF fIv fDd (by decide)) hM4
  have z5 := size_sem I (invF fIv fDd) s4
  have k5 : ∀ r, 19 ≤ r → r ≠ fIv → r ≠ fIv + 1 →
      rd (semXIR I (invF fIv fDd) s4).M r = rd s4.M r := fun r h0 a b => fr_invF h0 a b
  generalize semXIR I (invF fIv fDd) s4 = s5 at v5 hM5 z5 k5
  -- the register facts so far, against `s`
  have K5 : ∀ r, 19 ≤ r → r ≠ fIv → r ≠ fIv + 1 → r ≠ fLp → r ≠ fLp + 1 → r ≠ fDd → r ≠ fDd + 1 →
      r ≠ fX → r ≠ fX + 1 → r ≠ bA1 → r ≠ bA → r ≠ bK → rd s5.M r = rd s.M r :=
    fun r h0 a b c d e f g h i j k => (k5 r h0 a b).trans ((k4 r (by omega) c d).trans
      (k3 r e f g h i j k))
  have Lp5 : rdF s5.M fLp = lp * (ds + g) := by
    rw [rdF_eq (k5 _ (by decide) (by decide) (by decide)) (k5 _ (by decide) (by decide)
      (by decide)), m4]
  -- `fX := W[t]`
  have t5 : rd s5.M bT = toWord t := (K5 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans hBt
  have hH5 : ∀ y, regs ≤ y → rd s5.M y = rd s.M y := fun y hy => by
    simp only [regs] at hy
    rw [K5 y (by omega) (by simp only [fIv]; omega) (by simp only [fIv]; omega)
      (by simp only [fLp]; omega) (by simp only [fLp]; omega) (by simp only [fDd]; omega)
      (by simp only [fDd]; omega) (by simp only [fX]; omega) (by simp only [fX]; omega)
      (by simp only [bA1]; omega) (by simp only [bA]; omega) (by simp only [bK]; omega)]
  obtain ⟨a6, a6f⟩ := addrPs_sem s5.M hM5.1 (d := bA) (i := bT) (b := wb) (m := 2) (by decide)
    (by decide) (by decide) t5
  have hM6 : Inv (runPrims (addrPs bA bT wb 2) s5.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM5
  have e6 : semXIR I (.blk (addrPs bA bT wb 2)) s5 = ⟨runPrims (addrPs bA bT wb 2) s5.M, s5.o⟩ := rfl
  rw [e6]
  have z6 := size_runPrims (addrPs bA bT wb 2) s5.M
  generalize runPrims (addrPs bA bT wb 2) s5.M = M6 at a6 a6f hM6 z6
  obtain ⟨l7, -, l7f⟩ := ldF_sem I ⟨M6, s5.o⟩ hM6 (d := fX) (p := bA) (p1 := bA1)
    (x := wb + 2 * t) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a6
    (by simp only [regs]; omega) hwb2
  rw [rdF_eq (a6f _ (by simp only [bA]; omega) (by simp only [bK]; omega))
    (a6f _ (by simp only [bA]; omega) (by simp only [bK]; omega)),
    rdF_eq (hH5 _ (by simp only [regs]; omega)) (hH5 _ (by simp only [regs]; omega)), hW] at l7
  have hM7 := inv_sem I (P := ldF fX bA bA1) (s := ⟨M6, s5.o⟩)
    (by simp +decide only [ldF, WF, Prim.dst, fX, bA1, and_true]) hM6
  have z7 := size_sem I (ldF fX bA bA1) ⟨M6, s5.o⟩
  have k7 : ∀ r, r ≠ fX → r ≠ fX + 1 → r ≠ bA1 → r ≠ bA → r ≠ bK →
      rd (semXIR I (ldF fX bA bA1) ⟨M6, s5.o⟩).M r = rd s5.M r := fun r a b c d e =>
    (l7f r a b c).trans (a6f r d e)
  generalize semXIR I (ldF fX bA bA1) ⟨M6, s5.o⟩ = s7 at l7 l7f hM7 z7 k7
  -- `fEt := W[t] · fIv`
  have m8 := mulF_sem (I := I) (s := s7) hM7 (d := fEt) (a := fX) (b := fIv) (by decide)
    (by decide) (by decide) (by decide)
  rw [l7, rdF_eq (k7 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (k7 _ (by decide) (by decide) (by decide) (by decide) (by decide)), v5] at m8
  have hM8 := inv_sem I (wf_mulF fEt fX fIv (by decide)) hM7
  have z8 := size_sem I (mulF fEt fX fIv) s7
  have k8 : ∀ r, 15 ≤ r → r ≠ fEt → r ≠ fEt + 1 → r ≠ fX → r ≠ fX + 1 → r ≠ bA1 → r ≠ bA → r ≠ bK →
      rd (semXIR I (mulF fEt fX fIv) s7).M r = rd s5.M r := fun r h0 a b c d e f g =>
    (fr_mulF h0 a b).trans (k7 r c d e f g)
  generalize semXIR I (mulF fEt fX fIv) s7 = s8 at m8 hM8 z8 k8
  -- `E[t] := fEt`
  have t8 : rd s8.M bT = toWord t := (k8 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans t5
  obtain ⟨a9, a9f⟩ := addrPs_sem s8.M hM8.1 (d := bA) (i := bT) (b := eb) (m := 2) (by decide)
    (by decide) (by decide) t8
  have hM9 : Inv (runPrims (addrPs bA bT eb 2) s8.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM8
  have e9 : semXIR I (.blk (addrPs bA bT eb 2)) s8 = ⟨runPrims (addrPs bA bT eb 2) s8.M, s8.o⟩ := rfl
  rw [e9]
  have z9 := size_runPrims (addrPs bA bT eb 2) s8.M
  have E9 : rdF (runPrims (addrPs bA bT eb 2) s8.M) fEt = w * (ds + g)⁻¹ := by
    rw [rdF_eq (a9f _ (by decide) (by decide)) (a9f _ (by decide) (by decide)), m8]
  generalize runPrims (addrPs bA bT eb 2) s8.M = M9 at a9 a9f hM9 z9 E9
  have hz : eb + 2 * t + 1 < M9.size := by
    rw [z9, z8, z7, z6, z5, z4, z3, z2]; show _ < M1.size; rw [z1]; exact hsz
  obtain ⟨g1, g2, hM10⟩ := stF_sem I ⟨M9, s8.o⟩ hM9 (p := bA) (p1 := bA1) (v := fEt)
    (x := eb + 2 * t) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) a9 (by simp only [regs]; omega) heb2 hz
  -- the registers after the store, against `s8`
  have K10 : ∀ r, r < regs → r ≠ bA1 → r ≠ cTmp → r ≠ bA → r ≠ bK →
      rd (semXIR I (stF bA bA1 fEt) ⟨M9, s8.o⟩).M r = rd s8.M r := fun r hr a b c d => by
    simp only [regs] at hr
    rw [g2 r (by omega) (by omega) a b,
      a9f r c d]
  generalize semXIR I (stF bA bA1 fEt) ⟨M9, s8.o⟩ = s10 at g1 g2 hM10 K10
  have t10 : rd s10.M bT = toWord t := (K10 _ (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans t8
  obtain ⟨i11, i11f⟩ := incr_sem s10.M hM10 (r := bT) (x := t) (by decide) (by decide) t10
  have e11 : semXIR I (.blk [.op .add bT bT cOne]) s10 =
      ⟨runPrims [.op .add bT bT cOne] s10.M, s10.o⟩ := rfl
  rw [e11]
  -- `fLp`, `fDs` from `s5` to the end
  have back : ∀ r, 15 ≤ r → r < regs → r ≠ bT → r ≠ bA1 → r ≠ cTmp → r ≠ bA → r ≠ bK →
      r ≠ fEt → r ≠ fEt + 1 → r ≠ fX → r ≠ fX + 1 →
      rd (runPrims [.op .add bT bT cOne] s10.M) r = rd s5.M r := fun r h0 hr a b c d e f g h i =>
    (i11f r a).trans ((K10 r hr b c d e).trans (k8 r h0 f g h i b d e))
  refine ⟨?_, ?_, i11, ?_, fun y hy h1' h2' => ?_, inv_runPrims (by simp [Prim.dst, bT]) hM10⟩
  · rw [rdF_eq (i11f _ (by simp only [bT]; omega)) (i11f _ (by simp only [bT]; omega)), g1, E9]
  · rw [rdF_eq (back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
      (back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)), Lp5]
  · rw [rdF_eq (back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
      (back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)),
      rdF_eq (K5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (K5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)), hDs]
  · simp only [regs] at hy
    rw [i11f _ (by simp only [bT]; omega), g2 y h1' h2' (by simp only [bA1]; omega)
      (by simp only [cTmp]; omega), a9f _ (by simp only [bA]; omega) (by simp only [bK]; omega),
      k8 _ (by omega) (by simp only [fEt]; omega) (by simp only [fEt]; omega)
        (by simp only [fX]; omega) (by simp only [fX]; omega) (by simp only [bA1]; omega)
        (by simp only [bA]; omega) (by simp only [bK]; omega), hH5 y (by simp only [regs]; omega)]

/-! ## One coordinate's accumulation -/

/-- `d += M[r]`. -/
theorem addOp_sem (M : Mem) (hs : regs ≤ M.size) {d r x y : ℕ} (hd : d < regs)
    (hx : rd M d = toWord x) (hy : rd M r = toWord y) :
    rd (runPrims [.op .add d d r] M) d = toWord (x + y) ∧
    ∀ j, j ≠ d → rd (runPrims [.op .add d d r] M) j = rd M j := by
  refine ⟨?_, fun j hj => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hj) _⟩
  simp only [runPrims, List.foldl, Prim.run]
  rw [rd_set_self (by simp only [regs] at hs hd; omega), hx, hy, add_toWord]

theorem lo_aBody (jb eb cb cs : ℕ) : Lo (aBody jb eb cb cs) := by
  have h1 : Lo (mulF fPr fY fX) := lo_mulF (by decide)
  have h2 : Lo (addF fAc fAc fPr) := lo_addF (by decide)
  simp [aBody, Lo, ldF, addrPs, Prim.dst, regs, bK, bA, bJ, bA1, bT, h1, h2]
  simp [fY, fX]

theorem wf_aBody (jb eb cb cs : ℕ) : WF (aBody jb eb cb cs) := by
  simp +decide only [aBody, addrPs, ldF, WF, Prim.dst, wfF_mul, wfF_add, bA, bK, bA1, bJ, fY, fX,
    fPr, fAc, bT, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true,
    List.cons_append, List.nil_append]

/-- **One term of `acc`**: `acc += y(J_t) · E[t]`, `y(j)` at `cb + cs·j + 2c`. -/
theorem aBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {jb eb cb cs t c x : ℕ} {acc : F}
    (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb) (hjb2 : jb + t < 2 ^ 64)
    (heb2 : eb + 2 * t + 1 < 2 ^ 64) (hcb2 : cb + cs * x + 2 * c + 1 < 2 ^ 64)
    (hBt : rd s.M bT = toWord t) (hCo : rd s.M bCo = toWord (2 * c)) (hAc : rdF s.M fAc = acc)
    (hJ : rd s.M (jb + t) = toWord x) :
    rdF (semXIR I (aBody jb eb cb cs) s).M fAc =
      acc + rdF s.M (cb + cs * x + 2 * c) * rdF s.M (eb + 2 * t) ∧
    rd (semXIR I (aBody jb eb cb cs) s).M bT = toWord (t + 1) ∧
    Inv (semXIR I (aBody jb eb cb cs) s).M := by
  have hs := hM.1
  simp only [regs] at hs hjb heb hcb
  have hH : ∀ (P : XIR) (s' : St), Lo P → ∀ y, regs ≤ y → rd (semXIR I P s').M y = rd s'.M y :=
    fun P s' h y hy => hframe I P s' h y hy
  rw [aBody]
  simp only [semXIR_seq]
  obtain ⟨a1, a1f⟩ := addrPs_sem s.M hM.1 (d := bA) (i := bT) (b := jb) (m := 1) (by decide)
    (by decide) (by decide) hBt
  have hM1 : Inv (runPrims (addrPs bA bT jb 1) s.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM
  have e1 : semXIR I (.blk (addrPs bA bT jb 1)) s = ⟨runPrims (addrPs bA bT jb 1) s.M, s.o⟩ := rfl
  rw [e1]
  generalize runPrims (addrPs bA bT jb 1) s.M = M1 at a1 a1f hM1
  have hH1 : ∀ y, regs ≤ y → rd M1 y = rd s.M y := fun y hy =>
    a1f y (by simp only [regs] at hy; simp only [bA]; omega)
      (by simp only [regs] at hy; simp only [bK]; omega)
  obtain ⟨l2, l2f⟩ := bload_sem I ⟨M1, s.o⟩ hM1 (d := bJ) (a := bA) (x := jb + 1 * t) (by decide)
    a1 (by omega)
  rw [hH1 _ (by simp only [regs]; omega), Nat.one_mul, hJ] at l2
  have hM2 := inv_sem I (P := .load bJ bA) (s := ⟨M1, s.o⟩) (by simp +decide only [WF, bJ]) hM1
  have k2 : ∀ r, r ≠ bJ → r ≠ bA → r ≠ bK → rd (semXIR I (.load bJ bA) ⟨M1, s.o⟩).M r = rd s.M r :=
    fun r a b c => (l2f r a).trans (a1f r b c)
  generalize semXIR I (.load bJ bA) ⟨M1, s.o⟩ = s2 at l2 l2f hM2 k2
  -- `bJ := cb + cs·x + 2c`
  have hs2 := hM2.1
  obtain ⟨c3, c3f⟩ := addrPs_sem s2.M hs2 (d := bJ) (i := bJ) (b := cb) (m := cs) (by decide)
    (by decide) (by decide) l2
  obtain ⟨c4, c4f⟩ := addOp_sem (runPrims (addrPs bJ bJ cb cs) s2.M) (by rw [size_runPrims]; exact hs2)
    (d := bJ) (r := bCo) (x := cb + cs * x) (y := 2 * c) (by decide) c3
    ((c3f _ (by decide) (by decide)).trans ((k2 _ (by decide) (by decide) (by decide)).trans hCo))
  have e3 : semXIR I (.blk (addrPs bJ bJ cb cs ++ [.op .add bJ bJ bCo])) s2 =
      ⟨runPrims [.op .add bJ bJ bCo] (runPrims (addrPs bJ bJ cb cs) s2.M), s2.o⟩ := by
    show (⟨runPrims _ s2.M, s2.o⟩ : St) = _; rw [runPrims_append]
  rw [e3]
  have hM3 : Inv (runPrims [.op .add bJ bJ bCo] (runPrims (addrPs bJ bJ cb cs) s2.M)) :=
    inv_runPrims (by simp [Prim.dst, bJ]) (inv_runPrims (by simp [addrPs, Prim.dst, bJ, bK]) hM2)
  have k3 : ∀ r, r ≠ bJ → r ≠ bK →
      rd (runPrims [.op .add bJ bJ bCo] (runPrims (addrPs bJ bJ cb cs) s2.M)) r = rd s2.M r :=
    fun r a b => (c4f r a).trans (c3f r a b)
  generalize runPrims [.op .add bJ bJ bCo] (runPrims (addrPs bJ bJ cb cs) s2.M) = M3 at c4 c4f hM3 k3
  -- `fY := y(J_t)`
  obtain ⟨l5, -, l5f⟩ := ldF_sem I ⟨M3, s2.o⟩ hM3 (d := fY) (p := bJ) (p1 := bA1)
    (x := cb + cs * x + 2 * c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) c4 (by simp only [regs]; omega) hcb2
  have hy : rdF (semXIR I (ldF fY bJ bA1) ⟨M3, s2.o⟩).M fY = rdF s.M (cb + cs * x + 2 * c) := by
    rw [l5, rdF_eq (k3 _ (by simp only [bJ]; omega) (by simp only [bK]; omega))
      (k3 _ (by simp only [bJ]; omega) (by simp only [bK]; omega)),
      rdF_eq (k2 _ (by simp only [bJ]; omega) (by simp only [bA]; omega) (by simp only [bK]; omega))
      (k2 _ (by simp only [bJ]; omega) (by simp only [bA]; omega) (by simp only [bK]; omega))]
  have hM5 := inv_sem I (P := ldF fY bJ bA1) (s := ⟨M3, s2.o⟩)
    (by simp +decide only [ldF, WF, Prim.dst, fY, bA1, and_true]) hM3
  have k5 : ∀ r, r ≠ fY → r ≠ fY + 1 → r ≠ bA1 → r ≠ bJ → r ≠ bA → r ≠ bK →
      rd (semXIR I (ldF fY bJ bA1) ⟨M3, s2.o⟩).M r = rd s.M r := fun r a b c d e f =>
    (l5f r a b c).trans ((k3 r d f).trans (k2 r d e f))
  generalize semXIR I (ldF fY bJ bA1) ⟨M3, s2.o⟩ = s5 at hy hM5 k5 l5f
  -- `fX := E[t]`
  have t5 : rd s5.M bT = toWord t := (k5 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hBt
  obtain ⟨a6, a6f⟩ := addrPs_sem s5.M hM5.1 (d := bA) (i := bT) (b := eb) (m := 2) (by decide)
    (by decide) (by decide) t5
  have e6 : semXIR I (.blk (addrPs bA bT eb 2)) s5 = ⟨runPrims (addrPs bA bT eb 2) s5.M, s5.o⟩ := rfl
  rw [e6]
  have hM6 : Inv (runPrims (addrPs bA bT eb 2) s5.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM5
  generalize runPrims (addrPs bA bT eb 2) s5.M = M6 at a6 a6f hM6
  obtain ⟨l7, -, l7f⟩ := ldF_sem I ⟨M6, s5.o⟩ hM6 (d := fX) (p := bA) (p1 := bA1)
    (x := eb + 2 * t) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a6
    (by simp only [regs]; omega) heb2
  have he : rdF (semXIR I (ldF fX bA bA1) ⟨M6, s5.o⟩).M fX = rdF s.M (eb + 2 * t) := by
    have hx5 : ∀ y, regs ≤ y → rd s5.M y = rd s.M y := fun y hy => by
      simp only [regs] at hy
      exact k5 y (by simp only [fY]; omega) (by simp only [fY]; omega) (by simp only [bA1]; omega)
        (by simp only [bJ]; omega) (by simp only [bA]; omega) (by simp only [bK]; omega)
    rw [l7, rdF_eq (a6f _ (by simp only [bA]; omega) (by simp only [bK]; omega))
      (a6f _ (by simp only [bA]; omega) (by simp only [bK]; omega)),
      rdF_eq (hx5 _ (by simp only [regs]; omega)) (hx5 _ (by simp only [regs]; omega))]
  have hM7 := inv_sem I (P := ldF fX bA bA1) (s := ⟨M6, s5.o⟩)
    (by simp +decide only [ldF, WF, Prim.dst, fX, bA1, and_true]) hM6
  have k7 : ∀ r, r ≠ fX → r ≠ fX + 1 → r ≠ bA1 → r ≠ bA → r ≠ bK →
      rd (semXIR I (ldF fX bA bA1) ⟨M6, s5.o⟩).M r = rd s5.M r := fun r a b c d e =>
    (l7f r a b c).trans (a6f r d e)
  have hy7 : rdF (semXIR I (ldF fX bA bA1) ⟨M6, s5.o⟩).M fY = rdF s.M (cb + cs * x + 2 * c) := by
    rw [rdF_eq (k7 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (k7 _ (by decide) (by decide) (by decide) (by decide) (by decide)), hy]
  have ac7 : rdF (semXIR I (ldF fX bA bA1) ⟨M6, s5.o⟩).M fAc = acc := by
    rw [rdF_eq (k7 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (k7 _ (by decide) (by decide) (by decide) (by decide) (by decide)),
      rdF_eq (k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)), hAc]
  have t7 : rd (semXIR I (ldF fX bA bA1) ⟨M6, s5.o⟩).M bT = toWord t :=
    (k7 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans t5
  generalize semXIR I (ldF fX bA bA1) ⟨M6, s5.o⟩ = s7 at he hM7 k7 hy7 ac7 t7 l7f
  -- `fPr := y · E`, `fAc += fPr`
  have m8 := mulF_sem (I := I) (s := s7) hM7 (d := fPr) (a := fY) (b := fX) (by decide)
    (by decide) (by decide) (by decide)
  rw [hy7, he] at m8
  have hM8 := inv_sem I (wf_mulF fPr fY fX (by decide)) hM7
  have ac8 : rdF (semXIR I (mulF fPr fY fX) s7).M fAc = acc := by
    rw [rdF_eq (fr_mulF (by decide) (by decide) (by decide))
      (fr_mulF (by decide) (by decide) (by decide)), ac7]
  have t8 : rd (semXIR I (mulF fPr fY fX) s7).M bT = toWord t := by
    rw [fr_mulF (by decide) (by decide) (by decide), t7]
  generalize semXIR I (mulF fPr fY fX) s7 = s8 at m8 hM8 ac8 t8
  have d9 := addF_sem (I := I) (s := s8) hM8 (d := fAc) (a := fAc) (b := fPr) (by decide)
    (by decide) (by decide)
  rw [ac8, m8] at d9
  have hM9 := inv_sem I (wf_addF fAc fAc fPr (by decide)) hM8
  have t9 : rd (semXIR I (addF fAc fAc fPr) s8).M bT = toWord t := by
    rw [fr_addF (by decide) (by decide), t8]
  generalize semXIR I (addF fAc fAc fPr) s8 = s9 at d9 hM9 t9
  obtain ⟨i10, i10f⟩ := incr_sem s9.M hM9 (r := bT) (x := t) (by decide) (by decide) t9
  have e10 : semXIR I (.blk [.op .add bT bT cOne]) s9 = ⟨runPrims [.op .add bT bT cOne] s9.M, s9.o⟩ :=
    rfl
  rw [e10]
  exact ⟨by rw [rdF_eq (i10f _ (by decide)) (i10f _ (by decide)), d9], i10,
    inv_runPrims (by simp [Prim.dst, bT]) hM9⟩

/-! ## One coordinate -/

theorem pre4_sem (M : Mem) (hM : Inv M) (k : ℕ) :
    rdF (runPrims [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)] M) fAc = 0 ∧
    rd (runPrims [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)] M) bT =
      toWord 0 ∧
    rd (runPrims [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)] M) bN3 =
      toWord k ∧
    (∀ i, i ≠ fAc → i ≠ fAc + 1 → i ≠ bT → i ≠ bN3 →
      rd (runPrims [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)] M) i =
        rd M i) ∧
    Inv (runPrims [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)] M) := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, ?_, ?_, fun i h1 h2 h3 h4 => rd_runPrims_of_not_writes (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst] <;> omega) _,
    inv_runPrims (by simp [Prim.dst, fAc, bT, bN3]) hM⟩
  · simp only [runPrims, List.foldl, Prim.run, rdF, rdB]
    simp (disch := first | decide | (simp only [size_set, fAc, bT, bN3]; omega) |
      (simp only [fAc, bT, bN3]; omega)) only [rd_set_self, rd_set_ne]
    rfl
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, fAc, bT, bN3]; omega) |
      (simp only [fAc, bT, bN3]; omega)) only [rd_set_self, rd_set_ne]
    rfl
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, fAc, bT, bN3]; omega) |
      (simp only [fAc, bT, bN3]; omega)) only [rd_set_self, rd_set_ne]

/-- **The accumulation loop**: `acc = Σ_{t<k} y(J_t) · E[t]`. -/
theorem aLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb eb cb cs c : ℕ} {x : ℕ → ℕ}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb)
    (hjb2 : jb + k < 2 ^ 64) (heb2 : eb + 2 * k < 2 ^ 64)
    (hcb2 : ∀ t < k, cb + cs * x t + 2 * c + 1 < 2 ^ 64)
    (hN : rd s.M bN3 = toWord k) (hBt : rd s.M bT = toWord 0) (hCo : rd s.M bCo = toWord (2 * c))
    (hAc : rdF s.M fAc = 0) (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    rdF (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M fAc =
      ∑ t ∈ range k, rdF s.M (cb + cs * x t + 2 * c) * rdF s.M (eb + 2 * t) ∧
    Inv (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M ∧
    (∀ y, regs ≤ y → rd (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M y =
      rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC3 → r ≠ cTmp → ¬ Writes (aBody jb eb cb cs) r →
      rd (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M r = rd s.M r) := by
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧
    rdF st.M fAc = ∑ t ∈ range j, rdF s.M (cb + cs * x t + 2 * c) * rdF s.M (eb + 2 * t) ∧
    rd st.M bT = toWord j ∧ (∀ y, regs ≤ y → rd st.M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC3 → r ≠ cTmp → ¬ Writes (aBody jb eb cb cs) r → rd st.M r = rd s.M r)
  have ef : ∀ i, i ≠ bC3 → i ≠ cTmp → rd (entryK bC3 bN3 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  refine (loopK_run I (c := bC3) (n := bN3) (K := k) (aBody jb eb cb cs) Q s hM (by decide)
    (by decide) (by decide) hN hk ⟨inv_of_frame hM (size_entryK ..) fun i hi => ef i
      (by simp only [bC3]; omega) (by simp only [cTmp]; omega), ?_, ?_, fun y hy => ?_,
      fun r _ h1 h2 _ => ef r h1 h2⟩ ?_) |> fun h => ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.2.2⟩
  · rw [rdF_eq (ef _ (by decide) (by decide)) (ef _ (by decide) (by decide)), hAc, sum_range_zero]
  · rw [ef _ (by decide) (by decide), hBt]
  · simp only [regs] at hy
    exact ef y (by simp only [bC3]; omega) (by simp only [cTmp]; omega)
  · rintro j st hj ⟨hM', hA, hT', hH, hR⟩
    have hJ' : rd st.M (jb + j) = toWord (x j) := by
      rw [hH _ (by simp only [regs] at hjb ⊢; omega), hJ j hj]
    have hCo' : rd st.M bCo = toWord (2 * c) := by
      rw [hR _ (by decide) (by decide) (by decide) (by
        simp +decide only [aBody, addrPs, ldF, Writes, Prim.dst, bnw_mulF, bnw_addF, bCo, fPr, fAc,
          bA, bK, bJ, bA1, fY, fX, bT, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp,
          exists_eq_left, or_false, List.cons_append, List.nil_append]), hCo]
    obtain ⟨b1, b2, hM2⟩ := aBody_sem I st hM' (t := j) (c := c) (x := x j) hjb heb hcb (by omega)
      (by omega) (hcb2 j hj) hT' hCo' hA hJ'
    have hH2 : ∀ y, regs ≤ y → rd (semXIR I (aBody jb eb cb cs) st).M y = rd st.M y :=
      fun y hy => hframe I _ st (lo_aBody jb eb cb cs) y hy
    refine ⟨inv_decS hM2 (by decide), ?_, by rw [rd_decS (by decide), b2], fun y hy => ?_,
      fun r hr h1 h2 h3 => ?_⟩
    · rw [rdF_decS _ (by decide) (by decide), b1, sum_range_succ,
        rdF_eq (hH _ (by simp only [regs] at hcb ⊢; omega)) (hH _ (by simp only [regs] at hcb ⊢; omega)),
        rdF_eq (hH _ (by simp only [regs] at heb ⊢; omega)) (hH _ (by simp only [regs] at heb ⊢; omega))]
    · rw [rd_decS (by simp only [bC3, regs] at hy ⊢; omega), hH2 y hy, hH y hy]
    · rw [rd_decS (Ne.symm h1), frame I _ st (wf_aBody jb eb cb cs) hM' r hr h3, hR r hr h1 h2 h3]

/-- **One coordinate `c`**: `out[c][s] := (ℓ = 0 ? y_c(s) : ℓ · Σ_t y_c(J_t) E[t])` at
`ob + 2k·c + 2s`; `c += 1`. -/
theorem cBody_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k jb eb cb cs ob c s0 : ℕ} {x : ℕ → ℕ} {lp : F}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb) (hob : regs ≤ ob)
    (hjb2 : jb + k < 2 ^ 64) (heb2 : eb + 2 * k < 2 ^ 64)
    (hcb2 : ∀ t < k, cb + cs * x t + 2 * c + 1 < 2 ^ 64) (hcs2 : cb + cs * s0 + 2 * c + 1 < 2 ^ 64)
    (hob2 : ob + 2 * k * c + 2 * s0 + 1 < 2 ^ 64) (hsz : ob + 2 * k * c + 2 * s0 + 1 < s.M.size)
    (hc2 : 2 * c + 2 < 2 ^ 64)
    (hCi : rd s.M bCi = toWord c) (hCo : rd s.M bCo = toWord (2 * c)) (hS : rd s.M bS = toWord s0)
    (hLp : rdF s.M fLp = lp) (hZ : rd s.M bZ = bW (decide (lp = 0)))
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    rdF (semXIR I (cBody k jb eb cb cs ob) s).M (ob + 2 * k * c + 2 * s0) =
      (if lp = 0 then rdF s.M (cb + cs * s0 + 2 * c) else
        lp * ∑ t ∈ range k, rdF s.M (cb + cs * x t + 2 * c) * rdF s.M (eb + 2 * t)) ∧
    rd (semXIR I (cBody k jb eb cb cs ob) s).M bCi = toWord (c + 1) ∧
    rd (semXIR I (cBody k jb eb cb cs ob) s).M bCo = toWord (2 * (c + 1)) ∧
    (∀ y, regs ≤ y → y ≠ ob + 2 * k * c + 2 * s0 → y ≠ ob + 2 * k * c + 2 * s0 + 1 →
      rd (semXIR I (cBody k jb eb cb cs ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (cBody k jb eb cb cs ob) s).M := by
  have hs := hM.1
  simp only [regs] at hs hjb heb hcb hob
  rw [cBody]
  simp only [semXIR_seq]
  obtain ⟨q1, q2, q3, q4, hM1⟩ := pre4_sem s.M hM k
  have e1 : semXIR I (.blk [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)])
      s = ⟨runPrims [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)] s.M,
        s.o⟩ := rfl
  rw [e1]
  have z1 := size_runPrims [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)]
    s.M
  generalize runPrims [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)] s.M =
    M1 at q1 q2 q3 q4 hM1 z1
  have hH1 : ∀ y, regs ≤ y → rd M1 y = rd s.M y := fun y hy => by
    simp only [regs] at hy
    exact q4 y (by simp only [fAc]; omega) (by simp only [fAc]; omega) (by simp only [bT]; omega)
      (by simp only [bN3]; omega)
  have hCo1 : rd M1 bCo = toWord (2 * c) := (q4 _ (by decide) (by decide) (by decide)
    (by decide)).trans hCo
  obtain ⟨A1, hM2, A3, A4⟩ := aLoop_sem I ⟨M1, s.o⟩ hM1 (k := k) (jb := jb) (eb := eb) (cb := cb)
    (cs := cs) (c := c) (x := x) hk (by simp only [regs]; omega) (by simp only [regs]; omega)
    (by simp only [regs]; omega) hjb2 heb2 hcb2 q3 q2 hCo1 q1
    (fun t ht => by rw [hH1 _ (by simp only [regs]; omega), hJ t ht])
  have nw : ∀ r, r ∈ [bZ, bS, bCi, bCo, fLp, fLp + 1] → ¬ Writes (aBody jb eb cb cs) r := by
    simp +decide only [aBody, addrPs, ldF, Writes, Prim.dst, bnw_mulF, bnw_addF, bZ, bS, bCi, bCo,
      fLp, fPr, fAc, bA, bK, bJ, bA1, fY, fX, bT, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
      exists_eq_or_imp, forall_eq, exists_eq_left, or_false, and_true, List.cons_append,
      List.nil_append]
  have R2 : ∀ r, r ∈ [bZ, bS, bCi, bCo, fLp, fLp + 1] →
      rd (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) ⟨M1, s.o⟩).M r = rd s.M r :=
    fun r hr => by
      have : r < regs ∧ r ≠ bC3 ∧ r ≠ cTmp ∧ r ≠ fAc ∧ r ≠ fAc + 1 ∧ r ≠ bT ∧ r ≠ bN3 := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      obtain ⟨a, b, c', d, e, f, g⟩ := this
      rw [A4 r a b c' (nw r hr), q4 r d e f g]
  replace A1 : rdF (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) ⟨M1, s.o⟩).M fAc =
      ∑ t ∈ range k, rdF s.M (cb + cs * x t + 2 * c) * rdF s.M (eb + 2 * t) := by
    rw [A1]
    exact Finset.sum_congr rfl fun t _ => by
      dsimp only
      rw [rdF_eq (hH1 _ (by simp only [regs]; omega)) (hH1 _ (by simp only [regs]; omega)),
        rdF_eq (hH1 (eb + 2 * t) (by simp only [regs]; omega))
          (hH1 (eb + 2 * t + 1) (by simp only [regs]; omega))]
  have z2 := size_sem I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) ⟨M1, s.o⟩
  generalize semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) ⟨M1, s.o⟩ = s2 at A1 hM2 A3 A4 R2 z2
  have H2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy => (A3 y hy).trans (hH1 y hy)
  have hs2 := hM2.1
  -- the value: `y_c(s)` or `ℓ · acc`
  have st3 : rdF (semXIR I (.ite bZ (yIR cb cs) (mulF fAc fLp fAc)) s2).M fAc =
        (if lp = 0 then rdF s.M (cb + cs * s0 + 2 * c) else
          lp * ∑ t ∈ range k, rdF s.M (cb + cs * x t + 2 * c) * rdF s.M (eb + 2 * t)) ∧
      (∀ r, r ∈ [bS, bCi, bCo] →
        rd (semXIR I (.ite bZ (yIR cb cs) (mulF fAc fLp fAc)) s2).M r = rd s.M r) ∧
      (∀ y, regs ≤ y → rd (semXIR I (.ite bZ (yIR cb cs) (mulF fAc fLp fAc)) s2).M y = rd s.M y) ∧
      Inv (semXIR I (.ite bZ (yIR cb cs) (mulF fAc fLp fAc)) s2).M := by
    have wy : WF (yIR cb cs) := by simp +decide only [yIR, addrPs, ldF, WF, Prim.dst, bA, bK, fAc,
      bA1, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true,
      List.cons_append, List.nil_append]
    have ly : Lo (yIR cb cs) := by simp +decide only [yIR, addrPs, ldF, Lo, Prim.dst, bA, bK, fAc,
      bA1, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true,
      List.cons_append, List.nil_append]
    have nwy : ∀ r, r ∈ [bS, bCi, bCo] → ¬ Writes (yIR cb cs) r := by
      simp +decide only [yIR, addrPs, ldF, Writes, Prim.dst, bA, bK, fAc, bA1, bS, bCi, bCo,
        List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq,
        exists_eq_left, or_false, and_true, List.cons_append, List.nil_append]
    have nwm : ∀ r, r ∈ [bS, bCi, bCo] → ¬ Writes (mulF fAc fLp fAc) r := by
      simp [bnw_mulF, fAc, bS, bCi, bCo]
    have mem3 : ∀ r, r ∈ [bS, bCi, bCo] → r < regs ∧ r ∈ [bZ, bS, bCi, bCo, fLp, fLp + 1] := by
      simp [bS, bCi, bCo, regs]
    rw [semXIR_ite, R2 _ (by simp), hZ]
    by_cases hl : lp = 0
    · rw [decide_eq_true hl, if_neg bW_ne_zero, if_pos hl]
      refine ⟨?_, fun r hr => ?_, fun y hy => (hframe I _ s2 ly y hy).trans (H2 y hy),
        inv_sem I wy hM2⟩
      · rw [yIR, semXIR_seq]
        obtain ⟨c1, c1f⟩ := addrPs_sem s2.M hs2 (d := bA) (i := bS) (b := cb) (m := cs) (by decide)
          (by decide) (by decide) ((R2 _ (by simp)).trans hS)
        obtain ⟨c2, -⟩ := addOp_sem (runPrims (addrPs bA bS cb cs) s2.M)
          (by rw [size_runPrims]; exact hs2) (d := bA) (r := bCo) (x := cb + cs * s0) (y := 2 * c)
          (by decide) c1 ((c1f _ (by decide) (by decide)).trans ((R2 _ (by simp)).trans hCo))
        have e : semXIR I (.blk (addrPs bA bS cb cs ++ [.op .add bA bA bCo])) s2 =
            ⟨runPrims [.op .add bA bA bCo] (runPrims (addrPs bA bS cb cs) s2.M), s2.o⟩ := by
          show (⟨runPrims _ s2.M, s2.o⟩ : St) = _; rw [runPrims_append]
        have hMa : Inv (runPrims [.op .add bA bA bCo] (runPrims (addrPs bA bS cb cs) s2.M)) :=
          inv_runPrims (by simp [Prim.dst, bA]) (inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM2)
        have ha : ∀ y, regs ≤ y →
            rd (runPrims [.op .add bA bA bCo] (runPrims (addrPs bA bS cb cs) s2.M)) y = rd s.M y :=
          fun y hy => by
            simp only [regs] at hy
            exact (rd_runPrims_of_not_writes (by simp [Prim.dst, bA]; omega) _).trans
              ((rd_runPrims_of_not_writes (by simp [addrPs, Prim.dst, bA, bK]; omega) _).trans
                (H2 y (by simp only [regs]; omega)))
        rw [e]
        generalize runPrims [.op .add bA bA bCo] (runPrims (addrPs bA bS cb cs) s2.M) = Ma at c2 hMa ha
        obtain ⟨l1, -, -⟩ := ldF_sem I ⟨Ma, s2.o⟩ hMa (d := fAc) (p := bA) (p1 := bA1)
          (x := cb + cs * s0 + 2 * c) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) c2 (by simp only [regs]; omega) hcs2
        rw [l1, rdF_eq (ha _ (by simp only [regs]; omega)) (ha _ (by simp only [regs]; omega))]
      · rw [frame I _ s2 wy hM2 r (mem3 r hr).1 (nwy r hr), R2 r (mem3 r hr).2]
    · rw [decide_eq_false hl, bW_false, if_pos rfl, if_neg hl]
      refine ⟨?_, fun r hr => ?_, fun y hy => (hframe I _ s2 (lo_mulF (by decide)) y hy).trans
        (H2 y hy), inv_sem I (wf_mulF _ _ _ (by decide)) hM2⟩
      · rw [mulF_sem hM2 (by decide) (by decide) (by decide) (by decide), A1,
          rdF_eq (R2 _ (by simp)) (R2 _ (by simp)), hLp]
      · rw [frame I _ s2 (wf_mulF _ _ _ (by decide)) hM2 r (mem3 r hr).1 (nwm r hr),
          R2 r (mem3 r hr).2]
  obtain ⟨v3, r3, h3, hM3⟩ := st3
  have z3 := size_sem I (.ite bZ (yIR cb cs) (mulF fAc fLp fAc)) s2
  generalize semXIR I (.ite bZ (yIR cb cs) (mulF fAc fLp fAc)) s2 = s3 at v3 r3 h3 hM3 z3
  have hs3 := hM3.1
  -- the address `ob + 2k·c + 2s`
  obtain ⟨o1, o1f⟩ := addrPs_sem s3.M hs3 (d := bA) (i := bCi) (b := ob) (m := 2 * k) (by decide)
    (by decide) (by decide) ((r3 _ (by simp)).trans hCi)
  obtain ⟨o2, o2f⟩ := addOp_sem (runPrims (addrPs bA bCi ob (2 * k)) s3.M)
    (by rw [size_runPrims]; exact hs3) (d := bA) (r := bS) (x := ob + 2 * k * c) (y := s0)
    (by decide) o1 ((o1f _ (by decide) (by decide)).trans ((r3 _ (by simp)).trans hS))
  obtain ⟨o3, o3f⟩ := addOp_sem (runPrims [.op .add bA bA bS] (runPrims (addrPs bA bCi ob (2 * k)) s3.M))
    (by rw [size_runPrims, size_runPrims]; exact hs3) (d := bA) (r := bS) (x := ob + 2 * k * c + s0)
    (y := s0) (by decide) o2 ((o2f _ (by decide)).trans ((o1f _ (by decide) (by decide)).trans
      ((r3 _ (by simp)).trans hS)))
  have e4 : semXIR I (.blk (addrPs bA bCi ob (2 * k) ++ [.op .add bA bA bS, .op .add bA bA bS])) s3 =
      ⟨runPrims [.op .add bA bA bS] (runPrims [.op .add bA bA bS]
        (runPrims (addrPs bA bCi ob (2 * k)) s3.M)), s3.o⟩ := by
    show (⟨runPrims _ s3.M, s3.o⟩ : St) = _
    rw [runPrims_append, show ([.op .add bA bA bS, .op .add bA bA bS] : List Prim) =
      [.op .add bA bA bS] ++ [.op .add bA bA bS] from rfl, runPrims_append]
  rw [e4]
  have k4 : ∀ r, r ≠ bA → r ≠ bK → rd (runPrims [.op .add bA bA bS] (runPrims [.op .add bA bA bS]
      (runPrims (addrPs bA bCi ob (2 * k)) s3.M))) r = rd s3.M r := fun r a b =>
    (o3f r a).trans ((o2f r a).trans (o1f r a b))
  have hM4 : Inv (runPrims [.op .add bA bA bS] (runPrims [.op .add bA bA bS]
      (runPrims (addrPs bA bCi ob (2 * k)) s3.M))) :=
    inv_runPrims (by simp [Prim.dst, bA]) (inv_runPrims (by simp [Prim.dst, bA])
      (inv_runPrims (by simp [addrPs, Prim.dst, bA, bK]) hM3))
  have z4 : (runPrims [.op .add bA bA bS] (runPrims [.op .add bA bA bS]
      (runPrims (addrPs bA bCi ob (2 * k)) s3.M))).size = s3.M.size := by simp only [size_runPrims]
  rw [show ob + 2 * k * c + s0 + s0 = ob + 2 * k * c + 2 * s0 by ring] at o3
  generalize runPrims [.op .add bA bA bS] (runPrims [.op .add bA bA bS]
      (runPrims (addrPs bA bCi ob (2 * k)) s3.M)) = M4 at o3 k4 hM4 z4
  -- the store
  have hz : ob + 2 * k * c + 2 * s0 + 1 < M4.size := by
    rw [z4, z3, z2]; show _ < M1.size; rw [z1]; exact hsz
  obtain ⟨g1, g2, hM5⟩ := stF_sem I ⟨M4, s3.o⟩ hM4 (p := bA) (p1 := bA1) (v := fAc)
    (x := ob + 2 * k * c + 2 * s0) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) o3 (by simp only [regs]; omega) hob2 hz
  have K5 : ∀ r, r < regs → r ≠ bA1 → r ≠ cTmp → r ≠ bA → r ≠ bK →
      rd (semXIR I (stF bA bA1 fAc) ⟨M4, s3.o⟩).M r = rd s3.M r := fun r hr a b c' d => by
    simp only [regs] at hr
    rw [g2 r (by omega) (by omega) a b, k4 r c' d]
  generalize semXIR I (stF bA bA1 fAc) ⟨M4, s3.o⟩ = s5 at g1 g2 hM5 K5
  -- `c += 1`, `2c += 2`
  have hs5 := hM5.1
  simp only [regs] at hs5
  have h1 : rd s5.M cOne = 1 := hM5.2 0 (by decide)
  have ci5 : rd s5.M bCi = toWord c := by
    rw [K5 _ (by decide) (by decide) (by decide) (by decide) (by decide), r3 _ (by simp), hCi]
  have co5 : rd s5.M bCo = toWord (2 * c) := by
    rw [K5 _ (by decide) (by decide) (by decide) (by decide) (by decide), r3 _ (by simp), hCo]
  have e6 : semXIR I (.blk [.op .add bCi bCi cOne, .const bK 2, .op .add bCo bCo bK]) s5 =
      ⟨runPrims [.op .add bCi bCi cOne, .const bK 2, .op .add bCo bCo bK] s5.M, s5.o⟩ := rfl
  rw [e6]
  have f6 : ∀ y, y ≠ bCi → y ≠ bK → y ≠ bCo →
      rd (runPrims [.op .add bCi bCi cOne, .const bK 2, .op .add bCo bCo bK] s5.M) y = rd s5.M y :=
    fun y a b c' => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst] <;>
        first | exact Ne.symm a | exact Ne.symm b | exact Ne.symm c') _
  refine ⟨?_, ?_, ?_, fun y hy hy1 hy2 => ?_,
    inv_runPrims (by simp [Prim.dst, bCi, bK, bCo]) hM5⟩
  · rw [rdF_eq (f6 _ (by simp only [bCi]; omega) (by simp only [bK]; omega) (by simp only [bCo]; omega))
      (f6 _ (by simp only [bCi]; omega) (by simp only [bK]; omega) (by simp only [bCo]; omega)), g1,
      rdF_eq (k4 _ (by decide) (by decide)) (k4 _ (by decide) (by decide)), v3]
  · simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_ne (by decide), rd_set_self (by simp only [bCi]; omega),
      ci5, h1, add_one_toWord]
  · simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, bCo]; omega), rd_set_ne (by decide),
      rd_set_ne (by decide), co5, rd_set_self (by simp only [size_set, bK]; omega),
      show (2 : Word) = toWord 2 from rfl, add_toWord]
    ring_nf
  · simp only [regs] at hy
    rw [f6 _ (by simp only [bCi]; omega) (by simp only [bK]; omega) (by simp only [bCo]; omega),
      g2 y hy1 hy2 (by simp only [bA1]; omega) (by simp only [cTmp]; omega),
      k4 _ (by simp only [bA]; omega) (by simp only [bK]; omega), h3 y (by simp only [regs]; omega)]

/-! ## The loops of one target -/

theorem wf_eBody (djb wb eb : ℕ) : WF (eBody djb wb eb) := by
  simp +decide only [eBody, addrPs, ldF, stF, WF, Prim.dst, wfF_mul, wfF_add, wfF_inv, bA, bK, bA1,
    fX, fDd, fLp, fIv, fEt, bT, cTmp, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]

/-- **The `E` row**: `E[t] = W[t] (ds + DJ[t])⁻¹` for `t < k`, `ℓ = Π_t (ds + DJ[t])`. -/
theorem eLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k djb wb eb : ℕ} {ds : F}
    (hk : k < 2 ^ 64) (hdjb : regs ≤ djb) (hwb : regs ≤ wb) (heb : regs ≤ eb)
    (hdj2 : djb + 2 * k < 2 ^ 64) (hwb2 : wb + 2 * k < 2 ^ 64) (heb2 : eb + 2 * k < 2 ^ 64)
    (hsz : eb + 2 * k ≤ s.M.size) (hdE : djb + 2 * k ≤ eb ∨ eb + 2 * k ≤ djb)
    (hwE : wb + 2 * k ≤ eb ∨ eb + 2 * k ≤ wb)
    (hN : rd s.M bN2 = toWord k) (hBt : rd s.M bT = toWord 0) (hDs : rdF s.M fDs = ds)
    (hLp : rdF s.M fLp = 1) :
    (∀ t < k, rdF (semXIR I (.loopK bC2 bN2 (toWord k) (eBody djb wb eb)) s).M (eb + 2 * t) =
      rdF s.M (wb + 2 * t) * (ds + rdF s.M (djb + 2 * t))⁻¹) ∧
    rdF (semXIR I (.loopK bC2 bN2 (toWord k) (eBody djb wb eb)) s).M fLp =
      ∏ t ∈ range k, (ds + rdF s.M (djb + 2 * t)) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + 2 * k ≤ y) →
      rd (semXIR I (.loopK bC2 bN2 (toWord k) (eBody djb wb eb)) s).M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (eBody djb wb eb) r →
      rd (semXIR I (.loopK bC2 bN2 (toWord k) (eBody djb wb eb)) s).M r = rd s.M r) ∧
    Inv (semXIR I (.loopK bC2 bN2 (toWord k) (eBody djb wb eb)) s).M := by
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bT = toWord j ∧
    rdF st.M fDs = ds ∧ rdF st.M fLp = ∏ t ∈ range j, (ds + rdF s.M (djb + 2 * t)) ∧
    (∀ t < j, rdF st.M (eb + 2 * t) = rdF s.M (wb + 2 * t) * (ds + rdF s.M (djb + 2 * t))⁻¹) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + 2 * j ≤ y) → rd st.M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (eBody djb wb eb) r → rd st.M r = rd s.M r)
  have ef : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (c := bC2) (n := bN2) (K := k) (eBody djb wb eb) Q s hM (by decide)
    (by decide) (by decide) hN hk ⟨inv_of_frame hM (size_entryK ..) fun i hi => ef i
      (by simp only [bC2]; omega) (by simp only [cTmp]; omega), size_entryK .., by
        rw [ef _ (by decide) (by decide), hBt],
      by rw [rdF_eq (ef _ (by decide) (by decide)) (ef _ (by decide) (by decide)), hDs],
      by rw [rdF_eq (ef _ (by decide) (by decide)) (ef _ (by decide) (by decide)), hLp,
        prod_range_zero],
      fun t ht => absurd ht (Nat.not_lt_zero _),
      fun y hy _ => ef y (by simp only [regs, bC2] at hy ⊢; omega)
        (by simp only [regs, cTmp] at hy ⊢; omega),
      fun r _ h1 h2 _ => ef r h1 h2⟩ ?_
  · exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, fun y hy hy2 => h.2.2.2.2.2.2.1 y hy hy2,
      h.2.2.2.2.2.2.2, h.1⟩
  · rintro j st hj ⟨hM', hz, hT', hD, hL, hE, hH, hR⟩
    simp only [regs] at hdjb hwb heb
    have hG : rdF st.M (djb + 2 * j) = rdF s.M (djb + 2 * j) :=
      rdF_eq (hH _ (by simp only [regs]; omega) (by omega)) (hH _ (by simp only [regs]; omega)
        (by omega))
    have hW : rdF st.M (wb + 2 * j) = rdF s.M (wb + 2 * j) :=
      rdF_eq (hH _ (by simp only [regs]; omega) (by omega)) (hH _ (by simp only [regs]; omega)
        (by omega))
    obtain ⟨b1, b2, b3, b4, b5, hM2⟩ := eBody_sem I st hM' (t := j) (by simp only [regs]; omega)
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
      (by omega) hT' hD hL hG hW
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz], by rw [rd_decS (by decide), b3],
      by rw [rdF_decS _ (by decide) (by decide), b4],
      by rw [rdF_decS _ (by decide) (by decide), b2, prod_range_succ], fun t ht => ?_,
      fun y hy hy2 => ?_, fun r hr h1 h2 h3 => ?_⟩
    · rw [rdF_decS _ (by simp only [bC2]; omega) (by simp only [bC2]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [rdF_eq (b5 _ (by simp only [regs]; omega) (by omega) (by omega))
          (b5 _ (by simp only [regs]; omega) (by omega) (by omega)), hE t ht]
      · exact b1
    · rw [rd_decS (by simp only [bC2, regs] at hy ⊢; omega), b5 y hy (by omega) (by omega),
        hH y hy (by omega)]
    · rw [rd_decS (Ne.symm h1), frame I _ st (wf_eBody djb wb eb) hM' r hr h3, hR r hr h1 h2 h3]

theorem wf_cBody (k jb eb cb cs ob : ℕ) : WF (cBody k jb eb cb cs ob) := by
  simp +decide only [cBody, aBody, yIR, addrPs, ldF, stF, WF, Writes, Prim.dst, wfF_mul, wfF_add,
    bnw_mulF, bnw_addF, bA, bK, bA1, bJ, fY, fX, fPr, fAc, bT, bN3, bC3, bCi, bCo, cTmp, regs,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq, exists_eq_left,
    or_false, and_true, List.cons_append, List.nil_append]

/-- **The coordinates of one target**: `out[c][s] = (ℓ = 0 ? y_c(s) : ℓ Σ_t y_c(J_t) E[t])` for
`c < C`. -/
theorem cLoop_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb eb cb cs ob s0 : ℕ} {x : ℕ → ℕ} {lp : F}
    (hk : k < 2 ^ 64) (hC : C < 2 ^ 62) (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb)
    (hob : regs ≤ ob) (hjb2 : jb + k < 2 ^ 64) (heb2 : eb + 2 * k < 2 ^ 64)
    (hcb2 : ∀ t < k, ∀ c < C, cb + cs * x t + 2 * c + 1 < 2 ^ 64)
    (hcs2 : ∀ c < C, cb + cs * s0 + 2 * c + 1 < 2 ^ 64) (hs0 : s0 < k)
    (hob2 : ob + 2 * k * C < 2 ^ 64) (hsz : ob + 2 * k * C ≤ s.M.size)
    (hOJ : ob + 2 * k * C ≤ jb ∨ jb + k ≤ ob) (hOE : ob + 2 * k * C ≤ eb ∨ eb + 2 * k ≤ ob)
    (hOY : ∀ c < C, ∀ j, j ∈ (List.range k).map x ∨ j = s0 →
      ob + 2 * k * C ≤ cb + cs * j + 2 * c ∨ cb + cs * j + 2 * c + 2 ≤ ob)
    (hN : rd s.M bN2 = toWord C) (hCi : rd s.M bCi = toWord 0) (hCo : rd s.M bCo = toWord 0)
    (hS : rd s.M bS = toWord s0) (hLp : rdF s.M fLp = lp) (hZ : rd s.M bZ = bW (decide (lp = 0)))
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    (∀ c < C, rdF (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M
        (ob + 2 * k * c + 2 * s0) =
      (if lp = 0 then rdF s.M (cb + cs * s0 + 2 * c) else
        lp * ∑ t ∈ range k, rdF s.M (cb + cs * x t + 2 * c) * rdF s.M (eb + 2 * t))) ∧
    (∀ y, regs ≤ y → (∀ c < C, y ≠ ob + 2 * k * c + 2 * s0 ∧ y ≠ ob + 2 * k * c + 2 * s0 + 1) →
      rd (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (cBody k jb eb cb cs ob) r →
      rd (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M r = rd s.M r) ∧
    Inv (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M := by
  simp only [regs] at hjb heb hcb hob
  let V : ℕ → F := fun c => if lp = 0 then rdF s.M (cb + cs * s0 + 2 * c) else
    lp * ∑ t ∈ range k, rdF s.M (cb + cs * x t + 2 * c) * rdF s.M (eb + 2 * t)
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bCi = toWord j ∧
    rd st.M bCo = toWord (2 * j) ∧
    (∀ c < j, rdF st.M (ob + 2 * k * c + 2 * s0) = V c) ∧
    (∀ y, regs ≤ y → (∀ c < j, y ≠ ob + 2 * k * c + 2 * s0 ∧ y ≠ ob + 2 * k * c + 2 * s0 + 1) →
      rd st.M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (cBody k jb eb cb cs ob) r → rd st.M r = rd s.M r)
  have ef : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord C) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (c := bC2) (n := bN2) (K := C) (cBody k jb eb cb cs ob) Q s hM (by decide)
    (by decide) (by decide) hN (by omega) ⟨inv_of_frame hM (size_entryK ..) fun i hi => ef i
      (by simp only [bC2]; omega) (by simp only [cTmp]; omega), size_entryK .., by
        rw [ef _ (by decide) (by decide), hCi],
      by rw [ef _ (by decide) (by decide), hCo],
      fun c hc => absurd hc (Nat.not_lt_zero _),
      fun y hy _ => ef y (by simp only [regs, bC2] at hy ⊢; omega)
        (by simp only [regs, cTmp] at hy ⊢; omega),
      fun r _ h1 h2 _ => ef r h1 h2⟩ ?_
  · exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, h.1⟩
  · rintro j st hj ⟨hM', hz, hCi', hCo', hV, hH, hR⟩
    have nwc : ∀ r, r ∈ [bS, fLp, fLp + 1, bZ] → ¬ Writes (cBody k jb eb cb cs ob) r := by
      simp +decide only [cBody, aBody, yIR, addrPs, ldF, stF, Writes, Prim.dst, bnw_mulF, bnw_addF,
        bA, bK, bA1, bJ, fY, fX, fPr, fAc, bT, bN3, bC3, bCi, bCo, cTmp, bS, fLp, bZ, List.mem_cons,
        List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq, exists_eq_left, or_false,
        and_true, List.cons_append, List.nil_append]
    have R : ∀ r, r ∈ [bS, fLp, fLp + 1, bZ] → rd st.M r = rd s.M r := fun r hr => by
      have : r < regs ∧ r ≠ bC2 ∧ r ≠ cTmp := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      exact hR r this.1 this.2.1 this.2.2 (nwc r hr)
    have hHy : ∀ y, regs ≤ y → (y < ob ∨ ob + 2 * k * C ≤ y) → rd st.M y = rd s.M y :=
      fun y hy hy2 => hH y hy fun c hc => by
        have : 2 * k * c + 2 * s0 + 1 < 2 * k * C := by
          have := Nat.mul_le_mul_left (2 * k) (show c + 1 ≤ C by omega)
          rw [Nat.mul_add, Nat.mul_one] at this; omega
        constructor <;> omega
    have hk2 : 2 * k * j + 2 * s0 + 1 < 2 * k * C := by
      have := Nat.mul_le_mul_left (2 * k) (show j + 1 ≤ C by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    obtain ⟨b1, b2, b3, b4, hM2⟩ := cBody_sem I st hM' (c := j) (s0 := s0) (x := x) (lp := lp) hk
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
      (by simp only [regs]; omega) hjb2 heb2 (fun t ht => hcb2 t ht j hj) (hcs2 j hj) (by omega)
      (by rw [hz]; omega) (by omega) hCi' hCo' ((R _ (by simp)).trans hS)
      (by rw [rdF_eq (R _ (by simp)) (R _ (by simp)), hLp]) ((R _ (by simp)).trans hZ)
      (fun t ht => by
        rw [hHy _ (by simp only [regs]; omega) (by rcases hOJ with h | h <;> omega), hJ t ht])
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz],
      by rw [rd_decS (by decide), b2], by rw [rd_decS (by decide), b3], fun c hc => ?_,
      fun y hy hy2 => ?_, fun r hr h1 h2 h3 => ?_⟩
    · rw [rdF_decS _ (by simp only [bC2]; omega) (by simp only [bC2]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · have hlt : 2 * k * c + 2 * s0 + 1 < 2 * k * j := by
          have := Nat.mul_le_mul_left (2 * k) (show c + 1 ≤ j by omega)
          rw [Nat.mul_add, Nat.mul_one] at this; omega
        rw [rdF_eq (b4 _ (by simp only [regs]; omega) (by omega) (by omega))
          (b4 _ (by simp only [regs]; omega) (by omega) (by omega)), hV c hc]
      · rw [b1]
        have hy' : ∀ j', j' ∈ (List.range k).map x ∨ j' = s0 →
            rdF st.M (cb + cs * j' + 2 * c) = rdF s.M (cb + cs * j' + 2 * c) := fun j' hj' =>
          rdF_eq (hHy _ (by simp only [regs]; omega) (by rcases hOY c hj j' hj' with h | h <;> omega))
            (hHy _ (by simp only [regs]; omega) (by rcases hOY c hj j' hj' with h | h <;> omega))
        simp only [V]
        split_ifs
        · exact hy' s0 (.inr rfl)
        · refine congrArg (lp * ·) (Finset.sum_congr rfl fun t ht => ?_)
          have ht' := Finset.mem_range.1 ht
          rw [hy' (x t) (.inl (List.mem_map.2 ⟨t, List.mem_range.2 (Finset.mem_range.1 ht), rfl⟩)),
            rdF_eq (hHy _ (by simp only [regs]; omega) (by rcases hOE with h | h <;> omega))
              (hHy _ (by simp only [regs]; omega) (by rcases hOE with h | h <;> omega))]
    · rw [rd_decS (by simp only [bC2, regs] at hy ⊢; omega),
        b4 y hy (hy2 j (by omega)).1 (hy2 j (by omega)).2,
        hH y hy fun c hc => hy2 c (by omega)]
    · rw [rd_decS (Ne.symm h1), frame I _ st (wf_cBody k jb eb cb cs ob) hM' r hr h3,
        hR r hr h1 h2 h3]

end FR.X
