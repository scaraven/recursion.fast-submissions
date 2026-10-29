-- New for `flock-recursive` (BLUEPRINT §6.2 step 4: `P = A[0…k)`; stage S-H2, track L-ext).
import FRXBfly

/-!
# The agreement set's first `k` positions on the machine

BLUEPRINT §6.2 step 4 takes the first `k` positions of the agreement set `A` (`P = A[0…k)`,
`FRXDecodeB.firstK`). On the machine `A` is a flag array: word `f j` at `fb + j`, nonzero iff
`j ∈ A`. The scan `scanIR n k fb lb` runs over `j = 0 … n − 1` and appends `j` to the list at
`lb` while fewer than `k` positions are listed.

**`scanIR_sem`**: the count is `min(|L|, k)` and cell `lb + t` holds `L[t]`, `L = scanL n f` the
flagged positions in increasing order. **`firstK_scan`**: `firstK n A k` is the set of the
listed positions.
-/

namespace FR.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-! ## Registers and the program -/

/-- The position `j`. -/ def rJs : ℕ := 178
/-- The count of listed positions. -/ def rCn : ℕ := 179
/-- The flag test. -/ def rFl : ℕ := 180
/-- An address. -/ def rAd3 : ℕ := 181
/-- `k`. -/ def rK3 : ℕ := 182
/-- Counter of the scan. -/ def rC4 : ℕ := 183
/-- Count of the scan. -/ def rN4 : ℕ := 184

/-- The listing step: `M[lb + cnt] := j`, `cnt += 1`. -/
def appendIR (lb : ℕ) : XIR :=
  .seq (.blk [.const uT1 (toWord lb), .op .add rAd3 rCn uT1])
    (.seq (.store rAd3 rJs) (.blk [.op .add rCn rCn cOne]))

/-- The flag test: `rFl := [f j ≠ 0 ∧ cnt < k]`. -/
def testPs : List Prim :=
  [.const uT1 0, .op .eq rFl rFl uT1, .op .eq rFl rFl uT1, .op .ltu uT2 rCn rK3,
   .op .and rFl rFl uT2]

/-- **One position** `j`. -/
def scanBody (fb lb : ℕ) : XIR :=
  .seq (.blk [.const uT1 (toWord fb), .op .add rAd3 rJs uT1]) (.seq (.load rFl rAd3)
    (.seq (.blk testPs) (.seq (.ite rFl (appendIR lb) (.blk []))
      (.blk [.op .add rJs rJs cOne]))))

/-- **The scan** of positions `0 … n − 1` for the first `k` flagged ones. -/
def scanIR (n k fb lb : ℕ) : XIR :=
  .seq (.blk [.const rJs 0, .const rCn 0, .const rK3 (toWord k), .const rN4 (toWord n)])
    (.loopK rC4 rN4 (toWord n) (scanBody fb lb))

theorem wf_scanIR (n k fb lb : ℕ) : WF (scanIR n k fb lb) := by
  simp +decide only [scanIR, scanBody, appendIR, testPs, WF, Writes, Prim.dst, rJs, rCn, rFl, rAd3,
    rK3, rC4, rN4, uT1, uT2, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    exists_eq_or_imp, forall_eq, exists_eq_left, or_false, and_true]

theorem noLoopT_scanIR (n k fb lb : ℕ) : NoLoopT (scanIR n k fb lb) := by
  simp [scanIR, scanBody, appendIR, NoLoopT]

theorem outs_scanIR (n k fb lb t : ℕ) : outs (scanIR n k fb lb) t = 0 := by
  simp [scanIR, scanBody, appendIR, outs]

theorem cost_scanIR (n k fb lb t : ℕ) (hn : n < 2 ^ 64) :
    cost (scanIR n k fb lb) t = 16 + n * 32 := by
  have a : (toWord n).toNat = n := toNat_toWord hn
  simp only [scanIR, scanBody, appendIR, testPs, cost, blkSteps, List.length_cons,
    List.length_nil, a]
  norm_num
  omega

/-! ## The pure list -/

/-- **The flagged positions below `n`**, in increasing order. -/
def scanL (n : ℕ) (f : ℕ → Word) : List ℕ := (List.range n).filter fun j => f j ≠ 0

theorem scanL_succ (n : ℕ) (f : ℕ → Word) :
    scanL (n + 1) f = scanL n f ++ if f n ≠ 0 then [n] else [] := by
  simp only [scanL, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
  by_cases h : f n = 0 <;> simp [h]

/-- **`firstK` is the scan's list**: on flags that mark `A` below `n`, the first `k` positions of
`A` are the first `k` listed positions. -/
theorem firstK_scan {n k : ℕ} {A : Finset ℕ} {f : ℕ → Word} (hA : ∀ j < n, j ∈ A ↔ f j ≠ 0) :
    firstK n A k = ((scanL n f).take k).toFinset := by
  rw [firstK, scanL]
  congr 2
  exact List.filter_congr fun j hj => by
    rw [List.mem_range] at hj
    simp only [decide_eq_decide]
    exact hA j hj

/-- **Decoding on the scanned positions** (`decode_agree` through `firstK_scan`): if the flags
mark an agreement set `A` of `u` with `Enc(c)` of at least `2^ℓ` positions below `n ≤ 2^20`,
interpolating on the first `2^ℓ` listed positions and running the butterflies returns `c`. -/
theorem scan_decode {ℓ n : ℕ} (hℓ : ℓ ≤ logNMax) (hn : n ≤ nMax) {A : Finset ℕ} {f : ℕ → Word}
    (hA : ∀ i ∈ A, i < n) (hAf : ∀ j < n, j ∈ A ↔ f j ≠ 0) (hcard : 2 ^ ℓ ≤ A.card)
    (c : Fin (2 ^ ℓ) → F) (u : ℕ → F) (hu : ∀ i ∈ A, u i = encN D c i) (i : Fin (2 ^ ℓ)) :
    bflyRun (M := F) D logNMax 0 ℓ (interpF D ((scanL n f).take (2 ^ ℓ)).toFinset u) i = c i := by
  rw [← firstK_scan hAf]
  exact decode_agree hℓ hn hA hcard c u hu i

/-! ## The semantics -/

theorem bW_eq_zero (b : Bool) : XOp.eq.eval (bW b) 0 = bW (!b) := by cases b <;> decide

theorem wf_appendIR (lb : ℕ) : WF (appendIR lb) := by
  simp +decide only [appendIR, WF, Prim.dst, uT1, rAd3, rCn, cTmp, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

theorem wf_scanBody (fb lb : ℕ) : WF (scanBody fb lb) := (wf_scanIR 0 0 fb lb).2.2.2.2

/-- **One position of the scan**: `j` is listed at `lb + c` iff `f j ≠ 0` and `c < k`. -/
theorem scanBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {fb lb j c k : ℕ} {f : ℕ → Word}
    (hlb : regs ≤ lb) (hlb2 : lb + k < 2 ^ 64) (hlbs : lb + k ≤ s.M.size) (hck : c ≤ k)
    (hfb0 : regs ≤ fb) (hfb : fb + j < 2 ^ 64) (hj : j + 1 < 2 ^ 64)
    (hJ : rd s.M rJs = toWord j) (hC : rd s.M rCn = toWord c) (hK : rd s.M rK3 = toWord k)
    (hF : rd s.M (fb + j) = f j) :
    rd (semXIR I (scanBody fb lb) s).M rJs = toWord (j + 1) ∧
    rd (semXIR I (scanBody fb lb) s).M rK3 = toWord k ∧
    (if f j ≠ 0 ∧ c < k then
      rd (semXIR I (scanBody fb lb) s).M rCn = toWord (c + 1) ∧
        rd (semXIR I (scanBody fb lb) s).M (lb + c) = toWord j ∧
        ∀ x, regs ≤ x → x ≠ lb + c → rd (semXIR I (scanBody fb lb) s).M x = rd s.M x
    else
      rd (semXIR I (scanBody fb lb) s).M rCn = toWord c ∧
        ∀ x, regs ≤ x → rd (semXIR I (scanBody fb lb) s).M x = rd s.M x) := by
  have hs := hM.1
  simp only [regs] at hs hlb hfb0
  have hT4 : cTmp = 4 := rfl
  -- the address and the flag
  have w1 : WF (.seq (.blk [.const uT1 (toWord fb), .op .add rAd3 rJs uT1]) (.seq (.load rFl rAd3)
      (.blk testPs))) := by simp +decide only [testPs, WF, Prim.dst, uT1, uT2, rAd3, rFl,
        List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM1 := inv_sem I w1 hM
  have hH1 := hframe I (.seq (.blk [.const uT1 (toWord fb), .op .add rAd3 rJs uT1])
    (.seq (.load rFl rAd3) (.blk testPs))) s (by simp +decide only [testPs, Lo, Prim.dst, regs, uT1,
      uT2, rAd3, rFl, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
      and_true])
  have z1 := size_sem I (.seq (.blk [.const uT1 (toWord fb), .op .add rAd3 rJs uT1])
    (.seq (.load rFl rAd3) (.blk testPs))) s
  have fr1 : ∀ r, (r = rJs ∨ r = rCn ∨ r = rK3) → rd (semXIR I (.seq (.blk [.const uT1 (toWord fb),
      .op .add rAd3 rJs uT1]) (.seq (.load rFl rAd3) (.blk testPs))) s).M r = rd s.M r :=
    fun r hr => frame I _ s w1 hM r (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide only [testPs, Writes, Prim.dst, uT1, uT2, rAd3, rFl, rJs, rCn, rK3,
        List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
  have fl1 : rd (semXIR I (.seq (.blk [.const uT1 (toWord fb), .op .add rAd3 rJs uT1])
      (.seq (.load rFl rAd3) (.blk testPs))) s).M rFl = bW (decide (f j ≠ 0) && decide (c < k)) := by
    simp (disch := first | decide | (simp only [size_set, uT1, uT2, rAd3, rFl]; omega)) only
      [semXIR, runPrims, testPs, List.foldl, Prim.run, rd_set_self, rd_set_ne]
    rw [hJ, add_toWord, toNat_toWord (by omega), Nat.add_comm j fb,
      rd_set_ne (show rAd3 ≠ fb + j by simp only [rAd3]; omega),
      rd_set_ne (show uT1 ≠ fb + j by simp only [uT1]; omega), hF, hC, hK, eq_bW (f j) 0, bW_eq_zero,
      ltW_toWord (by omega) (by omega), bW_and]
    simp only [ne_eq, decide_not]
  simp only [semXIR_seq] at hM1 hH1 z1 fr1 fl1
  rw [scanBody]
  simp only [semXIR_seq]
  generalize semXIR I (.blk testPs) (semXIR I (.load rFl rAd3) (semXIR I (.blk [.const uT1 (toWord fb),
    .op .add rAd3 rJs uT1]) s)) = s1 at hM1 hH1 z1 fr1 fl1
  have hs1 := hM1.1
  simp only [regs] at hs1
  have j1 := fr1 _ (.inl rfl)
  have c1 := fr1 _ (.inr (.inl rfl))
  have k1 := fr1 _ (.inr (.inr rfl))
  rw [semXIR_ite, fl1]
  -- the final `j += 1`
  have fin : ∀ s2 : St, Inv s2.M → rd s2.M rJs = toWord j →
      rd (semXIR I (.blk [.op .add rJs rJs cOne]) s2).M rJs = toWord (j + 1) ∧
      ∀ x, x ≠ rJs → rd (semXIR I (.blk [.op .add rJs rJs cOne]) s2).M x = rd s2.M x :=
    fun s2 h2 hj2 => ⟨by
      have := h2.1; simp only [regs] at this
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [rJs]; omega), hj2, show rd s2.M cOne = 1 from h2.2 0 (by decide),
        add_one_toWord],
      fun x hx => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hx) _⟩
  by_cases hb : f j ≠ 0 ∧ c < k
  · have e : bW (decide (f j ≠ 0) && decide (c < k)) ≠ 0 := by
      rw [decide_eq_true hb.1, decide_eq_true hb.2]; decide
    rw [if_neg e, if_pos hb]
    -- the append
    have a1 : rd (semXIR I (.blk [.const uT1 (toWord lb), .op .add rAd3 rCn uT1]) s1).M rAd3 =
        toWord (lb + c) := by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, uT1, rAd3]; omega)) only
        [rd_set_self, rd_set_ne]
      rw [c1, hC, add_toWord, Nat.add_comm]
    have b1 : ∀ x, x ≠ uT1 → x ≠ rAd3 → rd (semXIR I (.blk [.const uT1 (toWord lb),
        .op .add rAd3 rCn uT1]) s1).M x = rd s1.M x := fun x h1 h2 =>
      rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
    have hM2 := inv_sem I (P := .blk [.const uT1 (toWord lb), .op .add rAd3 rCn uT1])
      (by simp +decide only [WF, Prim.dst, uT1, rAd3, List.mem_cons, List.mem_nil_iff,
        forall_eq_or_imp, forall_eq, or_false, and_true]) hM1
    have z2 := size_sem I (.blk [.const uT1 (toWord lb), .op .add rAd3 rCn uT1]) s1
    rw [appendIR, semXIR_seq]
    generalize semXIR I (.blk [.const uT1 (toWord lb), .op .add rAd3 rCn uT1]) s1 = s2
      at a1 b1 hM2 z2
    have st : ∀ i, i ≠ cTmp → rd (storeM s2.M rAd3 rJs) i =
        if i = lb + c then rd s2.M rJs else rd s2.M i := fun i hi =>
      rd_storeM hM2 a1 (by simp only [regs]; omega) (by omega) (by omega) (by decide) (by decide) hi
    have hM3 : Inv (storeM s2.M rAd3 rJs) := inv_sem I (P := .store rAd3 rJs)
      (by simp +decide only [WF, rAd3, cTmp]) hM2
    rw [semXIR_seq]
    have e3 : semXIR I (.store rAd3 rJs) s2 = ⟨storeM s2.M rAd3 rJs, s2.o⟩ := rfl
    rw [e3]
    have hs3 := hM3.1
    simp only [regs] at hs3
    have r3 : ∀ r, r < 256 → r ≠ cTmp → rd (storeM s2.M rAd3 rJs) r = rd s2.M r := fun r hr h =>
      by rw [st r h, if_neg (by omega)]
    -- `cnt += 1`
    have c4 : rd (semXIR I (.blk [.op .add rCn rCn cOne]) ⟨storeM s2.M rAd3 rJs, s2.o⟩).M rCn =
        toWord (c + 1) := by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [rCn, size_storeM]; omega), r3 _ (by decide) (by decide),
        b1 _ (by decide) (by decide), c1, hC, r3 _ (by decide) (by decide),
        show rd s2.M cOne = 1 from hM2.2 0 (by decide), add_one_toWord]
    have b4 : ∀ x, x ≠ rCn → rd (semXIR I (.blk [.op .add rCn rCn cOne])
        ⟨storeM s2.M rAd3 rJs, s2.o⟩).M x = rd (storeM s2.M rAd3 rJs) x := fun x hx =>
      rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hx) _
    have hM4 := inv_sem I (P := .blk [.op .add rCn rCn cOne]) (s := ⟨storeM s2.M rAd3 rJs, s2.o⟩)
      (by simp +decide only [WF, Prim.dst, rCn]) hM3
    generalize semXIR I (.blk [.op .add rCn rCn cOne]) ⟨storeM s2.M rAd3 rJs, s2.o⟩ = s4
      at c4 b4 hM4
    obtain ⟨f1, f2⟩ := fin s4 hM4 (by
      rw [b4 _ (by decide), r3 _ (by decide) (by decide), b1 _ (by decide) (by decide), j1, hJ])
    refine ⟨f1, ?_, ?_, ?_, fun x hx hx2 => ?_⟩
    · rw [f2 _ (by decide), b4 _ (by decide), r3 _ (by decide) (by decide),
        b1 _ (by decide) (by decide), k1, hK]
    · rw [f2 _ (by decide), c4]
    · rw [f2 _ (by simp only [rJs]; omega), b4 _ (by simp only [rCn]; omega),
        st _ (by omega), if_pos rfl, b1 _ (by decide) (by decide), j1, hJ]
    · simp only [regs] at hx
      rw [f2 _ (by simp only [rJs]; omega), b4 _ (by simp only [rCn]; omega), st _ (by omega),
        if_neg hx2, b1 _ (by simp only [uT1]; omega) (by simp only [rAd3]; omega),
        hH1 x (by simp only [regs]; omega)]
  · have e : bW (decide (f j ≠ 0) && decide (c < k)) = 0 := by
      rw [show (decide (f j ≠ 0) && decide (c < k)) = false by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; tauto]; rfl
    rw [if_pos e, if_neg hb]
    have e2 : semXIR I (.blk []) s1 = s1 := by cases s1; rfl
    rw [e2]
    obtain ⟨f1, f2⟩ := fin s1 hM1 (by rw [j1, hJ])
    refine ⟨f1, by rw [f2 _ (by decide), k1, hK], by rw [f2 _ (by decide), c1, hC],
      fun x hx => ?_⟩
    simp only [regs] at hx
    rw [f2 _ (by simp only [rJs]; omega), hH1 x (by simp only [regs]; omega)]

/-- **The scan**: the count is `min(|L|, k)` and `lb + t` holds `L[t]` (`L = scanL n f`); the heap
outside `[lb, lb + k)` is kept. -/
theorem scanIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n k fb lb : ℕ} {f : ℕ → Word}
    (hlb : regs ≤ lb) (hlb2 : lb + k < 2 ^ 64) (hlbs : lb + k ≤ s.M.size)
    (hfb0 : regs ≤ fb) (hfb2 : fb + n < 2 ^ 64) (hn : n < 2 ^ 64) (hdisj : fb + n ≤ lb ∨ lb + k ≤ fb)
    (hF : ∀ j < n, rd s.M (fb + j) = f j) :
    rd (semXIR I (scanIR n k fb lb) s).M rCn = toWord (min (scanL n f).length k) ∧
    (∀ t < min (scanL n f).length k,
      rd (semXIR I (scanIR n k fb lb) s).M (lb + t) = toWord ((scanL n f).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < lb ∨ lb + k ≤ x) → rd (semXIR I (scanIR n k fb lb) s).M x = rd s.M x) ∧
    Inv (semXIR I (scanIR n k fb lb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hlb hfb0
  have w0 : WF (.blk [.const rJs 0, .const rCn 0, .const rK3 (toWord k), .const rN4 (toWord n)]) := by
    simp +decide only [WF, Prim.dst, rJs, rCn, rK3, rN4, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have hH0 := hframe I (.blk [.const rJs 0, .const rCn 0, .const rK3 (toWord k),
    .const rN4 (toWord n)]) s (by simp +decide only [Lo, Prim.dst, regs, rJs, rCn, rK3, rN4,
      List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
  have z0 := size_sem I (.blk [.const rJs 0, .const rCn 0, .const rK3 (toWord k),
    .const rN4 (toWord n)]) s
  have r0 : rd (semXIR I (.blk [.const rJs 0, .const rCn 0, .const rK3 (toWord k),
        .const rN4 (toWord n)]) s).M rJs = toWord 0 ∧
      rd (semXIR I (.blk [.const rJs 0, .const rCn 0, .const rK3 (toWord k),
        .const rN4 (toWord n)]) s).M rCn = toWord 0 ∧
      rd (semXIR I (.blk [.const rJs 0, .const rCn 0, .const rK3 (toWord k),
        .const rN4 (toWord n)]) s).M rK3 = toWord k ∧
      rd (semXIR I (.blk [.const rJs 0, .const rCn 0, .const rK3 (toWord k),
        .const rN4 (toWord n)]) s).M rN4 = toWord n := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rJs, rCn, rK3, rN4]; omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  rw [scanIR, semXIR_seq]
  generalize semXIR I (.blk [.const rJs 0, .const rCn 0, .const rK3 (toWord k),
    .const rN4 (toWord n)]) s = s0 at hM0 hH0 r0 z0
  obtain ⟨j0, c0, k0, n0⟩ := r0
  rw [loopK_eq I (scanBody fb lb) s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hn]
  have hE : ∀ i, i ≠ rC4 → i ≠ cTmp → rd (entryK rC4 rN4 (toWord n) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC4) (n := rN4) (K := toWord n) hM0 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rJs = toWord j ∧ rd s'.M rK3 = toWord k ∧
    rd s'.M rCn = toWord (min (scanL j f).length k) ∧
    (∀ t < min (scanL j f).length k, rd s'.M (lb + t) = toWord ((scanL j f).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < lb ∨ lb + k ≤ x) → rd s'.M x = rd s.M x)
  have step : ∀ j s', j < n → P j s' → P (j + 1) (decS rC4 (semXIR I (scanBody fb lb) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hF' : rd s'.M (fb + j) = f j := by
      rw [i7 _ (by simp only [regs]; omega) (by omega), hF j hj]
    obtain ⟨e1, e2, e3⟩ := scanBody_sem I s' i1 (f := f) (lb := lb) (c := min (scanL j f).length k)
      (by simp only [regs]; omega) hlb2 (by omega) (Nat.min_le_right _ _) hfb0 (by omega)
      (by omega) i3 i5 i4 hF'
    have hd : ∀ x, x ≠ rC4 → rd (decS rC4 (semXIR I (scanBody fb lb) s')).M x =
        rd (semXIR I (scanBody fb lb) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hM' := inv_decS (inv_sem I (wf_scanBody fb lb) i1) (show 4 ≤ rC4 by decide)
    have hz' : (decS rC4 (semXIR I (scanBody fb lb) s')).M.size = s.M.size := by
      rw [size_decS, size_sem, i2]
    dsimp only [P]
    rw [scanL_succ]
    by_cases hb : f j ≠ 0 ∧ min (scanL j f).length k < k
    · rw [if_pos hb] at e3
      obtain ⟨g1, g2, g3⟩ := e3
      have hlen : min (scanL j f ++ [j]).length k = min (scanL j f).length k + 1 := by
        rw [List.length_append, List.length_singleton]; omega
      rw [if_pos hb.1]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), e2],
        by rw [hd _ (by decide), g1, hlen], fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [rC4, regs] at *; omega)]
        rw [hlen] at ht
        by_cases htc : t = min (scanL j f).length k
        · subst htc
          rw [g2, List.getD_append_right _ _ _ _ (by omega)]
          have : min (scanL j f).length k = (scanL j f).length := by omega
          rw [this, Nat.sub_self]; rfl
        · rw [g3 _ (by simp only [regs]; omega) (by omega), i6 t (by omega),
            List.getD_append _ _ _ _ (by omega)]
      · rw [hd _ (by simp only [rC4, regs] at *; omega), g3 x hx (by omega), i7 x hx hx2]
    · rw [if_neg hb] at e3
      obtain ⟨g1, g2⟩ := e3
      have hsame : ∀ t < min (scanL j f ++ if f j ≠ 0 then [j] else []).length k,
          (scanL j f ++ if f j ≠ 0 then [j] else []).getD t 0 = (scanL j f).getD t 0 ∧
          t < min (scanL j f).length k := by
        intro t ht
        by_cases h1 : f j ≠ 0
        · rw [if_pos h1] at ht ⊢
          rw [List.length_append, List.length_singleton] at ht
          have : min (scanL j f).length k = k := by
            by_contra h; exact hb ⟨h1, by omega⟩
          exact ⟨List.getD_append _ _ _ _ (by omega), by omega⟩
        · rw [if_neg h1] at ht ⊢
          simp only [List.append_nil] at ht ⊢
          exact ⟨by simp, ht⟩
      have hmin : min (scanL j f ++ if f j ≠ 0 then [j] else []).length k =
          min (scanL j f).length k := by
        by_cases h1 : f j ≠ 0
        · rw [if_pos h1, List.length_append, List.length_singleton]
          have : min (scanL j f).length k = k := by
            by_contra h; exact hb ⟨h1, by omega⟩
          omega
        · rw [if_neg h1, List.append_nil]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), e2],
        by rw [hd _ (by decide), g1, hmin], fun t ht => ?_, fun x hx hx2 => ?_⟩
      · obtain ⟨q1, q2⟩ := hsame t ht
        rw [hd _ (by simp only [rC4, regs] at *; omega), g2 _ (by simp only [regs]; omega), q1,
          i6 t q2]
      · rw [hd _ (by simp only [rC4, regs] at *; omega), g2 x hx, i7 x hx hx2]
  have hP0 : P 0 ⟨entryK rC4 rN4 (toWord n) s0.M, s0.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun t ht => absurd ht (by simp [scanL]),
      fun x hx _ => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), j0]
    · dsimp only; rw [hE _ (by decide) (by decide), k0]
    · dsimp only; rw [hE _ (by decide) (by decide), c0]; simp [scanL]
    · dsimp only
      rw [hE _ (by simp only [rC4, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
  have := iterL_ind (f := semXIR I (scanBody fb lb)) (c := rC4) (m := n) P step n 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2, this.1⟩

/-! ## Controls (kernel runs on a toy memory) -/

namespace AgreeControls

/-- Store the flags `fs` at `256 …` (scratch registers `200`, `201`). -/
def putFlags : List Word → ℕ → XIR
  | [], _ => .blk []
  | f :: fs, j => .seq (.blk [.const 200 (toWord (256 + j)), .const 201 f])
      (.seq (.store 200 201) (putFlags fs (j + 1)))

/-- Output the count, then `m` list cells from `270`. -/
def outList : ℕ → XIR
  | 0 => .out rCn
  | m + 1 => .seq (outList m) (.seq (.blk [.const 200 (toWord (270 + m))])
      (.seq (.load 201 200) (.out 201)))

/-- The flags `0, 5, 0, 7, 7, 0, 1, 0` (`A = {1, 3, 4, 6}`), the scan for `k`, the output. -/
def toyScan (k m : ℕ) : XIR :=
  .seq (putFlags [0, 5, 0, 7, 7, 0, 1, 0] 0) (.seq (scanIR 8 k 256 270) (outList m))

/-- **Positive**: the first two flagged positions are `1, 3` (`firstK 8 A 2`). -/
theorem toyScan_two : (toProg 280 0 (toyScan 2 2)).run [] 1500 = some [2, 1, 3] := by
  decide +kernel

/-- **Limit**: asking for six lists all four (`min(|A|, k)`); the cells past the count stay `0`. -/
theorem toyScan_six : (toProg 280 0 (toyScan 6 6)).run [] 1500 = some [4, 1, 3, 4, 6, 0, 0] := by
  decide +kernel

end AgreeControls

end FR.X
