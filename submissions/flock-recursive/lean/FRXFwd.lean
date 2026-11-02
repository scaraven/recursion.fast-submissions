-- G6: this module also holds the former modules `FRXBfly`, `FRXEncB` (one section each, in import order).
import FRXBaryDefs

section G6_FRXBfly

-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, §6.5 `coeffs_spec`; stage S-H2, track L-ext).

/-!
# The butterflies on the machine: the semantics

* Loops by invariant (`iterL_ind`, `loopK_eq`); heap `F` loads and stores (`ldF_sem`, `stF_sem`).
* **`alphaIR_sem`**: `α = Σ_{i<20} [bit_i(base)] T(i)`, i.e. `wAt D 20 l base` on the table row of
  level `l`.
-/

namespace FR.X

open RecursionFast Finset

attribute [local irreducible] entryK storeM

/-! ## Loops by invariant -/

theorem iterL_ind {f : St → St} {c m : ℕ} (P : ℕ → St → Prop)
    (h : ∀ j s, j < m → P j s → P (j + 1) (decS c (f s))) :
    ∀ k j s, j + k ≤ m → P j s → P (j + k) (iterL f c k s)
  | 0, _, _, _, hP => hP
  | k + 1, j, s, hk, hP => by
    rw [show j + (k + 1) = (j + 1) + k by omega]
    exact iterL_ind P h k (j + 1) _ (by omega) (h j s (by omega) hP)

theorem loopK_eq (I : Array Word) {c n : ℕ} {K : Word} (b : XIR) (s : St) (hM : Inv s.M)
    (hc : 4 < c) (hcr : c < regs) (hn : n ≠ c) (hN : rd s.M n = K) :
    semXIR I (.loopK c n K b) s = iterL (semXIR I b) c K.toNat ⟨entryK c n K s.M, s.o⟩ := by
  simp only [semXIR, entryK_count hM hc hcr hn hN]

/-! ## Heap `F` elements -/

/-- **A heap load**: `d, d + 1 :=` cells `x, x + 1` (`M[p] = x`); `p1 := x + 1`. -/
theorem ldF_sem (I : Array Word) (s : St) (hM : Inv s.M) {d p p1 x : ℕ} (hd : 4 ≤ d)
    (hdr : d + 1 < regs)
    (hp1r : p1 < regs) (hpd : d ≠ p) (hp1d : p1 ≠ d) (hp1d' : p1 ≠ d + 1)
    (hP : rd s.M p = toWord x) (hx : regs ≤ x) (hx2 : x + 1 < 2 ^ 64) :
    rdF (semXIR I (ldF d p p1) s).M d = rdF s.M x ∧
    rd (semXIR I (ldF d p p1) s).M p1 = toWord (x + 1) ∧
    ∀ i, i ≠ d → i ≠ d + 1 → i ≠ p1 → rd (semXIR I (ldF d p p1) s).M i = rd s.M i := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs hdr hp1r hx
  have e : semXIR I (ldF d p p1) s = ⟨((s.M.setIfInBounds d (rd s.M (rd s.M p).toNat)).setIfInBounds
      p1 (XOp.add.eval (rd (s.M.setIfInBounds d (rd s.M (rd s.M p).toNat)) p)
        (rd (s.M.setIfInBounds d (rd s.M (rd s.M p).toNat)) cOne))).setIfInBounds (d + 1)
      (rd ((s.M.setIfInBounds d (rd s.M (rd s.M p).toNat)).setIfInBounds p1
        (XOp.add.eval (rd (s.M.setIfInBounds d (rd s.M (rd s.M p).toNat)) p)
          (rd (s.M.setIfInBounds d (rd s.M (rd s.M p).toNat)) cOne)))
        (rd ((s.M.setIfInBounds d (rd s.M (rd s.M p).toNat)).setIfInBounds p1
          (XOp.add.eval (rd (s.M.setIfInBounds d (rd s.M (rd s.M p).toNat)) p)
            (rd (s.M.setIfInBounds d (rd s.M (rd s.M p).toNat)) cOne))) p1).toNat), s.o⟩ := rfl
  rw [e]
  generalize hM1 : s.M.setIfInBounds d (rd s.M (rd s.M p).toNat) = M1
  have hz1 : M1.size = s.M.size := by rw [← hM1, size_set]
  have a1 : rd M1 p = toWord x := by rw [← hM1, rd_set_ne hpd, hP]
  have a2 : rd M1 cOne = 1 := by
    rw [← hM1, rd_set_ne (by simp only [cOne]; omega), h1]
  have a3 : rd M1 d = rd s.M x := by
    rw [← hM1, rd_set_self (by omega), hP, toNat_toWord (by omega)]
  have a4 : ∀ i, i ≠ d → rd M1 i = rd s.M i := fun i hi => by rw [← hM1, rd_set_ne (Ne.symm hi)]
  rw [a1, a2, add_one_toWord]
  generalize hM2 : M1.setIfInBounds p1 (toWord (x + 1)) = M2
  have hz2 : M2.size = s.M.size := by rw [← hM2, size_set, hz1]
  have b1 : rd M2 p1 = toWord (x + 1) := by rw [← hM2, rd_set_self (by omega)]
  have b2 : ∀ i, i ≠ p1 → rd M2 i = rd M1 i := fun i hi => by rw [← hM2, rd_set_ne (Ne.symm hi)]
  rw [b1, toNat_toWord hx2]
  refine ⟨?_, ?_, fun i i1 i2 i3 => ?_⟩
  · simp only [rdF, rdB]
    rw [rd_set_ne (by omega), rd_set_self (by omega), b2 _ (Ne.symm hp1d), a3, b2 _ (by omega),
      a4 _ (by omega)]
  · rw [rd_set_ne (Ne.symm hp1d'), b1]
  · rw [rd_set_ne (Ne.symm i2), b2 _ i3, a4 _ i1]

/-- **A heap store**: cells `x, x + 1 :=` registers `v, v + 1` (`M[p] = x`); `p1 := x + 1`. -/
theorem stF_sem (I : Array Word) (s : St) (hM : Inv s.M) {p p1 v x : ℕ} (hp1 : 4 < p1)
    (hp1r : p1 < regs) (hpT : p ≠ cTmp) (hp1p : p1 ≠ p) (hvT : v ≠ cTmp) (hv1T : v + 1 ≠ cTmp)
    (hp1v : p1 ≠ v) (hp1v1 : p1 ≠ v + 1) (hvr : v + 1 < regs)
    (hP : rd s.M p = toWord x) (hx : regs ≤ x) (hx2 : x + 1 < 2 ^ 64) (hxs : x + 1 < s.M.size) :
    rdF (semXIR I (stF p p1 v) s).M x = rdF s.M v ∧
    (∀ i, i ≠ x → i ≠ x + 1 → i ≠ p1 → i ≠ cTmp → rd (semXIR I (stF p p1 v) s).M i = rd s.M i) ∧
    Inv (semXIR I (stF p p1 v) s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs hp1r hx hvr
  have hT4 : cTmp = 4 := rfl
  have hw : WF (stF p p1 v) := by simp [stF, WF, Prim.dst, hpT]; omega
  have hM' := inv_sem I hw hM
  refine ⟨?_, ?_, hM'⟩ <;>
  simp only [stF, semXIR] <;>
  generalize hM1 : runPrims [.op .add p1 p cOne] s.M = M1
  · have hz1 : M1.size = s.M.size := by rw [← hM1]; simp [runPrims, Prim.run]
    have a1 : rd M1 p = toWord x := by
      rw [← hM1]; simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_ne hp1p, hP]
    have a2 : rd M1 p1 = toWord (x + 1) := by
      rw [← hM1]; simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by omega), hP, h1, add_one_toWord]
    have a4 : ∀ i, i ≠ p1 → rd M1 i = rd s.M i := fun i hi => by
      rw [← hM1]; simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_ne (Ne.symm hi)]
    have hI1 : Inv M1 := inv_of_frame hM hz1 fun i hi => a4 i (by omega)
    have st1 : ∀ i, i ≠ cTmp → rd (storeM M1 p v) i = if i = x then rd M1 v else rd M1 i :=
      fun i hi => rd_storeM hI1 a1 (by simp only [regs]; omega) (by omega) (by omega) hpT hvT hi
    have hI2 : Inv (storeM M1 p v) := inv_of_frame hI1 (size_storeM ..) fun i hi => by
      rw [st1 i (by omega), if_neg (by omega)]
    have a5 : rd (storeM M1 p v) p1 = toWord (x + 1) := by
      rw [st1 _ (by omega), if_neg (by omega), a2]
    have st2 : ∀ i, i ≠ cTmp → rd (storeM (storeM M1 p v) p1 (v + 1)) i =
        if i = x + 1 then rd (storeM M1 p v) (v + 1) else rd (storeM M1 p v) i :=
      fun i hi => rd_storeM hI2 a5 (by simp only [regs]; omega) hx2 (by rw [size_storeM, hz1]; omega)
        (by omega) hv1T hi
    simp only [rdF, rdB]
    rw [st2 _ (by omega), if_neg (by omega), st1 _ (by omega),
      if_pos rfl, st2 _ (by omega), if_pos rfl,
      st1 _ hv1T, if_neg (by omega), a4 _ (Ne.symm hp1v), a4 _ (Ne.symm hp1v1)]
  · have hz1 : M1.size = s.M.size := by rw [← hM1]; simp [runPrims, Prim.run]
    have a1 : rd M1 p = toWord x := by
      rw [← hM1]; simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_ne hp1p, hP]
    have a2 : rd M1 p1 = toWord (x + 1) := by
      rw [← hM1]; simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by omega), hP, h1, add_one_toWord]
    have a4 : ∀ i, i ≠ p1 → rd M1 i = rd s.M i := fun i hi => by
      rw [← hM1]; simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_ne (Ne.symm hi)]
    have hI1 : Inv M1 := inv_of_frame hM hz1 fun i hi => a4 i (by omega)
    have st1 : ∀ i, i ≠ cTmp → rd (storeM M1 p v) i = if i = x then rd M1 v else rd M1 i :=
      fun i hi => rd_storeM hI1 a1 (by simp only [regs]; omega) (by omega) (by omega) hpT hvT hi
    have hI2 : Inv (storeM M1 p v) := inv_of_frame hI1 (size_storeM ..) fun i hi => by
      rw [st1 i (by omega), if_neg (by omega)]
    have a5 : rd (storeM M1 p v) p1 = toWord (x + 1) := by
      rw [st1 _ (by omega), if_neg (by omega), a2]
    have st2 : ∀ i, i ≠ cTmp → rd (storeM (storeM M1 p v) p1 (v + 1)) i =
        if i = x + 1 then rd (storeM M1 p v) (v + 1) else rd (storeM M1 p v) i :=
      fun i hi => rd_storeM hI2 a5 (by simp only [regs]; omega) hx2 (by rw [size_storeM, hz1]; omega)
        (by omega) hv1T hi
    intro i i1 i2 i3 i4
    rw [st2 _ i4, if_neg i2, st1 _ i4, if_neg i1, a4 _ i3]

/-! ## Word facts -/

theorem divu_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.divu.eval (toWord a) (toWord b) = toWord (a / b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_udiv, toNat_toWord ha, toNat_toWord hb,
    toNat_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem remu_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.remu.eval (toWord a) (toWord b) = toWord (a % b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_umod, toNat_toWord ha, toNat_toWord hb,
    toNat_toWord (lt_of_le_of_lt (Nat.mod_le _ _) ha)]

theorem mul_toWord (a b : ℕ) : XOp.mul.eval (toWord a) (toWord b) = toWord (a * b) :=
  (BitVec.ofNat_mul a b).symm

/-- The branch-free bit mask: `v` if bit `j` of `b` is set, else `0`. -/
theorem mask_bit (v : Word) {b j : ℕ} (hb : b < 2 ^ 64) (hj : j < 64) :
    XOp.and.eval v (XOp.sub.eval 0 (XOp.and.eval (XOp.shr.eval (toWord b) (toWord j)) 1)) =
      if b.testBit j then v else 0 := by
  rw [shr_toWord hb hj, and_one_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) hb), bit_eq]
  by_cases h : b.testBit j
  · rw [if_pos h, if_pos h]
    show v &&& (0 - toWord 1) = v
    rw [show (0 : Word) - toWord 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
  · rw [if_neg h, if_neg h]
    show v &&& (0 - toWord 0) = 0
    rw [show (0 : Word) - toWord 0 = 0 by decide]
    exact BitVec.eq_of_toNat_eq (by simp)

theorem xor_zero' (a : Word) : a ^^^ 0 = a := BitVec.eq_of_toNat_eq (by simp)

/-- Masked accumulation of an `F` element, word by word. -/
theorem rdF_acc (a₀ a₁ g₀ g₁ : Word) (p : Prop) [Decidable p] :
    (⟨wB (a₀ ^^^ (if p then g₀ else 0)), wB (a₁ ^^^ (if p then g₁ else 0))⟩ : F) =
      ⟨wB a₀, wB a₁⟩ + if p then ⟨wB g₀, wB g₁⟩ else 0 := by
  by_cases h : p
  · simp only [if_pos h]; rfl
  · simp only [if_neg h, add_zero, xor_zero']

/-! ## `α` -/

theorem loK_alphaIR : LoK alphaIR := by
  simp +decide only [alphaIR, alphaBody, ldF, LoK, Prim.dst, regs, rBit, uT1, rTa, rTa1, fG, fAl,
    uI, rN2, rC2, and_true]

theorem rdF_decS {c a : ℕ} (s : St) (h0 : c ≠ a) (h1 : c ≠ a + 1) :
    rdF (decS c s).M a = rdF s.M a := rdF_eq (rd_decS h0 s) (rd_decS h1 s)

/-- **One bit of `α`.** -/
theorem alphaBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {base ta j : ℕ} {T : ℕ → F}
    (hb : base < 2 ^ 64) (hj : j < 20) (hta : regs ≤ ta) (hta2 : ta + 40 < 2 ^ 64)
    (hBs : rd s.M rBs = toWord base) (hI : rd s.M uI = toWord j)
    (hTa : rd s.M rTa = toWord (ta + 2 * j)) (hT : rdF s.M (ta + 2 * j) = T j) :
    rdF (semXIR I alphaBody s).M fAl = rdF s.M fAl + (if base.testBit j then T j else 0) ∧
    rd (semXIR I alphaBody s).M uI = toWord (j + 1) ∧
    rd (semXIR I alphaBody s).M rTa = toWord (ta + 2 * (j + 1)) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs hta
  have w1 : WF (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
      .op .sub rBit uT1 rBit]) := by simp +decide only [WF, Prim.dst, rBit, uT1]
  have hM1 := inv_sem I w1 hM
  have hH1 := hframe I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
      .op .sub rBit uT1 rBit]) s (by simp +decide only [Lo, Prim.dst, regs, rBit, uT1])
  have r1 : rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M rBit =
        XOp.sub.eval 0 (XOp.and.eval (XOp.shr.eval (toWord base) (toWord j)) 1) ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M rTa = toWord (ta + 2 * j) ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M uI = toWord j ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M fAl = rd s.M fAl ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M (fAl + 1) = rd s.M (fAl + 1) ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M cOne = 1 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rBit, uT1]; omega)) only
      [rd_set_self, rd_set_ne]
    · rw [hBs, hI, h1]
    · exact hTa
    · exact hI
    · exact h1
  rw [alphaBody, semXIR_seq]
  generalize semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
    .op .sub rBit uT1 rBit]) s = s1 at hM1 hH1 r1
  obtain ⟨b1, a1, i1, f1, f1', o1⟩ := r1
  have hs1 := hM1.1
  simp only [regs] at hs1
  obtain ⟨l1, l2, l3⟩ := ldF_sem I s1 hM1 (d := fG) (p := rTa) (p1 := rTa1) (x := ta + 2 * j)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a1
    (by simp only [regs]; omega) (by omega)
  rw [semXIR_seq]
  have hM2 := inv_sem I (P := ldF fG rTa rTa1) (by simp +decide only [ldF, WF, Prim.dst, fG, rTa1,
    and_true]) hM1
  generalize semXIR I (ldF fG rTa rTa1) s1 = s2 at l1 l2 l3 hM2
  have hs2 := hM2.1
  simp only [regs] at hs2
  have g2 : rdF s2.M fG = T j := by
    rw [l1, ← hT]; exact rdF_eq (hH1 _ (by simp only [regs]; omega)) (hH1 _ (by simp only [regs]; omega))
  have k1 : rd s2.M rBit = XOp.sub.eval 0 (XOp.and.eval (XOp.shr.eval (toWord base) (toWord j)) 1) :=
    (l3 _ (by decide) (by decide) (by decide)).trans b1
  have k2 : rd s2.M fAl = rd s.M fAl := (l3 _ (by decide) (by decide) (by decide)).trans f1
  have k3 : rd s2.M (fAl + 1) = rd s.M (fAl + 1) := (l3 _ (by decide) (by decide) (by decide)).trans f1'
  have k4 : rd s2.M rTa = toWord (ta + 2 * j) := (l3 _ (by decide) (by decide) (by decide)).trans a1
  have k5 : rd s2.M uI = toWord j := (l3 _ (by decide) (by decide) (by decide)).trans i1
  have k6 : rd s2.M cOne = 1 := (l3 _ (by decide) (by decide) (by decide)).trans o1
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_, ?_⟩
  · simp only [rdF, rdB]
    simp (disch := first | decide | (simp only [size_set, fG, fAl, uT1, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [k1, k2, k3]
    show (⟨wB (rd s.M fAl ^^^ XOp.and.eval (rd s2.M fG) (XOp.sub.eval 0 (XOp.and.eval
      (XOp.shr.eval (toWord base) (toWord j)) 1))), wB (rd s.M (fAl + 1) ^^^ XOp.and.eval
      (rd s2.M (fG + 1)) (XOp.sub.eval 0 (XOp.and.eval (XOp.shr.eval (toWord base) (toWord j))
      1)))⟩ : F) = _
    rw [mask_bit _ hb (by omega), mask_bit _ hb (by omega), rdF_acc, ← g2]
    rfl
  · simp (disch := first | decide | (simp only [size_set, fG, fAl, uT1, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [k5, k6, add_one_toWord]
  · simp (disch := first | decide | (simp only [size_set, fG, fAl, uT1, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [k4, show (2 : Word) = toWord 2 from rfl, add_toWord]
    congr 1

/-- **`α`**: the sum over the bits `i < 20` of `base` of the table entries `T i` at `ta + 2i`
(the row at `rTr`). -/
theorem alphaIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {base ta : ℕ} {T : ℕ → F}
    (hb : base < 2 ^ 64) (hta : regs ≤ ta) (hta2 : ta + 40 < 2 ^ 64)
    (hBs : rd s.M rBs = toWord base) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < 20, rdF s.M (ta + 2 * i) = T i) :
    rdF (semXIR I alphaIR s).M fAl = ∑ i ∈ range 20, if base.testBit i then T i else 0 := by
  have hs := hM.1
  simp only [regs] at hs hta
  have w0 : WF (.blk [.const fAl 0, .const (fAl + 1) 0, .const uI 0, .op .or rTa rTr rTr,
      .const rN2 20]) := by simp +decide only [WF, Prim.dst, fAl, uI, rTa, rN2]
  have hM0 := inv_sem I w0 hM
  have hH0 := hframe I (.blk [.const fAl 0, .const (fAl + 1) 0, .const uI 0, .op .or rTa rTr rTr,
      .const rN2 20]) s (by simp +decide only [Lo, Prim.dst, regs, fAl, uI, rTa, rN2])
  have r0 : rdF (semXIR I (.blk [.const fAl 0, .const (fAl + 1) 0, .const uI 0,
        .op .or rTa rTr rTr, .const rN2 20]) s).M fAl = 0 ∧
      rd (semXIR I (.blk [.const fAl 0, .const (fAl + 1) 0, .const uI 0,
        .op .or rTa rTr rTr, .const rN2 20]) s).M uI = toWord 0 ∧
      rd (semXIR I (.blk [.const fAl 0, .const (fAl + 1) 0, .const uI 0,
        .op .or rTa rTr rTr, .const rN2 20]) s).M rTa = toWord (ta + 2 * 0) ∧
      rd (semXIR I (.blk [.const fAl 0, .const (fAl + 1) 0, .const uI 0,
        .op .or rTa rTr rTr, .const rN2 20]) s).M rBs = toWord base ∧
      rd (semXIR I (.blk [.const fAl 0, .const (fAl + 1) 0, .const uI 0,
        .op .or rTa rTr rTr, .const rN2 20]) s).M rN2 = 20 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, rdF, rdB]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, fAl, uI, rTa, rN2]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rfl
    · rw [hTr, or_self_eval]; rfl
    · exact hBs
  rw [alphaIR, semXIR_seq]
  generalize semXIR I (.blk [.const fAl 0, .const (fAl + 1) 0, .const uI 0, .op .or rTa rTr rTr,
    .const rN2 20]) s = s0 at hM0 hH0 r0
  obtain ⟨z0, i0, t0, b0, n0⟩ := r0
  rw [loopK_eq I alphaBody s0 hM0 (by decide) (by decide) (by decide) n0]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 20 s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := 20) hM0 (by decide)
  have wb : WF alphaBody := wf_alphaIR.2.2.2.2
  have lb : LoK alphaBody := loK_alphaIR.2.2
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ rd s'.M uI = toWord j ∧
    rd s'.M rTa = toWord (ta + 2 * j) ∧ rd s'.M rBs = toWord base ∧
    (∀ x, regs ≤ x → rd s'.M x = rd s.M x) ∧
    rdF s'.M fAl = ∑ i ∈ range j, if base.testBit i then T i else 0
  have step : ∀ j s', j < 20 → P j s' → P (j + 1) (decS rC2 (semXIR I alphaBody s')) := by
    rintro j s' hj ⟨q1, q2, q3, q4, q5, q6⟩
    have hTj : rdF s'.M (ta + 2 * j) = T j := by
      rw [← hT j hj]
      exact rdF_eq (q5 (ta + 2 * j) (by simp only [regs]; omega))
        (q5 (ta + 2 * j + 1) (by simp only [regs]; omega))
    obtain ⟨e1, e2, e3⟩ := alphaBody_sem I s' q1 (T := T) hb hj (by simp only [regs]; omega) hta2
      q4 q2 q3 hTj
    refine ⟨inv_decS (inv_sem I wb q1) (by decide), ?_, ?_, ?_, fun x hx => ?_, ?_⟩
    · rw [rd_decS (by decide), e2]
    · rw [rd_decS (by decide), e3]
    · rw [rd_decS (by decide), frame I _ s' wb q1 _ (by decide) (by
        simp +decide only [alphaBody, ldF, Writes, Prim.dst, rBit, uT1, rTa, rTa1, fG, fAl, uI, rBs,
          or_false]), q4]
    · rw [rd_decS (by simp only [rC2, regs] at *; omega), hframeK I _ s' lb x hx, q5 x hx]
    · rw [rdF_decS _ (by decide) (by decide), e1, q6, sum_range_succ]
  have hP0 : P 0 ⟨entryK rC2 rN2 20 s0.M, s0.o⟩ := by
    refine ⟨hME, ?_, ?_, ?_, fun x hx => ?_, ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), i0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only; rw [hE _ (by decide) (by decide), b0]
    · dsimp only
      rw [hE _ (by simp only [rC2, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
    · dsimp only
      rw [rdF_eq (hE _ (by decide) (by decide)) (hE _ (by decide) (by decide)), z0]; rfl
  have := iterL_ind (f := semXIR I alphaBody) (c := rC2) (m := 20) P step 20 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  exact this.2.2.2.2.2

/-! ## The pairs of a level (pure) -/

/-- The block base of pair `q` at level `l`. -/
def baseP (l q : ℕ) : ℕ := q / 2 ^ l * 2 ^ (l + 1)

/-- The low position of pair `q`. -/
def loP (l q : ℕ) : ℕ := baseP l q + q % 2 ^ l

/-- The high position of pair `q`. -/
def hiP (l q : ℕ) : ℕ := loP l q + 2 ^ l

/-- The pair of position `i`. -/
def pairOf (l i : ℕ) : ℕ := i / 2 ^ (l + 1) * 2 ^ l + i % 2 ^ l

theorem divmod_lin {a x P : ℕ} (hx : x < P) : (a * P + x) / P = a ∧ (a * P + x) % P = x := by
  have hP : 0 < P := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hx, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

theorem pow_succ' (l : ℕ) : 2 ^ (l + 1) = 2 ^ l + 2 ^ l := by rw [pow_succ]; ring

theorem loP_div (l q : ℕ) : loP l q / 2 ^ (l + 1) = q / 2 ^ l ∧
    loP l q % 2 ^ (l + 1) = q % 2 ^ l := by
  have h := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  exact divmod_lin (by rw [pow_succ']; omega)

theorem hiP_div (l q : ℕ) : hiP l q / 2 ^ (l + 1) = q / 2 ^ l ∧
    hiP l q % 2 ^ (l + 1) = q % 2 ^ l + 2 ^ l := by
  have h := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  have := divmod_lin (a := q / 2 ^ l) (x := q % 2 ^ l + 2 ^ l) (P := 2 ^ (l + 1))
    (by rw [pow_succ']; omega)
  simpa [hiP, loP, baseP, Nat.add_assoc] using this

theorem pairOf_loP (l q : ℕ) : pairOf l (loP l q) = q := by
  have hb : loP l q = q % 2 ^ l + q / 2 ^ l * 2 * 2 ^ l := by rw [loP, baseP, pow_succ]; ring
  rw [pairOf, (loP_div l q).1, show loP l q % 2 ^ l = q % 2 ^ l by
    rw [hb, Nat.add_mul_mod_self_right, Nat.mod_mod]]
  exact Nat.div_add_mod' q _

theorem pairOf_hiP (l q : ℕ) : pairOf l (hiP l q) = q := by
  have hb : hiP l q = q % 2 ^ l + (q / 2 ^ l * 2 + 1) * 2 ^ l := by
    rw [hiP, loP, baseP, pow_succ]; ring
  rw [pairOf, (hiP_div l q).1, show hiP l q % 2 ^ l = q % 2 ^ l by
    rw [hb, Nat.add_mul_mod_self_right, Nat.mod_mod]]
  exact Nat.div_add_mod' q _

/-- A position of pair `q` is its low or its high position. -/
theorem pair_cases {l i q : ℕ} (h : pairOf l i = q) : i = loP l q ∨ i = hiP l q := by
  subst h
  have hP : 0 < 2 ^ l := by positivity
  have hi := Nat.div_add_mod' i (2 ^ (l + 1))
  have hr := Nat.mod_lt i (show 0 < 2 ^ (l + 1) by positivity)
  rw [pow_succ'] at hr
  have hm : i % 2 ^ l = i % 2 ^ (l + 1) % 2 ^ l := by
    rw [pow_succ, Nat.mod_mul_right_mod]
  by_cases hx : i % 2 ^ (l + 1) < 2 ^ l
  · left
    have e : i % 2 ^ l = i % 2 ^ (l + 1) := by rw [hm, Nat.mod_eq_of_lt hx]
    obtain ⟨d1, d2⟩ := divmod_lin (a := i / 2 ^ (l + 1)) hx
    rw [loP, baseP, pairOf, e, d1, d2]
    omega
  · right
    have e : i % 2 ^ l = i % 2 ^ (l + 1) - 2 ^ l := by
      rw [hm, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    obtain ⟨d1, d2⟩ := divmod_lin (a := i / 2 ^ (l + 1)) (P := 2 ^ l)
      (x := i % 2 ^ (l + 1) - 2 ^ l) (by omega)
    rw [hiP, loP, baseP, pairOf, e, d1, d2]
    omega

/-- The positions of a pair lie in the row. -/
theorem hiP_lt {ℓ l q : ℕ} (hl : l < ℓ) (hq : q < 2 ^ (ℓ - 1)) : hiP l q < 2 ^ ℓ := by
  have hP : 0 < 2 ^ l := by positivity
  have e1 : 2 ^ (ℓ - 1) = 2 ^ (ℓ - 1 - l) * 2 ^ l := by rw [← pow_add]; congr 1; omega
  have e2 : 2 ^ ℓ = 2 ^ (ℓ - 1 - l) * 2 ^ (l + 1) := by rw [← pow_add]; congr 1; omega
  have hd : q / 2 ^ l < 2 ^ (ℓ - 1 - l) := by rw [Nat.div_lt_iff_lt_mul hP, ← e1]; exact hq
  have hm := Nat.mod_lt q hP
  have h3 : (q / 2 ^ l + 1) * 2 ^ (l + 1) ≤ 2 ^ (ℓ - 1 - l) * 2 ^ (l + 1) :=
    Nat.mul_le_mul_right _ hd
  have h2 := pow_succ' l
  rw [hiP, loP, baseP, e2]
  rw [Nat.add_mul, Nat.one_mul] at h3
  omega

theorem loP_lt_hiP (l q : ℕ) : loP l q < hiP l q := by
  have : 0 < 2 ^ l := by positivity
  simp only [hiP]; omega

/-- Every position of the row is in a pair below `2^(ℓ−1)`. -/
theorem pairOf_lt {ℓ l i : ℕ} (hl : l < ℓ) (hi : i < 2 ^ ℓ) : pairOf l i < 2 ^ (ℓ - 1) := by
  have hP : 0 < 2 ^ l := by positivity
  have e1 : 2 ^ (ℓ - 1) = 2 ^ (ℓ - 1 - l) * 2 ^ l := by rw [← pow_add]; congr 1; omega
  have e2 : 2 ^ ℓ = 2 ^ (ℓ - 1 - l) * 2 ^ (l + 1) := by rw [← pow_add]; congr 1; omega
  have hd : i / 2 ^ (l + 1) < 2 ^ (ℓ - 1 - l) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e2]; exact hi
  have h3 : (i / 2 ^ (l + 1) + 1) * 2 ^ l ≤ 2 ^ (ℓ - 1 - l) * 2 ^ l := Nat.mul_le_mul_right _ hd
  have hm := Nat.mod_lt i hP
  rw [pairOf, e1]
  rw [Nat.add_mul, Nat.one_mul] at h3
  omega

/-- **`bflyLevel` at a pair's positions** (characteristic 2: `u − α (w − u) = u + α (w + u)`). -/
theorem bflyLevel_lo (pt : ℕ → F) (N l q : ℕ) (Y : ℕ → F) :
    bflyLevel (M := F) pt N 0 l Y (loP l q) =
      Y (loP l q) + wAt pt N l (baseP l q) * (Y (hiP l q) + Y (loP l q)) := by
  have hm := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  obtain ⟨d1, d2⟩ := loP_div l q
  simp only [bflyLevel, d1, d2, Nat.mod_mod, if_pos hm, Nat.zero_add]
  rw [show q / 2 ^ l * 2 ^ (l + 1) + 2 ^ l + q % 2 ^ l = hiP l q by
    simp only [hiP, loP, baseP]; omega]
  rfl

theorem bflyLevel_hi (pt : ℕ → F) (N l q : ℕ) (Y : ℕ → F) :
    bflyLevel (M := F) pt N 0 l Y (hiP l q) = Y (hiP l q) + Y (loP l q) := by
  have hm := Nat.mod_lt q (show 0 < 2 ^ l by positivity)
  obtain ⟨d1, d2⟩ := hiP_div l q
  simp only [bflyLevel, d1, d2, if_neg (show ¬ (q % 2 ^ l + 2 ^ l < 2 ^ l) by omega),
    Nat.add_mod_right, Nat.mod_mod]
  rw [show q / 2 ^ l * 2 ^ (l + 1) + 2 ^ l + q % 2 ^ l = hiP l q by
    simp only [hiP, loP, baseP]; omega]
  rfl

/-! ## One butterfly on the machine -/

/-- `simp` form of `mulF`'s heap frame (with `mulF_wf_iff`, `mulF_writes_iff`): the `Lo` side
conditions below never unfold `mulF`'s primitives (G2: elaboration time). -/
theorem mulF_lo_iff {d a b : ℕ} (hd : d < 255) : Lo (mulF d a b) ↔ True :=
  iff_true_intro fun p hp => by have := mulFC_dst d a b p hp; simp only [regs]; omega

theorem wf_arithIR : WF arithIR := by
  simp +decide only [arithIR, ldF, addF, addFC, WF, Prim.dst, fU, fW, fH, fT, fN, rAL1, rAH1,
    mulF_wf_iff, mulF_writes_iff, and_true]

theorem lo_arithIR : Lo arithIR := by
  simp +decide only [arithIR, ldF, addF, addFC, Lo, Prim.dst, regs, fU, fW, fH, fT, fN, rAL1, rAH1,
    mulF_lo_iff, and_true]

theorem wf_pairBody : WF pairBody := by
  simp +decide only [pairBody, pairPs, arithIR, alphaIR, alphaBody, ldF, stF, addF, addFC, WF,
    Writes, Prim.dst, rQ, uX, uT1, uT2, rBs, rAL, rAL1, rAH, rAH1, rTa, rTa1, rBit, uI, rC2, rN2,
    fAl, fU, fW, fH, fT, fN, fG, cTmp, regs, mulF_wf_iff, mulF_writes_iff, or_false, and_true]

/-- **The arithmetic**: `fN := U + α (W + U)`, `fH := W + U` for the heap elements `U` at `a`
and `W` at `b`, `α` in `fAl`. -/
theorem arith_sem (I : Array Word) (s : St) (hM : Inv s.M) {a b : ℕ} (ha : regs ≤ a)
    (ha2 : a + 1 < 2 ^ 64) (hb : regs ≤ b) (hb2 : b + 1 < 2 ^ 64)
    (hAL : rd s.M rAL = toWord a) (hAH : rd s.M rAH = toWord b) :
    rdF (semXIR I arithIR s).M fN = rdF s.M a + rdF s.M fAl * (rdF s.M b + rdF s.M a) ∧
    rdF (semXIR I arithIR s).M fH = rdF s.M b + rdF s.M a := by
  have hs := hM.1
  simp only [regs] at hs ha hb
  rw [arithIR, semXIR_seq]
  obtain ⟨u1, -, u3⟩ := ldF_sem I s hM (d := fU) (p := rAL) (p1 := rAL1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hAL (by simp only [regs]; omega) ha2
  have hM1 := inv_sem I (P := ldF fU rAL rAL1) (by simp +decide only [ldF, WF, Prim.dst, fU, rAL1,
    and_true]) hM
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
  have hM2 := inv_sem I (P := ldF fW rAH rAH1) (by simp +decide only [ldF, WF, Prim.dst, fW, rAH1,
    and_true]) hM1
  generalize semXIR I (ldF fW rAH rAH1) s1 = s2 at w1 w3 hM2
  have hu2 : rdF s2.M fU = rdF s.M a :=
    (rdF_eq (w3 _ (by decide) (by decide) (by decide)) (w3 _ (by decide) (by decide) (by decide))).trans u1
  have hal2 : rdF s2.M fAl = rdF s.M fAl :=
    (rdF_eq (w3 _ (by decide) (by decide) (by decide)) (w3 _ (by decide) (by decide) (by decide))).trans hal1
  have hw2 : rdF s2.M fW = rdF s.M b := w1.trans hb1
  rw [semXIR_seq]
  have h3 := addF_sem (I := I) (s := s2) hM2 (d := fH) (a := fW) (b := fU) (by decide) (by decide)
    (by decide)
  have f3 : ∀ i, i ≠ fH → i ≠ fH + 1 → rd (semXIR I (addF fH fW fU) s2).M i = rd s2.M i :=
    fun i h1 h2 => addFC_frame _ _ _ h1 h2 _
  have hM3 := inv_sem I (wf_addF fH fW fU (by decide)) hM2
  generalize semXIR I (addF fH fW fU) s2 = s3 at h3 f3 hM3
  rw [semXIR_seq]
  have h4 := mulF_sem (I := I) (s := s3) hM3 (d := fT) (a := fAl) (b := fH) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ i, 15 ≤ i → i ≠ fT → i ≠ fT + 1 → rd (semXIR I (mulF fT fAl fH) s3).M i = rd s3.M i :=
    fun i h0 h1 h2 => by rw [mulF, sem_blk]; exact mulFC_frame _ _ _ (.inr h0) h1 h2 _
  have hM4 := inv_sem I (wf_mulF fT fAl fH (by decide)) hM3
  have hu3 : rdF s3.M fU = rdF s.M a :=
    (rdF_eq (f3 _ (by decide) (by decide)) (f3 _ (by decide) (by decide))).trans hu2
  have hal3 : rdF s3.M fAl = rdF s.M fAl :=
    (rdF_eq (f3 _ (by decide) (by decide)) (f3 _ (by decide) (by decide))).trans hal2
  generalize semXIR I (mulF fT fAl fH) s3 = s4 at h4 f4 hM4
  have h5 := addF_sem (I := I) (s := s4) hM4 (d := fN) (a := fU) (b := fT) (by decide) (by decide)
    (by decide)
  have hu4 : rdF s4.M fU = rdF s.M a :=
    (rdF_eq (f4 _ (by decide) (by decide) (by decide)) (f4 _ (by decide) (by decide) (by decide))).trans hu3
  have hh4 : rdF s4.M fH = rdF s.M b + rdF s.M a := by
    rw [rdF_eq (f4 _ (by decide) (by decide) (by decide)) (f4 _ (by decide) (by decide) (by decide)),
      h3, hw2, hu2]
  refine ⟨?_, ?_⟩
  · rw [h5, h4, hu4, hal3, h3, hw2, hu2]
  · rw [addF, ← hh4]
    exact rdF_eq (addFC_frame fN fU fT (i := fH) (by decide) (by decide) _)
      (addFC_frame fN fU fT (i := fH + 1) (by decide) (by decide) _)

/-- **The pair's addresses.** -/
theorem pairPs_sem (I : Array Word) (s : St) (hM : Inv s.M) {A l q : ℕ} (hq : q < 2 ^ 64)
    (hP : 2 ^ l < 2 ^ 64) (hQ : rd s.M rQ = toWord q) (hP2 : rd s.M rP2 = toWord (2 ^ l))
    (hA0 : rd s.M rA0 = toWord A) :
    rd (semXIR I (.blk pairPs) s).M rBs = toWord (baseP l q) ∧
    rd (semXIR I (.blk pairPs) s).M rAL = toWord (A + 2 * loP l q) ∧
    rd (semXIR I (.blk pairPs) s).M rAH = toWord (A + 2 * hiP l q) := by
  have hs := hM.1
  simp only [regs] at hs
  have e : q / 2 ^ l * (2 ^ l + 2 ^ l) = baseP l q := by rw [baseP, pow_succ']
  simp only [semXIR, runPrims, pairPs, List.foldl, Prim.run]
  refine ⟨?_, ?_, ?_⟩ <;>
  simp (disch := first | decide | (simp only [size_set, uT1, uX, uT2, rBs, rAL, rAH]; omega)) only
    [rd_set_self, rd_set_ne] <;>
  simp only [hQ, hP2, hA0, divu_toWord hq hP, remu_toWord hq hP, add_toWord, mul_toWord, e]
  · congr 1; simp only [loP]; ring
  · congr 1; simp only [hiP, loP]; ring

theorem pairBody_nw {r : ℕ} (hr : r = rA0 ∨ r = rP2 ∨ r = rTr ∨ r = rLv ∨ r = rC1 ∨ r = rN1 ∨
    r = rC3 ∨ r = rN3) : ¬ Writes pairBody r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide only [pairBody, pairPs, arithIR, alphaIR, alphaBody, ldF, stF, addF, addFC, Writes,
    Prim.dst, rQ, uX, uT1, uT2, rBs, rAL, rAL1, rAH, rAH1, rTa, rTa1, rBit, uI, rC2, rN2, fAl, fU,
    fW, fH, fT, fN, fG, cTmp, rA0, rP2, rTr, rLv, rC1, rN1, rC3, rN3, mulF_writes_iff, or_false]

/-- **One butterfly**: the pair's low and high elements become `u + α (w + u)` and `w + u`,
`α = Σ_{i<20} [bit_i(base)] T(i)`; nothing else on the heap changes; `q += 1`. -/
theorem pairBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {A ta l q : ℕ} {T : ℕ → F}
    (hl : l < 20) (hA : regs ≤ A) (hq : q < 2 ^ 64) (hhi : A + 2 * hiP l q + 2 < 2 ^ 64)
    (hsz : A + 2 * hiP l q + 1 < s.M.size) (hta : regs ≤ ta) (hta2 : ta + 40 < 2 ^ 64)
    (hQ : rd s.M rQ = toWord q) (hP2 : rd s.M rP2 = toWord (2 ^ l)) (hA0 : rd s.M rA0 = toWord A)
    (hTr : rd s.M rTr = toWord ta) (hT : ∀ i < 20, rdF s.M (ta + 2 * i) = T i) :
    rdF (semXIR I pairBody s).M (A + 2 * loP l q) = rdF s.M (A + 2 * loP l q) +
      (∑ i ∈ range 20, if (baseP l q).testBit i then T i else 0) *
        (rdF s.M (A + 2 * hiP l q) + rdF s.M (A + 2 * loP l q)) ∧
    rdF (semXIR I pairBody s).M (A + 2 * hiP l q) =
      rdF s.M (A + 2 * hiP l q) + rdF s.M (A + 2 * loP l q) ∧
    (∀ x, regs ≤ x → x ≠ A + 2 * loP l q → x ≠ A + 2 * loP l q + 1 → x ≠ A + 2 * hiP l q →
      x ≠ A + 2 * hiP l q + 1 → rd (semXIR I pairBody s).M x = rd s.M x) ∧
    rd (semXIR I pairBody s).M rQ = toWord (q + 1) := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hlh := loP_lt_hiP l q
  have hP : 2 ^ l < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hbase : baseP l q < 2 ^ 64 := by have : baseP l q ≤ loP l q := by simp [loP]
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
  rw [pairBody, semXIR_seq]
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
      simp +decide only [alphaIR, alphaBody, ldF, Writes, Prim.dst, rBit, uT1, rTa, rTa1, fG, fAl,
        uI, rN2, rC2, cTmp, rAL, rAH, rQ, or_false])
  rw [semXIR_seq]
  generalize semXIR I alphaIR s1 = s2 at a2 hM2 hH2 nwA z2
  have l2 : rd s2.M rAL = toWord (A + 2 * loP l q) := (nwA _ (.inl rfl)).trans p2
  have h2 : rd s2.M rAH = toWord (A + 2 * hiP l q) := (nwA _ (.inr (.inl rfl))).trans p3
  have q2 : rd s2.M rQ = toWord q := (nwA _ (.inr (.inr rfl))).trans q1
  have hY : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => (hH2 x hx).trans (hH1 x hx)
  -- the arithmetic
  obtain ⟨b1, b2⟩ := arith_sem I s2 hM2 (a := A + 2 * loP l q) (b := A + 2 * hiP l q)
    (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega) (by omega) l2 h2
  have hM3 := inv_sem I wf_arithIR hM2
  have z3 := size_sem I arithIR s2
  have hH3 := hframe I arithIR s2 lo_arithIR
  have nwB : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I arithIR s2).M r = rd s2.M r :=
    fun r hr => frame I _ s2 wf_arithIR hM2 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide only [arithIR, ldF, addF, addFC, Writes, Prim.dst, fU, fW, fH, fT, fN, rAL1,
        rAH1, rAL, rAH, rQ, mulF_writes_iff, or_false])
  have eU : rdF s2.M (A + 2 * loP l q) = rdF s.M (A + 2 * loP l q) :=
    rdF_eq (hY _ (by simp only [regs]; omega)) (hY _ (by simp only [regs]; omega))
  have eW : rdF s2.M (A + 2 * hiP l q) = rdF s.M (A + 2 * hiP l q) :=
    rdF_eq (hY _ (by simp only [regs]; omega)) (hY _ (by simp only [regs]; omega))
  rw [eU, eW, a2] at b1
  rw [eU, eW] at b2
  rw [semXIR_seq]
  generalize semXIR I arithIR s2 = s3 at b1 b2 hM3 hH3 nwB z3
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
theorem levelIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {A ta ℓ l : ℕ} {Y : ℕ → F}
    (hℓ : ℓ ≤ 20) (hl : l < ℓ) (hA : regs ≤ A) (hA2 : A + 2 * 2 ^ ℓ + 1 < 2 ^ 64)
    (hsz : A + 2 * 2 ^ ℓ ≤ s.M.size) (hta : regs ≤ ta) (hta2 : ta + 40 < 2 ^ 64)
    (hdisj : ta + 40 ≤ A ∨ A + 2 * 2 ^ ℓ ≤ ta)
    (hLv : rd s.M rLv = toWord l) (hA0 : rd s.M rA0 = toWord A) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < 20, rdF s.M (ta + 2 * i) = (wRow D logNMax l).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdF s.M (A + 2 * i) = Y i) :
    (∀ i < 2 ^ ℓ, rdF (semXIR I (levelIR ℓ) s).M (A + 2 * i) =
      bflyLevel (M := F) D logNMax 0 l Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 * 2 ^ ℓ ≤ x) → rd (semXIR I (levelIR ℓ) s).M x = rd s.M x) ∧
    (semXIR I (levelIR ℓ) s).M.size = s.M.size := by
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
    · rw [hLv, show rd s.M cOne = toWord 1 from hM.2 0 (by decide),
        shl_toWord (by omega) (by rw [Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)),
        Nat.one_mul]
    · exact hA0
    · exact hTr
  rw [levelIR, semXIR_seq]
  generalize semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s = s0 at hM0 z0 hH0 r0
  obtain ⟨q0, p0, n0, a0, t0⟩ := r0
  rw [loopK_eq I pairBody s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hP1]
  have hE : ∀ i, i ≠ rC1 → i ≠ cTmp → rd (entryK rC1 rN1 (toWord (2 ^ (ℓ - 1))) s0.M) i =
      rd s0.M i := fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC1) (n := rN1) (K := toWord (2 ^ (ℓ - 1))) hM0 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rQ = toWord j ∧ rd s'.M rP2 = toWord (2 ^ l) ∧ rd s'.M rA0 = toWord A ∧
    rd s'.M rTr = toWord ta ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 * 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdF s'.M (A + 2 * i) =
      if pairOf l i < j then bflyLevel (M := F) D logNMax 0 l Y i else Y i
  have nwP : ∀ r, (r = rA0 ∨ r = rP2 ∨ r = rTr) → ∀ s', Inv s'.M →
      rd (decS rC1 (semXIR I pairBody s')).M r = rd s'.M r := fun r hr s' hs' => by
    rw [rd_decS (by rcases hr with rfl | rfl | rfl <;> decide)]
    exact frame I _ s' wf_pairBody hs' _ (by rcases hr with rfl | rfl | rfl <;> decide)
      (pairBody_nw (by rcases hr with rfl | rfl | rfl <;> simp))
  have step : ∀ j s', j < 2 ^ (ℓ - 1) → P j s' → P (j + 1) (decS rC1 (semXIR I pairBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    have hhi := hiP_lt hl hj
    have hlh := loP_lt_hiP l j
    have hT' : ∀ i < 20, rdF s'.M (ta + 2 * i) = (wRow D logNMax l).getD i 0 := fun i hi => by
      rw [← hT i hi]
      exact rdF_eq (i7 _ (by simp only [regs]; omega) (by omega))
        (i7 _ (by simp only [regs]; omega) (by omega))
    have hp2 : 2 * hiP l j + 2 ≤ 2 * 2 ^ ℓ := by omega
    obtain ⟨e1, e2, e3, e4⟩ := pairBody_sem I s' i1 (A := A) (T := fun i => (wRow D logNMax l).getD i 0)
      (by omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
      (by simp only [regs]; omega) hta2 i3 i4 i5 i6 hT'
    have hd : ∀ x, x ≠ rC1 → rd (decS rC1 (semXIR I pairBody s')).M x =
        rd (semXIR I pairBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hlo' := i8 _ (by omega : loP l j < 2 ^ ℓ)
    have hhi' := i8 _ hhi
    rw [pairOf_loP, if_neg (lt_irrefl j)] at hlo'
    rw [pairOf_hiP, if_neg (lt_irrefl j)] at hhi'
    refine ⟨inv_decS (inv_sem I wf_pairBody i1) (by decide), by rw [size_decS, size_sem, i2], ?_,
      (nwP _ (.inr (.inl rfl)) s' i1).trans i4, (nwP _ (.inl rfl) s' i1).trans i5,
      (nwP _ (.inr (.inr rfl)) s' i1).trans i6, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide), e4]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC1]; omega), e3 x (by simp only [regs]; omega) (by omega) (by omega)
        (by omega) (by omega), i7 x (by simp only [regs]; omega) hx2]
    · have hdF : ∀ y, regs ≤ y → rdF (decS rC1 (semXIR I pairBody s')).M y =
          rdF (semXIR I pairBody s').M y := fun y hy =>
        rdF_eq (hd _ (by simp only [rC1, regs] at *; omega)) (hd _ (by simp only [rC1, regs] at *; omega))
      rw [hdF _ (by simp only [regs]; omega)]
      by_cases hq : pairOf l i = j
      · rw [if_pos (by omega)]
        rcases pair_cases hq with rfl | rfl
        · rw [e1, hlo', hhi', bflyLevel_lo]; rfl
        · rw [e2, hlo', hhi', bflyLevel_hi]
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
  have := iterL_ind (f := semXIR I pairBody) (c := rC1) (m := 2 ^ (ℓ - 1)) P step (2 ^ (ℓ - 1)) 0 _
    (by omega) hP0
  rw [Nat.zero_add] at this
  obtain ⟨-, z, -, -, -, -, f7, f8⟩ := this
  refine ⟨fun i hi => ?_, f7, z⟩
  rw [f8 i hi, if_pos (pairOf_lt hl hi)]

theorem levelIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rLv ∨ r = rTr ∨ r = rC3 ∨ r = rN3) (ℓ : ℕ) :
    ¬ Writes (levelIR ℓ) r := by
  intro h
  simp only [levelIR, Writes] at h
  rcases h with ⟨p, hp, he⟩ | h | h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [Prim.dst, rQ, rP2, rN1, rA0, rLv, rTr, rC3, rN3] at he
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [rC1, rA0, rLv, rTr, rC3, rN3] at h
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [cTmp, rA0, rLv, rTr, rC3, rN3] at h
  · exact pairBody_nw (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) h

/-- **The butterflies** (`bflyRun`) on the machine: from the row `Y` of `2^ℓ` elements at `A`
(`rA0 = A`) and the basis table at `tb`, `bflyIR ℓ tb` leaves `bflyRun D 20 0 ℓ Y` in the row
and keeps the heap outside it. -/
theorem bflyIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ} {Y : ℕ → F}
    (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 20) (hA : regs ≤ A) (hA2 : A + 2 * 2 ^ ℓ + 1 < 2 ^ 64)
    (hsz : A + 2 * 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 800 < 2 ^ 64)
    (hdisj : tb + 800 ≤ A ∨ A + 2 * 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdF s.M (A + 2 * i) = Y i) :
    (∀ i < 2 ^ ℓ, rdF (semXIR I (bflyIR ℓ tb) s).M (A + 2 * i) =
      bflyRun (M := F) D logNMax 0 ℓ Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 * 2 ^ ℓ ≤ x) → rd (semXIR I (bflyIR ℓ tb) s).M x = rd s.M x) ∧
    Inv (semXIR I (bflyIR ℓ tb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hA htb
  have hℓ64 : ℓ < 2 ^ 64 := by omega
  have w0 : WF (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) := by
    simp +decide only [WF, Prim.dst, rLv, rTr, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) s
  have hH0 := hframe I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) s
    (by simp +decide only [Lo, Prim.dst, regs, rLv, rTr, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have r0 : rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rLv = toWord 0 ∧
      rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rTr = toWord (tb + 40 * 0) ∧
      rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rN3 = toWord ℓ ∧
      rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rA0 = toWord A := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rLv, rTr, rN3]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rfl
    · exact hA0
  rw [bflyIR, semXIR_seq]
  generalize semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) s = s0
    at hM0 z0 hH0 r0
  obtain ⟨l0, t0, n0, a0⟩ := r0
  rw [loopK_eq I (lvlStep ℓ) s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hℓ64]
  have hE : ∀ i, i ≠ rC3 → i ≠ cTmp → rd (entryK rC3 rN3 (toWord ℓ) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC3) (n := rN3) (K := toWord ℓ) hM0 (by decide)
  have wl : WF (levelIR ℓ) := (wf_bflyIR ℓ tb).2.2.2.2.1
  have wlb : WF (.blk [.op .add rLv rLv cOne, .const uT1 40, .op .add rTr rTr uT1]) := by
    simp +decide only [WF, Prim.dst, rLv, uT1, rTr]
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rLv = toWord j ∧ rd s'.M rTr = toWord (tb + 40 * j) ∧ rd s'.M rA0 = toWord A ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 * 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdF s'.M (A + 2 * i) = bflyRun (M := F) D logNMax 0 j Y i
  have step : ∀ j s', j < ℓ → P j s' → P (j + 1) (decS rC3 (semXIR I (lvlStep ℓ) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hT : ∀ i < 20, rdF s'.M (tb + 40 * j + 2 * i) = (wRow D logNMax j).getD i 0 :=
      fun i hi => by
        rw [← hW j (by omega) i hi]
        exact rdF_eq (i6 _ (by simp only [regs]; omega) (by omega))
          (i6 _ (by simp only [regs]; omega) (by omega))
    obtain ⟨e1, e2, e3⟩ := levelIR_sem I s' i1 (Y := bflyRun (M := F) D logNMax 0 j Y) hℓ hj
      (by simp only [regs]; omega) hA2 (by omega) (by simp only [regs]; omega) (by omega) (by omega)
      i3 i5 i4 hT i7
    have hM1 := inv_sem I wl i1
    have nw : ∀ r, (r = rA0 ∨ r = rLv ∨ r = rTr) → rd (semXIR I (levelIR ℓ) s').M r = rd s'.M r :=
      fun r hr => frame I _ s' wl i1 _ (by rcases hr with rfl | rfl | rfl <;> decide)
        (levelIR_nw (by rcases hr with rfl | rfl | rfl <;> simp) ℓ)
    rw [lvlStep]
    simp only [semXIR_seq]
    generalize hs1 : semXIR I (levelIR ℓ) s' = s1 at e1 e2 e3 hM1 nw
    have hs1' := hM1.1
    simp only [regs] at hs1'
    have hd : ∀ x, x ≠ rC3 → rd (decS rC3 (semXIR I (.blk [.op .add rLv rLv cOne, .const uT1 40,
        .op .add rTr rTr uT1]) s1)).M x = rd (semXIR I (.blk [.op .add rLv rLv cOne,
        .const uT1 40, .op .add rTr rTr uT1]) s1).M x := fun x hx => rd_decS (Ne.symm hx) _
    have hb : ∀ x, x ≠ rLv → x ≠ uT1 → x ≠ rTr → rd (semXIR I (.blk [.op .add rLv rLv cOne,
        .const uT1 40, .op .add rTr rTr uT1]) s1).M x = rd s1.M x := fun x h1 h2 h3 =>
      rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩) _
    refine ⟨inv_decS (inv_sem I wlb hM1) (by decide), by rw [size_decS, size_sem, e3, i2], ?_, ?_,
      ?_, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
        [rd_set_self, rd_set_ne]
      rw [nw _ (.inr (.inl rfl)), i3, show rd s1.M cOne = 1 from hM1.2 0 (by decide),
        add_one_toWord]
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
        [rd_set_self, rd_set_ne]
      rw [nw _ (.inr (.inr rfl)), i4, show (40 : Word) = toWord 40 from rfl, add_toWord]
      congr 1
    · rw [hd _ (by decide), hb _ (by decide) (by decide) (by decide), nw _ (.inl rfl), i5]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC3]; omega), hb _ (by simp only [rLv]; omega) (by simp only [uT1]; omega)
        (by simp only [rTr]; omega), e2 x (by simp only [regs]; omega) hx2,
        i6 x (by simp only [regs]; omega) hx2]
    · rw [rdF_eq ((hd _ (by simp only [rC3]; omega)).trans (hb _ (by simp only [rLv]; omega)
        (by simp only [uT1]; omega) (by simp only [rTr]; omega)))
        ((hd _ (by simp only [rC3]; omega)).trans (hb _ (by simp only [rLv]; omega)
        (by simp only [uT1]; omega) (by simp only [rTr]; omega))), e1 i hi]
      rfl
  have hP0 : P 0 ⟨entryK rC3 rN3 (toWord ℓ) s0.M, s0.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), l0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only
      rw [hE _ (by simp only [rC3, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
    · dsimp only
      rw [show bflyRun (M := F) D logNMax 0 0 Y i = Y i from rfl, ← hY i hi]
      exact rdF_eq ((hE _ (by simp only [rC3]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
        ((hE _ (by simp only [rC3]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
  have := iterL_ind (f := semXIR I (lvlStep ℓ)) (c := rC3) (m := ℓ) P step ℓ 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  exact ⟨this.2.2.2.2.2.2, this.2.2.2.2.2.1, this.1⟩

/-! ## The basis table -/

theorem rdF_add_one (a b : Word) : (⟨wB (a ^^^ 1), wB (b ||| b)⟩ : F) = ⟨wB a, wB b⟩ + 1 := by
  rw [BitVec.or_self]
  show (⟨wB (a ^^^ 1), wB b⟩ : F) = ⟨wB a + 1, wB b + 0⟩
  rw [add_zero, wB_xor]; rfl

theorem wRow_zero_getD {i : ℕ} (hi : i < 20) : (wRow D logNMax 0).getD i 0 = D (2 ^ i) := by
  simp [wRow, hi, List.getD_eq_getElem?_getD, show D 0 = 0 by decide, show D 1 = 1 by decide]

theorem wRow_succ_getD (v : ℕ) {i : ℕ} (hi : i < 20) : (wRow D logNMax (v + 1)).getD i 0 =
    (wRow D logNMax v).getD i 0 * ((wRow D logNMax v).getD i 0 + 1) *
      ((wRow D logNMax v).getD (v + 1) 0 * ((wRow D logNMax v).getD (v + 1) 0 + 1))⁻¹ := by
  rw [wRow]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, wRow_length]; exact hi), List.getElem_map,
    ← List.getD_eq_getElem _ 0]
  rfl

/-- One entry of row `0`: `D(2^i)` at `tb + 2i`. -/
theorem row0Body_sem (I : Array Word) (s : St) (hM : Inv s.M) {tb i : ℕ} (hi : i < 20)
    (htb : regs ≤ tb) (htb2 : tb + 40 < 2 ^ 64) (hsz : tb + 40 ≤ s.M.size)
    (hI : rd s.M uI = toWord i) (hTa : rd s.M rTa = toWord (tb + 2 * i)) :
    rdF (semXIR I row0Body s).M (tb + 2 * i) = D (2 ^ i) ∧
    (∀ x, regs ≤ x → x ≠ tb + 2 * i → x ≠ tb + 2 * i + 1 → rd (semXIR I row0Body s).M x = rd s.M x) ∧
    rd (semXIR I row0Body s).M uI = toWord (i + 1) ∧
    rd (semXIR I row0Body s).M rTa = toWord (tb + 2 * (i + 1)) ∧
    rd (semXIR I row0Body s).M rTr = rd s.M rTr := by
  have hs := hM.1
  simp only [regs] at hs htb
  have w1 : WF (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) := by simp +decide only [WF,
    Prim.dst, fG]
  have hM1 := inv_sem I w1 hM
  have hH1 := hframe I (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) s
    (by simp +decide only [Lo, Prim.dst, regs, fG])
  have r1 : rd (semXIR I (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) s).M fG = toWord (2 ^ i) ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) s).M (fG + 1) = 0 ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) s).M rTa = toWord (tb + 2 * i) ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) s).M uI = toWord i ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) s).M rTr = rd s.M rTr := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, fG]; omega)) only [rd_set_self, rd_set_ne]
    · rw [hI, show rd s.M cOne = toWord 1 from hM.2 0 (by decide), shl_toWord (by omega)
        (by rw [Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)), Nat.one_mul]
    · exact hTa
    · exact hI
  rw [row0Body, semXIR_seq]
  have z1 := size_sem I (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) s
  generalize semXIR I (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) s = s1 at hM1 hH1 r1 z1
  obtain ⟨g1, g1', a1, i1, t1⟩ := r1
  obtain ⟨c1, c2, hM2⟩ := stF_sem I s1 hM1 (p := rTa) (p1 := rTa1) (v := fG) (x := tb + 2 * i)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) a1 (by simp only [regs]; omega) (by omega) (by omega)
  rw [semXIR_seq]
  generalize semXIR I (stF rTa rTa1 fG) s1 = s2 at c1 c2 hM2
  have hT4 : cTmp = 4 := rfl
  have hr2 : ∀ r, r < 256 → r ≠ rTa1 → r ≠ cTmp → rd s2.M r = rd s1.M r := fun r hr h1 h2 =>
    c2 r (by omega) (by omega) h1 h2
  have hb : ∀ x, x ≠ uT1 → x ≠ rTa → x ≠ uI → rd (semXIR I (.blk [.const uT1 2, .op .add rTa rTa uT1,
      .op .add uI uI cOne]) s2).M x = rd s2.M x := fun x h1 h2 h3 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩) _
  have hs2 := hM2.1
  simp only [regs] at hs2
  refine ⟨?_, fun x hx x1 x2 => ?_, ?_, ?_, ?_⟩
  · rw [rdF_eq (hb _ (by simp only [uT1]; omega) (by simp only [rTa]; omega) (by simp only [uI]; omega))
      (hb _ (by simp only [uT1]; omega) (by simp only [rTa]; omega) (by simp only [uI]; omega)), c1]
    simp only [rdF, rdB, g1, g1']
    rfl
  · simp only [regs] at hx
    rw [hb _ (by simp only [uT1]; omega) (by simp only [rTa]; omega) (by simp only [uI]; omega),
      c2 _ x1 x2 (by simp only [rTa1]; omega) (by omega), hH1 x (by simp only [regs]; omega)]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hr2 _ (by decide) (by decide) (by decide), i1,
      hr2 _ (by decide) (by decide) (by decide), show rd s1.M cOne = 1 from hM1.2 0 (by decide),
      add_one_toWord]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hr2 _ (by decide) (by decide) (by decide), a1, show (2 : Word) = toWord 2 from rfl,
      add_toWord]
    congr 1
  · rw [hb _ (by decide) (by decide) (by decide), hr2 _ (by decide) (by decide) (by decide), t1]

theorem wf_row0Body : WF row0Body := by
  simp +decide only [row0Body, stF, WF, Prim.dst, fG, rTa1, uT1, rTa, uI, cTmp, and_true]

/-- **Row `0`** at `rTr = tb`: `D(2^i)` at `tb + 2i`, `i < 20`. -/
theorem row0IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + 40 < 2 ^ 64) (hsz : tb + 40 ≤ s.M.size) (hTr : rd s.M rTr = toWord tb) :
    (∀ i < 20, rdF (semXIR I row0IR s).M (tb + 2 * i) = D (2 ^ i)) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + 40 ≤ x) → rd (semXIR I row0IR s).M x = rd s.M x) ∧
    rd (semXIR I row0IR s).M rTr = toWord tb ∧ Inv (semXIR I row0IR s).M ∧
    (semXIR I row0IR s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs htb
  have w0 : WF (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 20]) := by
    simp +decide only [WF, Prim.dst, uI, rTa, rN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 20]) s
  have hH0 := hframe I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 20]) s
    (by simp +decide only [Lo, Prim.dst, regs, uI, rTa, rN2])
  have r0 : rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 20]) s).M uI =
        toWord 0 ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 20]) s).M rTa =
        toWord (tb + 2 * 0) ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 20]) s).M rN2 = 20 ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 20]) s).M rTr =
        toWord tb := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, uI, rTa, rN2]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [hTr, or_self_eval]; rfl
    · exact hTr
  rw [row0IR, semXIR_seq]
  generalize semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 20]) s = s0
    at hM0 z0 hH0 r0
  obtain ⟨i0, a0, n0, t0⟩ := r0
  rw [loopK_eq I row0Body s0 hM0 (by decide) (by decide) (by decide) n0]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 20 s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := 20) hM0 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M uI = toWord j ∧ rd s'.M rTa = toWord (tb + 2 * j) ∧ rd s'.M rTr = toWord tb ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + 2 * j ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < j, rdF s'.M (tb + 2 * i) = D (2 ^ i)
  have step : ∀ j s', j < 20 → P j s' → P (j + 1) (decS rC2 (semXIR I row0Body s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := row0Body_sem I s' i1 hj (by simp only [regs]; omega) htb2
      (by omega) i3 i4
    have hd : ∀ x, x ≠ rC2 → rd (decS rC2 (semXIR I row0Body s')).M x =
        rd (semXIR I row0Body s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS (inv_sem I wf_row0Body i1) (by decide), by rw [size_decS, size_sem, i2],
      by rw [hd _ (by decide), e3], by rw [hd _ (by decide), e4], by rw [hd _ (by decide), e5, i5],
      fun x hx hx2 => ?_, fun i hi => ?_⟩
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC2]; omega), e2 x (by simp only [regs]; omega) (by omega) (by omega),
        i6 x (by simp only [regs]; omega) (by omega)]
    · rw [rdF_eq (hd _ (by simp only [rC2]; omega)) (hd _ (by simp only [rC2]; omega))]
      by_cases h : i = j
      · subst h; exact e1
      · rw [rdF_eq (e2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (e2 _ (by simp only [regs]; omega) (by omega) (by omega)), i7 i (by omega)]
  have hP0 : P 0 ⟨entryK rC2 rN2 20 s0.M, s0.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => absurd hi
      (Nat.not_lt_zero _)⟩
    · dsimp only; rw [hE _ (by decide) (by decide), i0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only
      rw [hE _ (by simp only [rC2, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
  have := iterL_ind (f := semXIR I row0Body) (c := rC2) (m := 20) P step 20 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  obtain ⟨f1, f2, -, -, f5, f6, f7⟩ := this
  exact ⟨f7, fun x hx hx2 => f6 x hx (by omega), f5, f1, f2⟩

/-- `a + 1` on the machine: `fW := fU + 1`. -/
theorem plusOne_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rdF (semXIR I (.blk [.op .xor fW fU cOne, .op .or (fW + 1) (fU + 1) (fU + 1)]) s).M fW =
      rdF s.M fU + 1 ∧
    ∀ x, x ≠ fW → x ≠ fW + 1 → rd (semXIR I (.blk [.op .xor fW fU cOne,
      .op .or (fW + 1) (fU + 1) (fU + 1)]) s).M x = rd s.M x := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun x h1 h2 => rd_runPrims_of_not_writes (by
    simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _⟩
  simp only [semXIR, runPrims, List.foldl, Prim.run, rdF, rdB]
  simp (disch := first | decide | (simp only [size_set, fW]; omega)) only [rd_set_self, rd_set_ne]
  rw [show rd s.M cOne = 1 from hM.2 0 (by decide)]
  exact rdF_add_one _ _

theorem wf_plusOne : WF (.blk [.op .xor fW fU cOne, .op .or (fW + 1) (fU + 1) (fU + 1)]) := by
  simp +decide only [WF, Prim.dst, fW]

theorem wf_rowBody : WF rowBody := by
  have m1 := wf_mulF fH fU fW (by decide)
  have m2 := wf_mulF fN fH fAl (by decide)
  simp only [rowBody, ldF, stF, WF, List.mem_cons, List.mem_nil_iff, m1, m2]
  simp [Prim.dst, fU, fW, rTa1, uT1, rAH, rAH1, rTa, cTmp]

/-- **One entry of row `j + 1`**: `a (a + 1) c` at `ta + 40 + 2k`, `a` the entry at `ta + 2k`,
`c` in `fAl`. -/
theorem rowBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {ta k : ℕ} (hk : k < 20)
    (hta : regs ≤ ta) (hta2 : ta + 80 < 2 ^ 64) (hsz : ta + 80 ≤ s.M.size)
    (hTa : rd s.M rTa = toWord (ta + 2 * k)) :
    rdF (semXIR I rowBody s).M (ta + 40 + 2 * k) =
      rdF s.M (ta + 2 * k) * (rdF s.M (ta + 2 * k) + 1) * rdF s.M fAl ∧
    (∀ x, regs ≤ x → x ≠ ta + 40 + 2 * k → x ≠ ta + 40 + 2 * k + 1 →
      rd (semXIR I rowBody s).M x = rd s.M x) ∧
    rd (semXIR I rowBody s).M rTa = toWord (ta + 2 * (k + 1)) ∧
    rdF (semXIR I rowBody s).M fAl = rdF s.M fAl ∧
    rd (semXIR I rowBody s).M rTr = rd s.M rTr ∧ rd (semXIR I rowBody s).M rLv = rd s.M rLv := by
  have hs := hM.1
  simp only [regs] at hs hta
  have hT4 : cTmp = 4 := rfl
  -- load `a`
  obtain ⟨u1, -, u3⟩ := ldF_sem I s hM (d := fU) (p := rTa) (p1 := rTa1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hTa (by simp only [regs]; omega) (by omega)
  have hM1 := inv_sem I (P := ldF fU rTa rTa1) (by simp +decide only [ldF, WF, Prim.dst, fU, rTa1,
    and_true]) hM
  have y1 := size_sem I (ldF fU rTa rTa1) s
  rw [rowBody, semXIR_seq]
  generalize semXIR I (ldF fU rTa rTa1) s = s1 at u1 u3 hM1 y1
  -- `a + 1`
  obtain ⟨v1, v2⟩ := plusOne_sem I s1 hM1
  have hM2 := inv_sem I wf_plusOne hM1
  have y2 := size_sem I (.blk [.op .xor fW fU cOne, .op .or (fW + 1) (fU + 1) (fU + 1)]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .xor fW fU cOne, .op .or (fW + 1) (fU + 1) (fU + 1)]) s1 = s2
    at v1 v2 hM2 y2
  -- the products
  have m3 := mulF_sem (I := I) (s := s2) hM2 (d := fH) (a := fU) (b := fW) (by decide) (by decide)
    (by decide) (by decide)
  have f3 : ∀ i, 15 ≤ i → i ≠ fH → i ≠ fH + 1 → rd (semXIR I (mulF fH fU fW) s2).M i = rd s2.M i :=
    fun i h0 h1 h2 => by rw [mulF, sem_blk]; exact mulFC_frame _ _ _ (.inr h0) h1 h2 _
  have hM3 := inv_sem I (wf_mulF fH fU fW (by decide)) hM2
  have y3 := size_sem I (mulF fH fU fW) s2
  rw [semXIR_seq]
  generalize semXIR I (mulF fH fU fW) s2 = s3 at m3 f3 hM3 y3
  have m4 := mulF_sem (I := I) (s := s3) hM3 (d := fN) (a := fH) (b := fAl) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ i, 15 ≤ i → i ≠ fN → i ≠ fN + 1 → rd (semXIR I (mulF fN fH fAl) s3).M i = rd s3.M i :=
    fun i h0 h1 h2 => by rw [mulF, sem_blk]; exact mulFC_frame _ _ _ (.inr h0) h1 h2 _
  have hM4 := inv_sem I (wf_mulF fN fH fAl (by decide)) hM3
  have y4 := size_sem I (mulF fN fH fAl) s3
  rw [semXIR_seq]
  generalize semXIR I (mulF fN fH fAl) s3 = s4 at m4 f4 hM4 y4
  -- facts on `s4`
  have k4 : ∀ x, 256 ≤ x → rd s4.M x = rd s.M x := fun x hx => by
    rw [f4 x (by omega) (by simp only [fN]; omega) (by simp only [fN]; omega),
      f3 x (by omega) (by simp only [fH]; omega) (by simp only [fH]; omega),
      v2 x (by simp only [fW]; omega) (by simp only [fW]; omega),
      u3 x (by simp only [fU]; omega) (by simp only [fU]; omega) (by simp only [rTa1]; omega)]
  have r4 : ∀ r, (r = rTa ∨ r = rTr ∨ r = rLv ∨ r = fAl ∨ r = fAl + 1) → rd s4.M r = rd s.M r :=
    fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [f4 _ (by decide) (by decide) (by decide), f3 _ (by decide) (by decide) (by decide),
        v2 _ (by decide) (by decide), u3 _ (by decide) (by decide) (by decide)]
  have n4 : rdF s4.M fN = rdF s.M (ta + 2 * k) * (rdF s.M (ta + 2 * k) + 1) * rdF s.M fAl := by
    have al2 : rdF s2.M fAl = rdF s.M fAl :=
      rdF_eq ((v2 _ (by decide) (by decide)).trans (u3 _ (by decide) (by decide) (by decide)))
        ((v2 _ (by decide) (by decide)).trans (u3 _ (by decide) (by decide) (by decide)))
    have al3 : rdF s3.M fAl = rdF s.M fAl :=
      (rdF_eq (f3 _ (by decide) (by decide) (by decide)) (f3 _ (by decide) (by decide) (by decide))).trans al2
    have fu2 : rdF s2.M fU = rdF s.M (ta + 2 * k) :=
      (rdF_eq (v2 _ (by decide) (by decide)) (v2 _ (by decide) (by decide))).trans u1
    rw [m4, m3, v1, al3, fu2, u1]
  -- the address
  have hs4 := hM4.1
  simp only [regs] at hs4
  have a5 : rd (semXIR I (.blk [.const uT1 40, .op .add rAH rTa uT1]) s4).M rAH =
      toWord (ta + 40 + 2 * k) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rAH]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [r4 _ (.inl rfl), hTa, show (40 : Word) = toWord 40 from rfl, add_toWord]
    congr 1; omega
  have b5 : ∀ x, x ≠ uT1 → x ≠ rAH → rd (semXIR I (.blk [.const uT1 40, .op .add rAH rTa uT1])
      s4).M x = rd s4.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM5 := inv_sem I (P := .blk [.const uT1 40, .op .add rAH rTa uT1])
    (by simp +decide only [WF, Prim.dst, uT1, rAH]) hM4
  have z5 := size_sem I (.blk [.const uT1 40, .op .add rAH rTa uT1]) s4
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const uT1 40, .op .add rAH rTa uT1]) s4 = s5 at a5 b5 hM5 z5
  -- the store
  obtain ⟨c1, c2, hM6⟩ := stF_sem I s5 hM5 (p := rAH) (p1 := rAH1) (v := fN)
    (x := ta + 40 + 2 * k) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) a5 (by simp only [regs]; omega) (by omega) (by omega)
  rw [semXIR_seq]
  generalize semXIR I (stF rAH rAH1 fN) s5 = s6 at c1 c2 hM6
  have hr6 : ∀ r, r < 256 → r ≠ rAH1 → r ≠ cTmp → rd s6.M r = rd s5.M r := fun r hr h1 h2 =>
    c2 r (by omega) (by omega) h1 h2
  have hb : ∀ x, x ≠ uT1 → x ≠ rTa → rd (semXIR I (.blk [.const uT1 2, .op .add rTa rTa uT1])
      s6).M x = rd s6.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hs6 := hM6.1
  simp only [regs] at hs6
  refine ⟨?_, fun x hx x1 x2 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [rdF_eq (hb _ (by simp only [uT1]; omega) (by simp only [rTa]; omega))
      (hb _ (by simp only [uT1]; omega) (by simp only [rTa]; omega)), c1,
      rdF_eq (b5 _ (by decide) (by decide)) (b5 _ (by decide) (by decide)), n4]
  · simp only [regs] at hx
    rw [hb _ (by simp only [uT1]; omega) (by simp only [rTa]; omega),
      c2 _ x1 x2 (by simp only [rAH1]; omega) (by omega), b5 _ (by simp only [uT1]; omega)
      (by simp only [rAH]; omega), k4 x hx]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rTa]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hr6 _ (by decide) (by decide) (by decide), b5 _ (by decide) (by decide), r4 _ (.inl rfl),
      hTa, show (2 : Word) = toWord 2 from rfl, add_toWord]
    congr 1
  · exact rdF_eq ((hb _ (by decide) (by decide)).trans ((hr6 _ (by decide) (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inr (.inr (.inl rfl))))))))
      ((hb _ (by decide) (by decide)).trans ((hr6 _ (by decide) (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inr (.inr (.inr rfl))))))))
  · exact (hb _ (by decide) (by decide)).trans ((hr6 _ (by decide) (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inl rfl)))))
  · exact (hb _ (by decide) (by decide)).trans ((hr6 _ (by decide) (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inr (.inl rfl))))))

set_option maxRecDepth 8000 in
/-- **Row `j + 1`** from row `j` (`R`, at `ta = rTr`; `rLv = j`, `j + 1 < 20`):
`R i (R i + 1) (b (b + 1))⁻¹` at `ta + 40 + 2i`, `b = R (j + 1)`. -/
theorem rowIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ta j : ℕ} {R : ℕ → F} (hj : j + 1 < 20)
    (hta : regs ≤ ta) (hta2 : ta + 80 < 2 ^ 64) (hsz : ta + 80 ≤ s.M.size)
    (hLv : rd s.M rLv = toWord j) (hTr : rd s.M rTr = toWord ta)
    (hR : ∀ i < 20, rdF s.M (ta + 2 * i) = R i) :
    (∀ i < 20, rdF (semXIR I rowIR s).M (ta + 40 + 2 * i) =
      R i * (R i + 1) * (R (j + 1) * (R (j + 1) + 1))⁻¹) ∧
    (∀ x, regs ≤ x → (x < ta + 40 ∨ ta + 80 ≤ x) → rd (semXIR I rowIR s).M x = rd s.M x) ∧
    rd (semXIR I rowIR s).M rLv = toWord (j + 1) ∧ rd (semXIR I rowIR s).M rTr = toWord (ta + 40) ∧
    Inv (semXIR I rowIR s).M ∧ (semXIR I rowIR s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hta
  have hT4 : cTmp = 4 := rfl
  -- `rTa := ta + 2 (j + 1)`
  have r1 : rd (semXIR I (.blk [.op .add uT1 rLv cOne, .op .add uT1 uT1 uT1, .op .add rTa rTr uT1])
      s).M rTa = toWord (ta + 2 * (j + 1)) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rTa]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hLv, hTr, show rd s.M cOne = 1 from hM.2 0 (by decide), add_one_toWord, add_toWord,
      add_toWord]
    congr 1; omega
  have b1 : ∀ x, x ≠ uT1 → x ≠ rTa → rd (semXIR I (.blk [.op .add uT1 rLv cOne,
      .op .add uT1 uT1 uT1, .op .add rTa rTr uT1]) s).M x = rd s.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM1 := inv_sem I (P := .blk [.op .add uT1 rLv cOne, .op .add uT1 uT1 uT1,
    .op .add rTa rTr uT1]) (by simp +decide only [WF, Prim.dst, uT1, rTa]) hM
  have y1 := size_sem I (.blk [.op .add uT1 rLv cOne, .op .add uT1 uT1 uT1,
    .op .add rTa rTr uT1]) s
  rw [rowIR, semXIR_seq]
  generalize semXIR I (.blk [.op .add uT1 rLv cOne, .op .add uT1 uT1 uT1,
    .op .add rTa rTr uT1]) s = s1 at r1 b1 hM1 y1
  -- `b`
  obtain ⟨u1, -, u3⟩ := ldF_sem I s1 hM1 (d := fU) (p := rTa) (p1 := rTa1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r1 (by simp only [regs]; omega) (by omega)
  have hM2 := inv_sem I (P := ldF fU rTa rTa1) (by simp +decide only [ldF, WF, Prim.dst, fU, rTa1,
    and_true]) hM1
  have y2 := size_sem I (ldF fU rTa rTa1) s1
  rw [semXIR_seq]
  generalize semXIR I (ldF fU rTa rTa1) s1 = s2 at u1 u3 hM2 y2
  have hb2 : rdF s2.M fU = R (j + 1) := by
    rw [u1, ← hR (j + 1) hj]
    exact rdF_eq (b1 _ (by simp only [uT1]; omega) (by simp only [rTa]; omega))
      (b1 _ (by simp only [uT1]; omega) (by simp only [rTa]; omega))
  obtain ⟨v1, v2⟩ := plusOne_sem I s2 hM2
  have hM3 := inv_sem I wf_plusOne hM2
  have y3 := size_sem I (.blk [.op .xor fW fU cOne, .op .or (fW + 1) (fU + 1) (fU + 1)]) s2
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .xor fW fU cOne, .op .or (fW + 1) (fU + 1) (fU + 1)]) s2 = s3
    at v1 v2 hM3 y3
  have m4 := mulF_sem (I := I) (s := s3) hM3 (d := fH) (a := fU) (b := fW) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ i, 15 ≤ i → i ≠ fH → i ≠ fH + 1 → rd (semXIR I (mulF fH fU fW) s3).M i = rd s3.M i :=
    fun i h0 h1 h2 => by rw [mulF, sem_blk]; exact mulFC_frame _ _ _ (.inr h0) h1 h2 _
  have hM4 := inv_sem I (wf_mulF fH fU fW (by decide)) hM3
  have y4 := size_sem I (mulF fH fU fW) s3
  rw [semXIR_seq]
  generalize semXIR I (mulF fH fU fW) s3 = s4 at m4 f4 hM4 y4
  have i5 := invF_sem (I := I) (s := s4) hM4 (d := fAl) (a := fH) (by decide) (by decide)
    (by decide)
  have f5 : ∀ i, 19 ≤ i → i ≠ fAl → i ≠ fAl + 1 → rd (semXIR I (invF fAl fH) s4).M i = rd s4.M i :=
    fun i h0 h1 h2 => by rw [invF, sem_blk]; exact invFC_frame _ _ (.inr h0) h1 h2 _
  have hM5 := inv_sem I (wf_invF fAl fH (by decide)) hM4
  have y5 := size_sem I (invF fAl fH) s4
  rw [semXIR_seq]
  generalize semXIR I (invF fAl fH) s4 = s5 at i5 f5 hM5 y5
  have c5 : rdF s5.M fAl = (R (j + 1) * (R (j + 1) + 1))⁻¹ := by
    rw [i5, m4, v1, rdF_eq (v2 _ (by decide) (by decide)) (v2 _ (by decide) (by decide)), hb2]
  have k5 : ∀ x, 256 ≤ x → rd s5.M x = rd s.M x := fun x hx => by
    rw [f5 x (by omega) (by simp only [fAl]; omega) (by simp only [fAl]; omega),
      f4 x (by omega) (by simp only [fH]; omega) (by simp only [fH]; omega),
      v2 x (by simp only [fW]; omega) (by simp only [fW]; omega),
      u3 x (by simp only [fU]; omega) (by simp only [fU]; omega) (by simp only [rTa1]; omega),
      b1 x (by simp only [uT1]; omega) (by simp only [rTa]; omega)]
  have r5 : ∀ r, (r = rTr ∨ r = rLv) → rd s5.M r = rd s.M r := fun r hr => by
    rcases hr with rfl | rfl <;>
    rw [f5 _ (by decide) (by decide) (by decide), f4 _ (by decide) (by decide) (by decide),
      v2 _ (by decide) (by decide), u3 _ (by decide) (by decide) (by decide),
      b1 _ (by decide) (by decide)]
  -- the entries
  have hs5 := hM5.1
  simp only [regs] at hs5
  have r6 : rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 20]) s5).M rTa = toWord (ta + 2 * 0) ∧
      rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 20]) s5).M rN2 = 20 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rTa, rN2]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [r5 _ (.inl rfl), hTr, or_self_eval]; rfl
  have b6 : ∀ x, x ≠ rTa → x ≠ rN2 → rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 20])
      s5).M x = rd s5.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM6 := inv_sem I (P := .blk [.op .or rTa rTr rTr, .const rN2 20])
    (by simp +decide only [WF, Prim.dst, rTa, rN2]) hM5
  have y6 := size_sem I (.blk [.op .or rTa rTr rTr, .const rN2 20]) s5
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 20]) s5 = s6 at r6 b6 hM6 y6
  obtain ⟨a6, n6⟩ := r6
  rw [semXIR_seq, loopK_eq I rowBody s6 hM6 (by decide) (by decide) (by decide) n6]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 20 s6.M) i = rd s6.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := 20) hM6 (by decide)
  let c := (R (j + 1) * (R (j + 1) + 1))⁻¹
  let P : ℕ → St → Prop := fun k s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rTa = toWord (ta + 2 * k) ∧ rdF s'.M fAl = c ∧ rd s'.M rTr = toWord ta ∧
    rd s'.M rLv = toWord j ∧
    (∀ x, regs ≤ x → (x < ta + 40 ∨ ta + 40 + 2 * k ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < k, rdF s'.M (ta + 40 + 2 * i) = R i * (R i + 1) * c
  have step : ∀ k s', k < 20 → P k s' → P (k + 1) (decS rC2 (semXIR I rowBody s')) := by
    rintro k s' hk ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rowBody_sem I s' i1 hk (by simp only [regs]; omega) hta2
      (by omega) i3
    have hd : ∀ x, x ≠ rC2 → rd (decS rC2 (semXIR I rowBody s')).M x =
        rd (semXIR I rowBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hRk : rdF s'.M (ta + 2 * k) = R k := by
      rw [← hR k hk]
      exact rdF_eq (i7 _ (by simp only [regs]; omega) (by omega))
        (i7 _ (by simp only [regs]; omega) (by omega))
    refine ⟨inv_decS (inv_sem I wf_rowBody i1) (by decide), by rw [size_decS, size_sem, i2],
      by rw [hd _ (by decide), e3], by rw [rdF_decS _ (by decide) (by decide), e4, i4],
      by rw [hd _ (by decide), e5, i5], by rw [hd _ (by decide), e6, i6],
      fun x hx hx2 => ?_, fun i hi => ?_⟩
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC2]; omega), e2 x (by simp only [regs]; omega) (by omega) (by omega),
        i7 x (by simp only [regs]; omega) (by omega)]
    · rw [rdF_eq (hd _ (by simp only [rC2]; omega)) (hd _ (by simp only [rC2]; omega))]
      by_cases h : i = k
      · subst h; rw [e1, hRk, i4]
      · rw [rdF_eq (e2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (e2 _ (by simp only [regs]; omega) (by omega) (by omega)), i8 i (by omega)]
  have hP0 : P 0 ⟨entryK rC2 rN2 20 s6.M, s6.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, y6, y5, y4, y3, y2, y1], ?_, ?_, ?_, ?_,
      fun x hx _ => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · dsimp only; rw [hE _ (by decide) (by decide), a6]
    · dsimp only
      rw [rdF_eq ((hE _ (by decide) (by decide)).trans (b6 _ (by decide) (by decide)))
        ((hE _ (by decide) (by decide)).trans (b6 _ (by decide) (by decide))), c5]
    · dsimp only
      rw [hE _ (by decide) (by decide), b6 _ (by decide) (by decide), r5 _ (.inl rfl), hTr]
    · dsimp only
      rw [hE _ (by decide) (by decide), b6 _ (by decide) (by decide), r5 _ (.inr rfl), hLv]
    · dsimp only
      simp only [regs] at hx
      rw [hE _ (by simp only [rC2]; omega) (by omega), b6 _ (by simp only [rTa]; omega)
        (by simp only [rN2]; omega), k5 x hx]
  have := iterL_ind (f := semXIR I rowBody) (c := rC2) (m := 20) P step 20 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  rw [show (20 : Word).toNat = 20 from rfl]
  generalize iterL (semXIR I rowBody) rC2 20 ⟨entryK rC2 rN2 20 s6.M, s6.o⟩ = s7 at this ⊢
  obtain ⟨g1, g2, -, -, g5, g6, g7, g8⟩ := this
  have hs7 := g1.1
  simp only [regs] at hs7
  have hb : ∀ x, x ≠ rLv → x ≠ uT1 → x ≠ rTr → rd (semXIR I (.blk [.op .add rLv rLv cOne,
      .const uT1 40, .op .add rTr rTr uT1]) s7).M x = rd s7.M x := fun x h1 h2 h3 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩) _
  have wfin : WF (.blk [.op .add rLv rLv cOne, .const uT1 40, .op .add rTr rTr uT1]) := by
    simp +decide only [WF, Prim.dst, rLv, uT1, rTr]
  refine ⟨fun i hi => ?_, fun x hx hx2 => ?_, ?_, ?_, inv_sem I wfin g1, ?_⟩
  rotate_left 4
  · rw [size_sem, g2]
  · rw [rdF_eq (hb _ (by simp only [rLv]; omega) (by simp only [uT1]; omega)
      (by simp only [rTr]; omega)) (hb _ (by simp only [rLv]; omega) (by simp only [uT1]; omega)
      (by simp only [rTr]; omega)), g8 i hi]
  · simp only [regs] at hx
    rw [hb _ (by simp only [rLv]; omega) (by simp only [uT1]; omega) (by simp only [rTr]; omega),
      g7 x (by simp only [regs]; omega) (by omega)]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [g6, show rd s7.M cOne = 1 from g1.2 0 (by decide), add_one_toWord]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [g5, show (40 : Word) = toWord 40 from rfl, add_toWord]

theorem wf_rowIR : WF rowIR := (wf_wtabIR 0).2.2.2.2.2.2

/-- **The basis table** (`wtabIR tb`): the rows `wRow D 20 v`, `v < 20`, at `tb + 40 v + 2 i`; the
heap outside `[tb, tb + 800)` is kept. -/
theorem wtabIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + 800 < 2 ^ 64) (hsz : tb + 800 ≤ s.M.size) :
    (∀ v < 20, ∀ i < 20, rdF (semXIR I (wtabIR tb) s).M (tb + 40 * v + 2 * i) =
      (wRow D logNMax v).getD i 0) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + 800 ≤ x) → rd (semXIR I (wtabIR tb) s).M x = rd s.M x) ∧
    Inv (semXIR I (wtabIR tb) s).M ∧ (semXIR I (wtabIR tb) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs htb
  have hT4 : cTmp = 4 := rfl
  have w0 : WF (.blk [.const rTr (toWord tb)]) := by simp +decide only [WF, Prim.dst, rTr,
    List.mem_cons, List.mem_nil_iff, forall_eq, or_false]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rTr (toWord tb)]) s
  have hH0 := hframe I (.blk [.const rTr (toWord tb)]) s (by simp +decide only [Lo, Prim.dst, regs,
    rTr, List.mem_cons, List.mem_nil_iff, forall_eq, or_false])
  have t0 : rd (semXIR I (.blk [.const rTr (toWord tb)]) s).M rTr = toWord tb := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rTr]; omega)
  rw [wtabIR, semXIR_seq]
  generalize semXIR I (.blk [.const rTr (toWord tb)]) s = s0 at hM0 z0 hH0 t0
  obtain ⟨o1, o2, o3, hM1, z1⟩ := row0IR_sem I s0 hM0 (by simp only [regs]; omega) (by omega)
    (by omega) t0
  rw [semXIR_seq]
  generalize semXIR I row0IR s0 = s1 at o1 o2 o3 hM1 z1
  have r2 : rd (semXIR I (.blk [.const rLv 0, .const rN3 19]) s1).M rLv = toWord 0 ∧
      rd (semXIR I (.blk [.const rLv 0, .const rN3 19]) s1).M rN3 = 19 := by
    have := hM1.1; simp only [regs] at this
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rLv, rN3]; omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have b2 : ∀ x, x ≠ rLv → x ≠ rN3 → rd (semXIR I (.blk [.const rLv 0, .const rN3 19]) s1).M x =
      rd s1.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM2 := inv_sem I (P := .blk [.const rLv 0, .const rN3 19]) (by simp +decide only [WF,
    Prim.dst, rLv, rN3])
    hM1
  have z2 := size_sem I (.blk [.const rLv 0, .const rN3 19]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const rLv 0, .const rN3 19]) s1 = s2 at r2 b2 hM2 z2
  obtain ⟨l2, n2⟩ := r2
  rw [loopK_eq I rowIR s2 hM2 (by decide) (by decide) (by decide) n2,
    show (19 : Word).toNat = 19 from rfl]
  have hE : ∀ i, i ≠ rC3 → i ≠ cTmp → rd (entryK rC3 rN3 19 s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC3) (n := rN3) (K := 19) hM2 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rLv = toWord j ∧ rd s'.M rTr = toWord (tb + 40 * j) ∧
    (∀ v ≤ j, ∀ i < 20, rdF s'.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + 40 * (j + 1) ≤ x) → rd s'.M x = rd s.M x)
  have step : ∀ j s', j < 19 → P j s' → P (j + 1) (decS rC3 (semXIR I rowIR s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rowIR_sem I s' i1 (ta := tb + 40 * j)
      (R := fun i => (wRow D logNMax j).getD i 0) (by omega) (by simp only [regs]; omega)
      (by omega) (by omega) i3 i4 (fun i hi => i5 j le_rfl i hi)
    have hd : ∀ x, x ≠ rC3 → rd (decS rC3 (semXIR I rowIR s')).M x =
        rd (semXIR I rowIR s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS e5 (by decide), by rw [size_decS, e6, i2], by rw [hd _ (by decide), e3],
      by rw [hd _ (by decide), e4, show tb + 40 * j + 40 = tb + 40 * (j + 1) by ring],
      fun v hv i hi => ?_, fun x hx hx2 => ?_⟩
    · rw [rdF_eq (hd _ (by simp only [rC3]; omega)) (hd _ (by simp only [rC3]; omega))]
      by_cases h : v = j + 1
      · subst h
        rw [show tb + 40 * (j + 1) + 2 * i = tb + 40 * j + 40 + 2 * i by ring, e1 i hi,
          wRow_succ_getD j hi]
      · rw [rdF_eq (e2 _ (by simp only [regs]; omega) (by omega))
          (e2 _ (by simp only [regs]; omega) (by omega)), i5 v (by omega) i hi]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC3]; omega), e2 x (by simp only [regs]; omega) (by omega),
        i6 x (by simp only [regs]; omega) (by omega)]
  have hP0 : P 0 ⟨entryK rC3 rN3 19 s2.M, s2.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z2, z1, z0], ?_, ?_, fun v hv i hi => ?_,
      fun x hx hx2 => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), l2]
    · dsimp only
      rw [hE _ (by decide) (by decide), b2 _ (by decide) (by decide), o3]; rfl
    · obtain rfl : v = 0 := by omega
      dsimp only
      rw [rdF_eq ((hE _ (by simp only [rC3]; omega) (by omega)).trans
          (b2 _ (by simp only [rLv]; omega) (by simp only [rN3]; omega)))
        ((hE _ (by simp only [rC3]; omega) (by omega)).trans
          (b2 _ (by simp only [rLv]; omega) (by simp only [rN3]; omega))),
        Nat.mul_zero, Nat.add_zero, o1 i hi, wRow_zero_getD hi]
    · dsimp only
      simp only [regs] at hx
      rw [hE _ (by simp only [rC3]; omega) (by omega), b2 _ (by simp only [rLv]; omega)
        (by simp only [rN3]; omega), o2 x (by simp only [regs]; omega) (by omega),
        hH0 x (by simp only [regs]; omega)]
  have := iterL_ind (f := semXIR I rowIR) (c := rC3) (m := 19) P step 19 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  obtain ⟨f1, f2, -, -, f5, f6⟩ := this
  exact ⟨fun v hv i hi => f5 v (by omega) i hi, fun x hx hx2 => f6 x hx (by omega), f1, f2⟩

/-! ## The decoding of a row on the machine -/

/-- **The machine decodes a row** (§6.2 step 4 with `bfly_decode_D`): if the row at `A` holds the
interpolated values `interpF D J u` on `D[0, 2^ℓ)` and `u` agrees with `Enc(c)` on `J`
(`|J| = 2^ℓ`, `J ⊆ [0, 2^20)`), the butterflies leave the message `c` in the row. -/
theorem bflyIR_decode (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ}
    (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 20) (hA : regs ≤ A) (hA2 : A + 2 * 2 ^ ℓ + 1 < 2 ^ 64)
    (hsz : A + 2 * 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 800 < 2 ^ 64)
    (hdisj : tb + 800 ≤ A ∨ A + 2 * 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    {J : Finset ℕ} (hJN : ∀ i ∈ J, i < nMax) (hJc : J.card = 2 ^ ℓ) (c : Fin (2 ^ ℓ) → F)
    (u : ℕ → F) (hu : ∀ i ∈ J, u i = encN D c i)
    (hY : ∀ i < 2 ^ ℓ, rdF s.M (A + 2 * i) = interpF D J u i) (i : Fin (2 ^ ℓ)) :
    rdF (semXIR I (bflyIR ℓ tb) s).M (A + 2 * i) = c i := by
  rw [(bflyIR_sem I s hM hℓ1 hℓ hA hA2 hsz htb htb2 hdisj hA0 hW hY).1 i i.2]
  exact bfly_decode_D (by simp only [logNMax]; omega) hJN hJc c u hu i

end FR.X

end G6_FRXBfly

section G6_FRXEncB

-- New for `flock-recursive` (BLUEPRINT §6.2 step 4: `Enc(g⁽ⁱ⁺¹⁾)`; stage S-H2, track L-ext).

/-!
# The forward butterflies: `Enc` on the machine's array (pure half)

BLUEPRINT §6.2 step 4 needs `Enc(f⁽ⁱ⁺¹⁾)` at every position of level `i`. S-D2's `encF` is the
sum `Σ_x c_x X_x(D j)`. A machine computes it as the forward additive NTT. That is the inverse of
`FRXDecodeB.bflyRun`, run top-down and in place. Level `l` maps the halves `u` (low) and `w` (high)
of each block of `2^(l+1)` to `u + α w` and `u + α w + w`, with `α = Ŵ_l(D base)`.

* `fwdRun_block`: after the levels `ℓ − 1, …, 0`, block `b` of size `2^ℓ` holds the values of
  its own coefficients on `D[b·2^ℓ, (b+1)·2^ℓ)`.
* **`fwdRun_enc`**: from a message of `2^m` coefficients zero-padded to `2^n`, the run of `n`
  levels gives `encF m c j` at every `j < 2^n`. One run covers all `2^(n−m)` cosets, so no coset
  offset is needed.
-/

namespace FR.X

open FR Finset Polynomial

/-- `b·2^k + j = b·2^k ⊕ j` for `j < 2^k`. -/
theorem mul_two_pow_add_eq_xor {b k j : ℕ} (hj : j < 2 ^ k) : b * 2 ^ k + j = b * 2 ^ k ^^^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hj, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases h : i < k
  · simp [h, show ¬ (k ≤ i) by omega]
  · rw [if_neg h, Nat.testBit_lt_two_pow (hj.trans_le (Nat.pow_le_pow_right (by norm_num)
      (by omega)))]
    simp [show k ≤ i by omega]

/-- `D` is additive on an aligned block: `D (b·2^k + j) = D (b·2^k) + D j` (`j < 2^k`). -/
theorem D_block {b k j : ℕ} (hj : j < 2 ^ k) : D (b * 2 ^ k + j) = D (b * 2 ^ k) + D j := by
  rw [mul_two_pow_add_eq_xor hj, D_xor]

section Fwd

variable {M : Type*} [Field M] [Algebra F M]

/-- **One forward level** `l`: in each block of `2^(l+1)` at `base`, the halves `u` (low) and
`w` (high) become `u + α w` (low) and `u + α w + w` (high), `α = Ŵ_l(D base)` (`bflyLevel`'s
inverse). -/
def fwdLevel (l : ℕ) (A : ℕ → M) (i : ℕ) : M :=
  let base := i / 2 ^ (l + 1) * 2 ^ (l + 1)
  let x := i % 2 ^ (l + 1)
  let u := A (base + x % 2 ^ l)
  let w := A (base + 2 ^ l + x % 2 ^ l)
  let α := algebraMap F M (wAtD l base)
  if x < 2 ^ l then u + α * w else u + α * w + w

/-- **The forward iteration**: levels `ℓ − 1, ℓ − 2, …, 0`. -/
def fwdRun : ℕ → (ℕ → M) → ℕ → M
  | 0, A => A
  | l + 1, A => fwdRun l (fwdLevel l A)

/-- `Ŵ_ℓ` on the block `b` of size `2^(ℓ+1)`: `Ŵ_ℓ(D(b·2^(ℓ+1) + j))` is `α` on the low half and
`α + 1` on the high half. -/
theorem normW_block {ℓ b j : ℕ} (hN : (b + 1) * 2 ^ (ℓ + 1) ≤ nMax) (hj : j < 2 ^ (ℓ + 1)) :
    (normW D ℓ).eval (D (b * 2 ^ (ℓ + 1) + j)) =
      wAtD ℓ (b * 2 ^ (ℓ + 1)) + if j < 2 ^ ℓ then 0 else 1 := by
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hℓ : ℓ < logNMax := by
    by_contra h
    have : 2 ^ (logNMax + 1) ≤ 2 ^ (ℓ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (ℓ + 1) ≤ (b + 1) * 2 ^ (ℓ + 1) := Nat.le_mul_of_pos_left _ (by omega)
    simp only [nMax, logNMax] at hN this; omega
  have hb : b * 2 ^ (ℓ + 1) < nMax := by
    have : 0 < 2 ^ (ℓ + 1) := by positivity
    nlinarith
  rw [D_block hj, normW_add D_xor, wAtD_eq hℓ hb]
  congr 1
  split_ifs with h
  · exact normW_eval_lt D h
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
    rw [two_pow_add_eq_xor (show j' < 2 ^ ℓ by omega), D_xor, normW_add D_xor,
      normW_eval_lt D (show j' < 2 ^ ℓ by omega), add_zero]
    exact normW_eval_self D_injOn_nMax hℓ

/-- **The block invariant**: after the levels `ℓ − 1, …, 0`, position `j` of block `b` holds the
value at `D(b·2^ℓ + j)` of the block's coefficients. -/
theorem fwdRun_block : ∀ (ℓ : ℕ) (A : ℕ → M) (b j : ℕ), j < 2 ^ ℓ → (b + 1) * 2 ^ ℓ ≤ nMax →
    fwdRun ℓ A (b * 2 ^ ℓ + j) = ∑ x ∈ range (2 ^ ℓ),
      A (b * 2 ^ ℓ + x) * algebraMap F M ((novelX D x).eval (D (b * 2 ^ ℓ + j))) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro A b j hj _
    obtain rfl : j = 0 := by simpa using hj
    simp [fwdRun, novelX, bitProd, bitSel]
  | succ ℓ ih =>
    intro A b j hj hN
    have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ ℓ := by positivity
    -- the level's value at the two halves
    have hval : ∀ x < 2 ^ ℓ, ∀ e < 2, fwdLevel ℓ A ((2 * b + e) * 2 ^ ℓ + x) =
        A (b * 2 ^ (ℓ + 1) + x) + algebraMap F M (wAtD ℓ (b * 2 ^ (ℓ + 1))) *
          A (b * 2 ^ (ℓ + 1) + 2 ^ ℓ + x) + if e = 0 then 0 else A (b * 2 ^ (ℓ + 1) + 2 ^ ℓ + x) := by
      intro x hx e he
      have hi : (2 * b + e) * 2 ^ ℓ + x = b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x) := by rw [hp]; ring
      have hlt : e * 2 ^ ℓ + x < 2 ^ (ℓ + 1) := by
        rw [hp]; interval_cases e <;> omega
      have hdiv : (b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x)) / 2 ^ (ℓ + 1) = b := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt,
          Nat.zero_add]
      have hmod : (b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x)) % 2 ^ (ℓ + 1) = e * 2 ^ ℓ + x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
      have hxm : (e * 2 ^ ℓ + x) % 2 ^ ℓ = x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      rw [hi, fwdLevel]
      simp only [hdiv, hmod, hxm]
      interval_cases e
      · simp [hx]
      · rw [if_neg (by omega), if_neg (by omega)]
    -- the target, split by the top coefficient bit
    have hN' : (2 * b + 1 + 1) * 2 ^ ℓ ≤ nMax := by
      have : (2 * b + 1 + 1) * 2 ^ ℓ = (b + 1) * 2 ^ (ℓ + 1) := by rw [hp]; ring
      omega
    have key : ∀ e < 2, ∀ j' < 2 ^ ℓ, j = e * 2 ^ ℓ + j' →
        fwdRun (ℓ + 1) A (b * 2 ^ (ℓ + 1) + j) = ∑ x ∈ range (2 ^ (ℓ + 1)),
          A (b * 2 ^ (ℓ + 1) + x) * algebraMap F M ((novelX D x).eval (D (b * 2 ^ (ℓ + 1) + j))) := by
      intro e he j' hj' hjj
      have hpos2 : b * 2 ^ (ℓ + 1) + j = (2 * b + e) * 2 ^ ℓ + j' := by rw [hjj, hp]; ring
      rw [fwdRun, hpos2, ih (fwdLevel ℓ A) (2 * b + e) j' hj' (by
        have : (2 * b + e + 1) * 2 ^ ℓ ≤ (2 * b + 1 + 1) * 2 ^ ℓ :=
          Nat.mul_le_mul_right _ (by omega)
        omega)]
      rw [← hpos2, sum_novel_succ, normW_block (by rwa [show (b + 1) * 2 ^ (ℓ + 1) =
        (2 * b + 1 + 1) * 2 ^ ℓ by rw [hp]; ring]) hj]
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.1 hx
      rw [hval x hx' e he]
      have hjlt : (j < 2 ^ ℓ) ↔ e = 0 := by
        constructor
        · intro h; by_contra h'; have : e = 1 := by omega
          subst this; omega
        · intro h; subst h; omega
      by_cases h0 : e = 0
      · rw [if_pos h0, if_pos (hjlt.2 h0), Nat.add_assoc, add_zero, add_zero]; ring
      · rw [if_neg h0, if_neg (fun h => h0 (hjlt.1 h)), Nat.add_assoc, map_add, map_one]; ring
    by_cases hlo : j < 2 ^ ℓ
    · exact key 0 (by norm_num) j hlo (by ring)
    · exact key 1 (by norm_num) (j - 2 ^ ℓ) (by rw [hp] at hj; omega) (by omega)

/-- **The forward run is `Enc`**: on a message `c` of `2^m` coefficients zero-padded to `2^n`
(`m ≤ n ≤ 20`), the `n` forward levels give `encF m c j` at every position `j < 2^n`. -/
theorem fwdRun_enc {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ logNMax) (c : Fin (2 ^ m) → M)
    (A : ℕ → M) (hA : ∀ x, A x = if h : x < 2 ^ m then c ⟨x, h⟩ else 0) {j : ℕ} (hj : j < 2 ^ n) :
    fwdRun n A j = encF m c j := by
  have hnN : 2 ^ n ≤ nMax := Nat.pow_le_pow_right (by norm_num) hn
  have hN : (0 + 1) * 2 ^ n ≤ nMax := by omega
  have h := fwdRun_block n A 0 j hj hN
  simp only [Nat.zero_mul, Nat.zero_add] at h
  have hm : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hmn
  rw [h, encF_eq (hmn.trans hn) (hj.trans_le hnN), encN,
    ← sum_range_add_sum_Ico _ hm, sum_eq_zero (s := Ico _ _) (fun x hx => by
      rw [hA x, dif_neg (by have := (mem_Ico.1 hx).1; omega), zero_mul]), add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun x => A x * algebraMap F M ((novelX D x).eval (D j)))]
  exact sum_congr rfl fun x _ => by rw [hA x, dif_pos x.2]

end Fwd

/-! ## Controls -/

/-- **Positive control**: one level on two points is `(u + α w, u + α w + w)`, `α = Ŵ₀(D 0)`. -/
theorem fwdRun_one (A : ℕ → F) :
    fwdRun 1 A 0 = A 0 + wAtD 0 0 * A 1 ∧ fwdRun 1 A 1 = A 0 + wAtD 0 0 * A 1 + A 1 := by
  simp [fwdRun, fwdLevel]

/-- **Inverse control**: on two points the forward level undoes `bflyRun`'s (so the forward
butterflies invert the decoder's, they are not a second inverse NTT). -/
theorem fwd_bfly_one (Y : ℕ → F) :
    fwdRun 1 (bflyRun D logNMax 0 1 Y) 0 = Y 0 ∧ fwdRun 1 (bflyRun D logNMax 0 1 Y) 1 = Y 1 := by
  obtain ⟨h0, h1⟩ := bflyRun_one (M := F) D logNMax 0 Y
  obtain ⟨f0, f1⟩ := fwdRun_one (bflyRun D logNMax 0 1 Y)
  rw [f0, f1, h0, h1]
  simp only [wAtD, Algebra.algebraMap_self, RingHom.id_apply]
  constructor <;> ring

end FR.X

end G6_FRXEncB

section G6_FRXFwd

-- New for `flock-recursive` (BLUEPRINT §6.2 step 4: `Enc(g⁽ⁱ⁺¹⁾)`; stage S-H2, track L-ext).

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

attribute [local irreducible] entryK storeM runPrims

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
  simp +decide only [fwdIR, fStep, fPre, flevelIR, fpairBody, pairPs, farithIR, alphaIR, alphaBody,
    ldF, stF, addF, addFC, WF, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAL1, rAH,
    rAH1, rTa, rTa1, rBit, uI, rTr, rC1, rN1, rC2, rN2, rC3, rN3, fAl, fU, fW, fH, fT, fN, fG, rKf,
    rTbf, cTmp, regs, mulF_wf_iff, mulF_writes_iff, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, exists_eq_or_imp, forall_eq, exists_eq_left, or_false, and_true]

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
  simp +decide only [farithIR, ldF, addF, addFC, WF, Prim.dst, fU, fW, fH, fT, fN, rAL1, rAH1,
    mulF_wf_iff, mulF_writes_iff, and_true]

theorem lo_farithIR : Lo farithIR := by
  simp +decide only [farithIR, ldF, addF, addFC, Lo, Prim.dst, regs, fU, fW, fH, fT, fN, rAL1, rAH1,
    mulF_lo_iff, and_true]

theorem wf_fpairBody : WF fpairBody := by
  simp +decide only [fpairBody, pairPs, farithIR, alphaIR, alphaBody, ldF, stF, addF, addFC, WF,
    Writes, Prim.dst, rQ, uX, uT1, uT2, rBs, rAL, rAL1, rAH, rAH1, rTa, rTa1, rBit, uI, rC2, rN2,
    fAl, fU, fW, fH, fT, fN, fG, cTmp, regs, mulF_wf_iff, mulF_writes_iff, or_false, and_true]

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
  have hM1 := inv_sem I (P := ldF fU rAL rAL1) (by simp +decide only [ldF, WF, Prim.dst, fU, rAL1,
    and_true]) hM
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
  have hM2 := inv_sem I (P := ldF fW rAH rAH1) (by simp +decide only [ldF, WF, Prim.dst, fW, rAH1,
    and_true]) hM1
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
  simp +decide only [fpairBody, pairPs, farithIR, alphaIR, alphaBody, ldF, stF, addF, addFC, Writes,
    Prim.dst, rQ, uX, uT1, uT2, rBs, rAL, rAL1, rAH, rAH1, rTa, rTa1, rBit, uI, rC2, rN2, fAl, fU,
    fW, fH, fT, fN, fG, cTmp, rA0, rP2, rTr, rLv, rC1, rN1, rC3, rN3, mulF_writes_iff, or_false]

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
      simp +decide only [alphaIR, alphaBody, ldF, Writes, Prim.dst, rBit, uT1, rTa, rTa1, fG, fAl,
        uI, rN2, rC2, cTmp, rAL, rAH, rQ, or_false])
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
      simp +decide only [farithIR, ldF, addF, addFC, Writes, Prim.dst, fU, fW, fH, fT, fN, rAL1,
        rAH1, rAL, rAH, rQ, mulF_writes_iff, or_false])
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
    simp +decide only [WF, Prim.dst, rKf, rTbf, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)]) s
  have hH0 := hframe I (.blk [.const rKf (toWord ℓ), .const rTbf (toWord tb), .const rN3 (toWord ℓ)]) s
    (by simp +decide only [Lo, Prim.dst, regs, rKf, rTbf, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
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
  have wpre : WF (.blk fPre) := by simp +decide only [fPre, WF, Prim.dst, rLv, uT1, rTr]
  have wl : WF (flevelIR ℓ) := by
    simp +decide only [flevelIR, fpairBody, pairPs, farithIR, alphaIR, alphaBody, ldF, stF, addF,
      addFC, WF, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAL1, rAH, rAH1, rTa, rTa1,
      rBit, uI, rTr, rC1, rN1, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, regs, mulF_wf_iff,
      mulF_writes_iff, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
      and_true]
  have wlb : WF (.blk [.op .sub rKf rKf cOne]) := by simp +decide only [WF, Prim.dst, rKf]
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rKf = toWord (ℓ - j) ∧ rd s'.M rTbf = toWord tb ∧ rd s'.M rA0 = toWord A ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 * 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdF s'.M (A + 2 * i) = fwdTop ℓ j Y i
  have step : ∀ j s', j < ℓ → P j s' → P (j + 1) (decS rC3 (semXIR I (fStep ℓ) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨p1, p2, p3⟩ := fPre_sem I s' i1 hj hℓ64 (tb := tb) (by omega) i3 i4
    have hM1 := inv_sem I wpre i1
    have hH1 := hframe I (.blk fPre) s' (by simp +decide only [fPre, Lo, Prim.dst, regs, rLv, uT1,
      rTr])
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
        simp +decide only [flevelIR, fpairBody, pairPs, farithIR, alphaIR, alphaBody, ldF, stF,
          addF, addFC, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAL1, rAH, rAH1, rTa,
          rTa1, rBit, uI, rTr, rC1, rN1, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, rA0, rKf,
          rTbf, mulF_writes_iff, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left,
          or_false])
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

end G6_FRXFwd
