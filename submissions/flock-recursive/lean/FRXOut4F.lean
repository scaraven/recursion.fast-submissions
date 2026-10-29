-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5; stage S-H4, pass 11, item 2: the
-- node output's segment emitters and the aggregate's segment count). 3.x analogue: `FRXOutRun`'s
-- `kflagIR`/`slotIR` (one kind flag, no ladder, no count).
import FRXOut4E

/-!
# The segments over the buffer, the ladder, the segment count

After the copy (`FRXOut4R.cpSeg_sem`) segment `i`'s words are the buffer's (`bufB`, shape
`apB`), so 3.x's `segIR` emits them unchanged (`FRXOut.segIR_sem` over `src M apB bufB`):

* **`bufSeg sg`** sets the buffer's context (`setB`) and emits `segOut (src M apB bufB) false 0 sg`;
* **`pfIR`** emits the proof's segment at the ladder of the buffer's word `10` (**`pfIR_sem`**:
  `pSeg4 seq4 (mOfB b)`, `b` the word's low byte; the three ladders are three copies, chosen by
  `b = 'P'` and `b ∈ {'K', 'M'}`, **`mOfB_eq`**);
* **`kSelIR κ a`** computes aggregate `a`'s segment count `kSel κ a w` into `qK` from the
  sub-slots' selector words (**`kSelIR_sem`**: per sub-slot the three selectors' `F` sum is `1`
  iff its low word is `1` and its high word `0`; the count stops at the first sub-slot that fails).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Specification -/

/-- The buffer's context: `oR := bufB`, depth-0 base `0`, the kind flag `0`. -/
def setB : XIR := .blk [.const oR (toWord bufB), .const (oBd 0) 0, .const oKF 0]

/-- **A segment over the buffer.** -/
def bufSeg (sg : Seg) : XIR := .seq setB (segIR apB 0 sg)

/-- The ladder flags from the buffer's word `10`'s low byte `b`: `qF0 := (b = 'P')`,
`qF1 := (b = 'K') ∨ (b = 'M')`. -/
def ladF : XIR :=
  .seq (.blk [.const oU (toWord 10)]) (.seq (ldw apB)
    (.blk [.const oK (toWord 255), .op .and oX oX oK, .const oK (toWord 0x50), .op .eq qF0 oX oK,
      .const oK (toWord 0x4B), .op .eq qF1 oX oK, .const oK (toWord 0x4D), .op .eq qT1 oX oK,
      .op .or qF1 qF1 qT1]))

/-- The proof's segment at ladder `m`. -/
def pfS (m : ℕ) : XIR := segIR apB 0 (pSeg4 seq4 m)

/-- **The proof over the buffer**, at the ladder of its word `10`. -/
def pfIR : XIR := .seq setB (.seq ladF (.ite qF0 (pfS 30) (.ite qF1 (pfS 31) (pfS 32))))

/-- **The ladder of a low byte**: `'P'` (`L30`) `30`; `'K'` (`L31`), `'M'` (`N2`) `31`; else `32`. -/
theorem mOfB_eq (b : UInt8) : mOfB b = if b = 0x50 then 30 else if b = 0x4B ∨ b = 0x4D then 31 else 32 := by
  unfold mOfB Snd.CKind.ofByte? SegKind.ofByte? NodeKind.ofByte?
  by_cases h1 : b = 0x50 <;> by_cases h2 : b = 0x4B <;> by_cases h3 : b = 0x4C <;> by_cases h4 : b = 0x4D <;>
    by_cases h5 : b = 0x4E <;> by_cases h6 : b = 0x4F <;> simp_all <;> rfl

/-! ## Proof helpers: the buffer's shape -/

theorem hA_B (x : Word) : regs ≤ (addrW apB (toWord bufB) x).toNat := by
  have := addrH_toNat (st := 20) (R := bufB) (u := x.toNat) le_rfl (by decide) x.isLt
  rw [toWord_toNat] at this
  rw [apB, this]; simp only [regs, bufB]; omega

theorem src_bufA (M : Mem) {u : ℕ} (hu : u < 2 ^ 64) : src M apB bufB u = rd M (bufA u) := by
  rw [src, bufA_apB hu]

theorem okSeg_pf : ∀ m ∈ [30, 31, 32], okSeg (pSeg4 seq4 m) = true ∧ depthSeg (pSeg4 seq4 m) ≤ 1 := by
  decide +kernel

theorem okSeg_tr : okSeg (trSeg4 seq4) = true ∧ depthSeg (trSeg4 seq4) ≤ 2 ∧ okSeg (trBody4 seq4) = true ∧
    depthSeg (trBody4 seq4) ≤ 2 := by
  decide +kernel

theorem low_iff (x : Word) {c : ℕ} (hc : c < 256) : x &&& toWord 255 = toWord c ↔ x.toNat.toUInt8 = c.toUInt8 := by
  rw [← BitVec.toNat_inj, ← UInt8.toNat_inj, BitVec.toNat_and, toNat_toWord (by norm_num : 255 < 2 ^ 64),
    toNat_toWord (by omega), show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  omega

/-- The low byte test as the machine computes it. -/
theorem low_eq (x : Word) {c : ℕ} (hc : c < 256) :
    XOp.eq.eval (XOp.and.eval x (toWord 255)) (toWord c) = if x.toNat.toUInt8 = c.toUInt8 then 1 else 0 := by
  simp only [XOp.eval]
  by_cases h : x.toNat.toUInt8 = c.toUInt8
  · have := (low_iff x hc).2 h; simp [this, h]
  · have := mt (low_iff x hc).1 h; simp [this, h]

/-! ## The buffer's segments -/

theorem setB_ctx (I : Array Word) {t : St} (hM : Inv t.M) :
    Ctx t.M bufB false (semXIR I setB t) ∧ rd (semXIR I setB t).M (oBd 0) = toWord 0 := by
  have hs := hM.1
  simp only [regs] at hs
  rw [setB, semXIR_blk]
  refine ⟨⟨inv_runPrims (by simp [Prim.dst, oR, oBd, oKF]) hM, size_runPrims _ _, fun y hy => ?_, ?_, ?_⟩, ?_⟩
  · exact rd_runPrims_of_not_writes (by simp only [regs] at hy; simp [Prim.dst, oR, oBd, oKF]; omega) _
  all_goals simp only [runPrims, List.foldl, Prim.run]
  all_goals simp (disch := (simp only [size_set, oR, oBd, oKF] at *; omega)) only [rd_set_self, rd_set_ne]
  all_goals first | rfl | simp

/-- **A segment over the buffer** emits its words over the heap's buffer; the heap is kept. -/
theorem bufSeg_sem (I : Array Word) (sg : Seg) (hok : okSeg sg = true) (hd : depthSeg sg ≤ 9) {M₀ : Mem}
    {t : St} (hO : OF M₀ t) :
    (semXIR I (bufSeg sg) t).o.toList = t.o.toList ++ segOut (src t.M apB bufB) false 0 sg ∧
      OF M₀ (semXIR I (bufSeg sg) t) ∧ ∀ y, regs ≤ y → rd (semXIR I (bufSeg sg) t).M y = rd t.M y := by
  obtain ⟨c1, b1⟩ := setB_ctx I hO.inv
  rw [bufSeg, semXIR_seq]
  have o1 : (semXIR I setB t).o = t.o := rfl
  generalize semXIR I setB t = t1 at c1 b1 o1
  obtain ⟨o2, c2, -⟩ := seg_step I apB hA_B sg hok hd c1 b1
  refine ⟨by rw [o2, o1], ⟨c2.inv, c2.size.trans hO.size, fun y h1 h2 => (c2.heap y h1).trans (hO.low y h1 h2)⟩,
    c2.heap⟩

theorem ladF_sem (I : Array Word) {M : Mem} {t : St} (hc : Ctx M bufB false t) (hb : rd t.M (oBd 0) = toWord 0) :
    (semXIR I ladF t).o = t.o ∧ Ctx M bufB false (semXIR I ladF t) ∧
      rd (semXIR I ladF t).M (oBd 0) = toWord 0 ∧
      rd (semXIR I ladF t).M qF0 = (if (src M apB bufB 10).toNat.toUInt8 = (0x50 : ℕ).toUInt8 then 1 else 0) ∧
      rd (semXIR I ladF t).M qF1 = (if (src M apB bufB 10).toNat.toUInt8 = (0x4B : ℕ).toUInt8 then 1 else 0) |||
        (if (src M apB bufB 10).toNat.toUInt8 = (0x4D : ℕ).toUInt8 then 1 else 0) := by
  have hs := hc.inv.1
  simp only [regs] at hs
  simp only [ladF, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.const oU (toWord 10)]) (by simp [Prim.dst, oU, oR, oKF, regs]) hc
  have u1 : rd (runPrims [.const oU (toWord 10)] t.M) oU = toWord 10 := by
    simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [oU]; omega)]
  have b1 : rd (runPrims [.const oU (toWord 10)] t.M) (oBd 0) = toWord 0 := by
    rw [rd_runPrims_of_not_writes (by simp [Prim.dst, oU, oBd])]; exact hb
  obtain ⟨l1, l2⟩ := ldw_src I apB hA_B _ c1 u1
  have c2 := ctx_ldw I apB c1
  have b2 := ldw_keep I apB _ c1.inv (r := oBd 0) (by simp [oBd, regs]) (by simp [oBd, oK, oT1, oT2, oT3, oAd, oX])
  generalize semXIR I (ldw apB) ⟨runPrims [.const oU (toWord 10)] t.M, t.o⟩ = t2 at l1 l2 c2 b2
  have hs2 := c2.inv.1
  simp only [regs] at hs2
  refine ⟨l2, ctx_blk (by simp [Prim.dst, oK, oX, qF0, qF1, qT1, oR, oKF, regs]) c2, ?_, ?_, ?_⟩
  · rw [rd_runPrims_of_not_writes (by simp [Prim.dst, oK, oX, qF0, qF1, qT1, oBd]), b2, b1]
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oX, qF0, qF1, qT1] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l1, low_eq _ (by norm_num)]
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oX, qF0, qF1, qT1] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l1]
    have e : ∀ c, c < 256 → XOp.eq.eval (XOp.and.eval (src M apB bufB 10) (toWord 255)) (toWord c) =
        if (src M apB bufB 10).toNat.toUInt8 = c.toUInt8 then 1 else 0 := fun c hc => low_eq _ hc
    rw [e _ (by norm_num), e _ (by norm_num)]
    rfl

theorem mOfB_flags (x : Word) :
    mOfB x.toNat.toUInt8 = if x.toNat.toUInt8 = (0x50 : ℕ).toUInt8 then 30 else
      if x.toNat.toUInt8 = (0x4B : ℕ).toUInt8 ∨ x.toNat.toUInt8 = (0x4D : ℕ).toUInt8 then 31 else 32 := by
  rw [mOfB_eq]; rfl

/-- **The proof's segment over the buffer**, at the ladder of the buffer's word `10`. -/
theorem pfIR_sem (I : Array Word) {M₀ : Mem} {t : St} (hO : OF M₀ t) :
    (semXIR I pfIR t).o.toList = t.o.toList ++
      segOut (src t.M apB bufB) false 0 (pSeg4 seq4 (mOfB (src t.M apB bufB 10).toNat.toUInt8)) ∧
      OF M₀ (semXIR I pfIR t) ∧ ∀ y, regs ≤ y → rd (semXIR I pfIR t).M y = rd t.M y := by
  obtain ⟨c1, b1⟩ := setB_ctx I hO.inv
  rw [pfIR, semXIR_seq]
  have o1 : (semXIR I setB t).o = t.o := rfl
  generalize semXIR I setB t = t1 at c1 b1 o1
  obtain ⟨o2, c2, b2, f0, f1⟩ := ladF_sem I c1 b1
  rw [semXIR_seq]
  generalize semXIR I ladF t1 = t2 at o2 c2 b2 f0 f1
  set x := src t.M apB bufB 10
  have hpf : ∀ m ∈ [30, 31, 32], (semXIR I (pfS m) t2).o.toList = t.o.toList ++
      segOut (src t.M apB bufB) false 0 (pSeg4 seq4 m) ∧ OF M₀ (semXIR I (pfS m) t2) ∧
      ∀ y, regs ≤ y → rd (semXIR I (pfS m) t2).M y = rd t.M y := fun m hm => by
    obtain ⟨g1, g2⟩ := okSeg_pf m hm
    obtain ⟨o3, c3, -⟩ := seg_step I apB hA_B (pSeg4 seq4 m) g1 (by omega) c2 b2
    exact ⟨by rw [pfS, o3, o2, o1], ⟨c3.inv, c3.size.trans hO.size, fun y h1 h2 => (c3.heap y h1).trans
      (hO.low y h1 h2)⟩, c3.heap⟩
  rw [mOfB_flags x, semXIR_ite, f0]
  by_cases h0 : x.toNat.toUInt8 = (0x50 : ℕ).toUInt8
  · simp only [h0, ↓reduceIte]
    first | exact hpf 30 (by simp) | (rw [if_neg (by decide : (1 : Word) ≠ 0)]; exact hpf 30 (by simp))
  · simp only [h0, ↓reduceIte]
    rw [semXIR_ite, f1]
    by_cases h1 : x.toNat.toUInt8 = (0x4B : ℕ).toUInt8 ∨ x.toNat.toUInt8 = (0x4D : ℕ).toUInt8
    · rw [if_pos h1]
      have : ((if x.toNat.toUInt8 = (0x4B : ℕ).toUInt8 then (1 : Word) else 0) |||
          if x.toNat.toUInt8 = (0x4D : ℕ).toUInt8 then 1 else 0) ≠ 0 := by
        rcases h1 with h | h <;> simp [h]
      rw [if_neg this]; exact hpf 31 (by simp)
    · rw [if_neg h1]
      have : ((if x.toNat.toUInt8 = (0x4B : ℕ).toUInt8 then (1 : Word) else 0) |||
          if x.toNat.toUInt8 = (0x4D : ℕ).toUInt8 then 1 else 0) = 0 := by
        rw [not_or] at h1; rw [if_neg h1.1, if_neg h1.2]; rfl
      rw [if_pos this]; exact hpf 32 (by simp)

end FR.X
