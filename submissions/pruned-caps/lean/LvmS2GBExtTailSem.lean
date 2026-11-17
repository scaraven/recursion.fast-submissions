-- New for lvm2 MP-B cap pruning (CAP-X, 2026-11-17): the semantics of the extractor's π-tail programs
-- (`LvmS2GBExtTail`).
import LvmS2GBExtTail
import LvmXDecCost

/-!
# The π tail's programs: semantics

* `cpWIR_sem`: the words `M[a … a + n)` are output; only `tA`, `tB` change.
* `clrIR_sem`: the cells `b … b + n − 1` become `0`; the other cells at or above `regs` are kept.
* `cntIR'_sem`: `tN` grows by the number of zero cells among `b … b + n − 1`.
* `nodesIR_sem`: the uncovered nodes' words in order.
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm.X

/-- The tail registers are registers. -/
theorem tregs : tA < regs ∧ tB < regs ∧ tC < regs ∧ tK < regs ∧ tN < regs := by decide

/-- One output word: `M[a]`, through `tA`, `tB`. -/
theorem cp1_sem (I : Array Word) (a : ℕ) (ha : regs ≤ a) (ha2 : a < 2 ^ 64) (s : St) (hM : Lvm.X.Inv s.M) :
    (semXIR I (.seq (.blk [.const tA (toWord a)]) (.seq (.load tB tA) (.out tB))) s).o.toList =
      s.o.toList ++ [Lvm.X.rd s.M a] ∧
    (∀ y, y ≠ tA → y ≠ tB → Lvm.X.rd (semXIR I (.seq (.blk [.const tA (toWord a)]) (.seq (.load tB tA) (.out tB))) s).M y =
      Lvm.X.rd s.M y) := by
  have hs := hM.1
  simp only [regs] at hs ha
  have hA : tA ≠ a := by simp only [tA]; omega
  refine ⟨?_, fun y h1 h2 => ?_⟩
  · simp only [semXIR, runPrims, List.foldl, Prim.run, Array.toList_push]
    simp (disch := ((try simp only [size_set, ne_eq]); (try simp only [tA, tB]); omega))
      [rd_set_self, rd_set_ne, toNat_toWord ha2, hA]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]

/-- **`cpWIR` outputs the words `M[a … a + n)`** (`a ≥ regs`), changes only `tA`, `tB`. -/
theorem cpWIR_sem (I : Array Word) : ∀ (n a : ℕ), regs ≤ a → a + n < 2 ^ 64 → ∀ (s : St), Lvm.X.Inv s.M →
    (semXIR I (cpWIR a n) s).o.toList = s.o.toList ++ (List.range n).map (fun k => Lvm.X.rd s.M (a + k)) ∧
    (∀ y, y ≠ tA → y ≠ tB → Lvm.X.rd (semXIR I (cpWIR a n) s).M y = Lvm.X.rd s.M y)
  | 0, a, _, _, s, hM => by simp [cpWIR, semXIR, runPrims]
  | n + 1, a, ha, ha2, s, hM => by
    have hwf : WF (.seq (.blk [.const tA (toWord a)]) (.seq (.load tB tA) (.out tB))) := by
      simp +decide [WF, Prim.dst, tA, tB]
    obtain ⟨e1, e2⟩ := cp1_sem I a ha (by omega) s hM
    obtain ⟨ih1, ih2⟩ := cpWIR_sem I n (a + 1) (by omega) (by omega) _ (inv_sem I hwf hM)
    refine ⟨?_, fun y h1 h2 => (ih2 y h1 h2).trans (e2 y h1 h2)⟩
    show (semXIR I (cpWIR (a + 1) n) (semXIR I _ s)).o.toList = _
    rw [ih1, e1, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.add_zero]
    congr 2
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply]
    have hr := tregs
    simp only [regs] at ha hr
    rw [e2 _ (by omega) (by omega), Nat.add_assoc, Nat.add_comm 1 k]

/-- The tail's scratch cells: `cTmp` and the tail registers but `tN`. -/
def TScr (i : ℕ) : Prop := i = cTmp ∨ i = tA ∨ i = tB ∨ i = tC ∨ i = tK

/-- One store of `v` at `b ≥ regs`. -/
theorem st1_sem (I : Array Word) (b : ℕ) (v : Word) (hb : regs ≤ b) (hb2 : b < 2 ^ 64) (s : St)
    (hM : Lvm.X.Inv s.M) (hbs : b < s.M.size) :
    (semXIR I (.seq (.blk [.const tA (toWord b), .const tC v]) (.store tA tC)) s).o = s.o ∧
    (∀ i, ¬ TScr i → Lvm.X.rd (semXIR I (.seq (.blk [.const tA (toWord b), .const tC v]) (.store tA tC)) s).M i =
      if i = b then v else Lvm.X.rd s.M i) := by
  have hs := hM.1
  simp only [regs] at hs hb
  refine ⟨by simp only [semXIR], fun i hi => ?_⟩
  simp only [TScr, not_or] at hi
  have hwf : WF (.blk [.const tA (toWord b), .const tC v]) := by simp +decide [WF, Prim.dst, tA, tC]
  have hM1 : Lvm.X.Inv (runPrims [.const tA (toWord b), .const tC v] s.M) := inv_sem I hwf hM
  simp only [semXIR]
  have hA : Lvm.X.rd (runPrims [.const tA (toWord b), .const tC v] s.M) tA = toWord b := by
    simp (disch := ((try simp only [size_set, ne_eq]); (try simp only [tA, tC]); omega))
      [runPrims, Prim.run, rd_set_self, rd_set_ne]
  rw [rd_storeM hM1 hA (by simp only [regs]; omega) hb2 (by rw [size_runPrims]; omega) (by simp only [tA, cTmp]; omega) (by simp only [tC, cTmp]; omega) hi.1]
  split_ifs with h
  · simp (disch := ((try simp only [size_set, ne_eq]); (try simp only [tA, tC]); omega))
      [runPrims, Prim.run, rd_set_self, rd_set_ne]
  · simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (Ne.symm hi.2.2.2.1), rd_set_ne (Ne.symm hi.2.1)]

/-- **`clrIR` zeroes `b … b + n − 1`** and keeps every other cell but the scratch. -/
theorem clrIR_sem (I : Array Word) : ∀ (n b : ℕ), regs ≤ b → b + n < 2 ^ 64 → ∀ (s : St), Lvm.X.Inv s.M →
    b + n ≤ s.M.size →
    (semXIR I (clrIR b n) s).o = s.o ∧
    (∀ i, ¬ TScr i → Lvm.X.rd (semXIR I (clrIR b n) s).M i = if b ≤ i ∧ i < b + n then 0 else Lvm.X.rd s.M i) ∧
    Lvm.X.Inv (semXIR I (clrIR b n) s).M ∧ (semXIR I (clrIR b n) s).M.size = s.M.size
  | 0, b, _, _, s, hM, _ => ⟨rfl, fun i _ => by simp [clrIR, semXIR, runPrims], by simpa [clrIR, semXIR, runPrims],
      by simp [clrIR, semXIR, runPrims]⟩
  | n + 1, b, hb, hb2, s, hM, hbs => by
    have hwf : WF (.seq (.blk [.const tA (toWord b), .const tC 0]) (.store tA tC)) := by
      simp +decide [WF, Prim.dst, tA, tC, cTmp]
    obtain ⟨e1, e2⟩ := st1_sem I b 0 hb (by omega) s hM (by omega)
    have hM1 := inv_sem I hwf hM
    have z1 := size_sem I (.seq (.blk [.const tA (toWord b), .const tC 0]) (.store tA tC)) s
    obtain ⟨ih1, ih2, ih3, ih4⟩ := clrIR_sem I n (b + 1) (by omega) (by omega) _ hM1 (by rw [z1]; omega)
    refine ⟨ih1.trans e1, fun i hi => ?_, ih3, ih4.trans z1⟩
    show Lvm.X.rd (semXIR I (clrIR (b + 1) n) (semXIR I _ s)).M i = _
    rw [ih2 i hi, e2 i hi]
    split_ifs <;> first | rfl | omega


/-! ## The marks -/

/-- **The `m`-bit field at bit `off`** of the words `w0`, `w1` (low first). -/
def fldW (w0 w1 : Word) (off m : ℕ) : ℕ := ((w0.toNat + 2 ^ 64 * w1.toNat) >>> off) % 2 ^ m

theorem fldW_lt (w0 w1 : Word) (off m : ℕ) : fldW w0 w1 off m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)

theorem fld_lo (w0 w1 : Word) (off m : ℕ) (hm : off + m ≤ 64) :
    ((w0 >>> off) &&& BitVec.ofNat 64 (2 ^ m - 1)).toNat = fldW w0 w1 off m := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [fldW, BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    show w0.toNat + 2 ^ 64 * w1.toNat = 2 ^ 64 * w1.toNat + w0.toNat by ring,
    Nat.testBit_two_pow_mul_add _ w0.isLt, ← BitVec.testBit_toNat]
  by_cases h1 : t < m
  · simp [h1, show t < 64 by omega, show off + t < 64 by omega]
  · simp [h1]

theorem fld_hi (w0 w1 : Word) (off m : ℕ) (ho : off < 64) (hm : 64 < off + m) (hm2 : m ≤ 64) :
    (((w0 >>> off) ||| (w1 <<< (64 - off))) &&& BitVec.ofNat 64 (2 ^ m - 1)).toNat = fldW w0 w1 off m := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [fldW, BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    show w0.toNat + 2 ^ 64 * w1.toNat = 2 ^ 64 * w1.toNat + w0.toNat by ring,
    Nat.testBit_two_pow_mul_add _ w0.isLt, ← BitVec.testBit_toNat, ← BitVec.testBit_toNat]
  by_cases h1 : t < m
  · by_cases h2 : off + t < 64
    · simp [h1, h2, show t < 64 by omega, show t < 64 - off by omega]
    · have h3 : (BitVec.toNat w0).testBit (off + t) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le w0.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have e : off + t - 64 = t - (64 - off) := by omega
      have e1 : t < 64 := by omega
      have e2 : ¬ t < 64 - off := by omega
      simp only [h1, h3, e1, e2, e, decide_true, decide_false, Bool.true_and, Bool.false_or, Bool.not_false,
        Bool.and_true, Bool.true_and, if_neg h2]
  · simp [h1]

/-- `mark1IR` before its store. -/
def mark1Pre (bm m a off : ℕ) : XIR :=
  .seq (.seq (.blk [.const tA (toWord a)]) (.load tB tA))
    (.seq (if off + m ≤ 64 then .blk [.const tK (toWord off), .op .shr tB tB tK]
      else .seq (.seq (.blk [.const tA (toWord (a + 1))]) (.load tC tA))
        (.blk [.const tK (toWord off), .op .shr tB tB tK, .const tK (toWord (64 - off)), .op .shl tC tC tK,
          .op .or tB tB tC]))
      (.blk [.const tK (toWord (2 ^ m - 1)), .op .and tB tB tK, .const tK (toWord bm), .op .add tB tB tK,
        .const tC 1]))

theorem mark1IR_eq (I : Array Word) (bm m a off : ℕ) (s : St) :
    semXIR I (mark1IR bm m a off) s = semXIR I (.store tB tC) (semXIR I (mark1Pre bm m a off) s) := by
  unfold mark1IR mark1Pre; split_ifs <;> rfl

theorem wf_mark1Pre (bm m a off : ℕ) : WF (mark1Pre bm m a off) := by
  unfold mark1Pre; split_ifs <;> simp +decide [WF, Prim.dst, tA, tB, tC, tK]

theorem wf_mark1IR (bm m a off : ℕ) : WF (mark1IR bm m a off) := by
  unfold mark1IR; split_ifs <;> simp +decide [WF, Prim.dst, tA, tB, tC, tK, cTmp]

theorem o_mark1IR (I : Array Word) (bm m a off : ℕ) (s : St) : (semXIR I (mark1IR bm m a off) s).o = s.o :=
  sem_o I _ s (by unfold mark1IR; split_ifs <;> rfl)

theorem semXIR_store (I : Array Word) (a v : ℕ) (s : St) : semXIR I (.store a v) s = ⟨storeM s.M a v, s.o⟩ := rfl

theorem semXIR_outB (I : Array Word) (v : ℕ) (s : St) : semXIR I (.out v) s = ⟨s.M, s.o.push (Lvm.X.rd s.M v)⟩ := rfl

theorem semXIR_blkB (I : Array Word) (ps : List Prim) (s : St) : semXIR I (.blk ps) s = ⟨runPrims ps s.M, s.o⟩ := rfl

theorem any_congr' {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self, any_congr' fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- The register values before the store. -/
theorem mark1Pre_sem (I : Array Word) (bm m a off : ℕ) (ha : regs ≤ a) (ha2 : a + 1 < 2 ^ 64) (hoff : off < 64)
    (hm : m ≤ 64) (hbm2 : bm + 2 ^ m < 2 ^ 64) (s : St) (hM : Lvm.X.Inv s.M) :
    Lvm.X.rd (semXIR I (mark1Pre bm m a off) s).M tB =
      toWord (bm + fldW (Lvm.X.rd s.M a) (Lvm.X.rd s.M (a + 1)) off m) ∧
    Lvm.X.rd (semXIR I (mark1Pre bm m a off) s).M tC = 1 ∧
    (∀ i, ¬ TScr i → Lvm.X.rd (semXIR I (mark1Pre bm m a off) s).M i = Lvm.X.rd s.M i) := by
  have hs := hM.1
  simp only [regs] at hs ha
  have hA : tA ≠ a := by simp only [tA]; omega
  have hA1 : tA ≠ a + 1 := by simp only [tA]; omega
  have hB1 : tB ≠ a + 1 := by simp only [tB]; omega
  have hm1 : 2 ^ m - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm; omega
  have hf := fldW_lt (Lvm.X.rd s.M a) (Lvm.X.rd s.M (a + 1)) off m
  have hfin : ∀ x : Word, x.toNat = fldW (Lvm.X.rd s.M a) (Lvm.X.rd s.M (a + 1)) off m →
      x + toWord bm = toWord (bm + fldW (Lvm.X.rd s.M a) (Lvm.X.rd s.M (a + 1)) off m) := fun x hx => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hx, toNat_toWord (by omega), toNat_toWord (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.add_comm]
  have eo : (toWord off).toNat % 64 = off := by rw [toNat_toWord (by omega), Nat.mod_eq_of_lt hoff]
  have eo' : (toWord (64 - off)).toNat % 64 = 64 - off ∨ off = 0 := by
    rcases Nat.eq_zero_or_pos off with h | h
    · exact .inr h
    · left; rw [toNat_toWord (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold mark1Pre
  split_ifs with hc
  · refine ⟨?_, ?_, fun i hi => ?_⟩
    · simp (disch := ((try simp only [size_set, ne_eq]); (try simp only [tA, tB, tC, tK]); omega))
        [semXIR, runPrims, Prim.run, rd_set_self, rd_set_ne, toNat_toWord (show a < 2 ^ 64 by omega), hA, XOp.eval,
          eo]
      exact hfin _ (fld_lo _ _ _ _ hc)
    · simp (disch := ((try simp only [size_set, ne_eq]); (try simp only [tA, tB, tC, tK]); omega))
        [semXIR, runPrims, Prim.run, rd_set_self, rd_set_ne]
    · simp only [TScr, not_or, tA, tB, tC, tK, cTmp] at hi
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := ((try simp only [ne_eq]); (try simp only [tA, tB, tC, tK]); omega)) only [rd_set_ne]
  · have hoff0 : off ≠ 0 := by omega
    have eo2 : (toWord (64 - off)).toNat % 64 = 64 - off := by
      rcases eo' with h | h
      · exact h
      · exact absurd h hoff0
    refine ⟨?_, ?_, fun i hi => ?_⟩
    · simp (disch := ((try simp only [size_set, ne_eq]); (try simp only [tA, tB, tC, tK]); omega))
        [semXIR, runPrims, Prim.run, rd_set_self, rd_set_ne, toNat_toWord (show a < 2 ^ 64 by omega),
          toNat_toWord ha2, hA, hA1, XOp.eval, eo, eo2]
      exact hfin _ (fld_hi _ _ _ _ hoff (by omega) hm)
    · simp (disch := ((try simp only [size_set, ne_eq]); (try simp only [tA, tB, tC, tK]); omega))
        [semXIR, runPrims, Prim.run, rd_set_self, rd_set_ne]
    · simp only [TScr, not_or, tA, tB, tC, tK, cTmp] at hi
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := ((try simp only [ne_eq]); (try simp only [tA, tB, tC, tK]); omega)) only [rd_set_ne]

/-- **One mark**: `M[bm + x] := 1`, `x` the field of the words at `a`, `a + 1`; the cells but the scratch kept. -/
theorem mark1IR_sem (I : Array Word) (bm m a off : ℕ) (ha : regs ≤ a) (ha2 : a + 1 < 2 ^ 64) (hoff : off < 64)
    (hm : m ≤ 64) (hbm : regs ≤ bm) (hbm2 : bm + 2 ^ m < 2 ^ 64) (s : St) (hM : Lvm.X.Inv s.M)
    (hbs : bm + 2 ^ m ≤ s.M.size) :
    (semXIR I (mark1IR bm m a off) s).o = s.o ∧
    (∀ i, ¬ TScr i → Lvm.X.rd (semXIR I (mark1IR bm m a off) s).M i =
      if i = bm + fldW (Lvm.X.rd s.M a) (Lvm.X.rd s.M (a + 1)) off m then 1 else Lvm.X.rd s.M i) := by
  obtain ⟨p1, p2, p3⟩ := mark1Pre_sem I bm m a off ha ha2 hoff hm hbm2 s hM
  have hM1 := inv_sem I (wf_mark1Pre bm m a off) hM
  have z1 := size_sem I (mark1Pre bm m a off) s
  have hf := fldW_lt (Lvm.X.rd s.M a) (Lvm.X.rd s.M (a + 1)) off m
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  refine ⟨o_mark1IR I bm m a off s, fun i hi => ?_⟩
  have hiT : i ≠ cTmp := fun h => hi (.inl h)
  rw [mark1IR_eq, semXIR_store]
  rw [rd_storeM hM1 p1 (by simp only [regs] at hbm ⊢; omega) (by omega) (by rw [z1]; omega)
    (by simp only [tB, cTmp]; omega) (by simp only [tC, cTmp]; omega) hiT, p2, p3 i hi]

/-- **The marks of a level**: `M[bm + x] := 1` for every path's field `x`. -/
theorem markIR_sem (I : Array Word) (bm m : ℕ) (hm : m ≤ 64) (hbm : regs ≤ bm) (hbm2 : bm + 2 ^ m < 2 ^ 64) :
    ∀ (ps : List (ℕ × ℕ)) (s : St), Lvm.X.Inv s.M → bm + 2 ^ m ≤ s.M.size →
    (∀ p ∈ ps, bm + 2 ^ m ≤ p.1 ∧ p.1 + 1 < 2 ^ 64 ∧ p.2 < 64) →
    (semXIR I (markIR bm m ps) s).o = s.o ∧
    (∀ i, ¬ TScr i → Lvm.X.rd (semXIR I (markIR bm m ps) s).M i =
      if ps.any (fun p => i == bm + fldW (Lvm.X.rd s.M p.1) (Lvm.X.rd s.M (p.1 + 1)) p.2 m) then 1
      else Lvm.X.rd s.M i) ∧
    Lvm.X.Inv (semXIR I (markIR bm m ps) s).M ∧ (semXIR I (markIR bm m ps) s).M.size = s.M.size
  | [], s, hM, _, _ => ⟨rfl, fun i _ => by simp [markIR, semXIR, runPrims], by simpa [markIR, semXIR, runPrims],
      by simp [markIR, semXIR, runPrims]⟩
  | (a, off) :: ps, s, hM, hbs, hp => by
    have h0 := hp (a, off) List.mem_cons_self
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
    have hreg : regs ≤ a := le_trans hbm (le_trans (Nat.le_add_right _ _) h0.1)
    obtain ⟨e1, e2⟩ := mark1IR_sem I bm m a off hreg h0.2.1 h0.2.2 hm hbm hbm2 s hM hbs
    have hM1 := inv_sem I (wf_mark1IR bm m a off) hM
    have z1 := size_sem I (mark1IR bm m a off) s
    obtain ⟨ih1, ih2, ih3, ih4⟩ := markIR_sem I bm m hm hbm hbm2 ps _ hM1 (by rw [z1]; exact hbs)
      fun p hp' => hp p (List.mem_cons_of_mem _ hp')
    have hf := fldW_lt (Lvm.X.rd s.M a) (Lvm.X.rd s.M (a + 1)) off m
    -- the reads of the later paths are above the bitmap
    have hk : ∀ p ∈ ps, Lvm.X.rd (semXIR I (mark1IR bm m a off) s).M p.1 = Lvm.X.rd s.M p.1 ∧
        Lvm.X.rd (semXIR I (mark1IR bm m a off) s).M (p.1 + 1) = Lvm.X.rd s.M (p.1 + 1) := fun p hp' => by
      have h1 := hp p (List.mem_cons_of_mem _ hp')
      have hnt : ∀ y, bm + 2 ^ m ≤ y → ¬ TScr y := fun y hy h => by
        simp only [TScr, cTmp, tA, tB, tC, tK, regs] at h hbm; omega
      rw [e2 _ (hnt _ h1.1), e2 _ (hnt _ (by omega)), if_neg (by omega), if_neg (by omega)]
      exact ⟨rfl, rfl⟩
    refine ⟨ih1.trans e1, fun i hi => ?_, ih3, ih4.trans z1⟩
    show Lvm.X.rd (semXIR I (markIR bm m ps) (semXIR I (mark1IR bm m a off) s)).M i = _
    rw [ih2 i hi, e2 i hi]
    have ea : ps.any (fun p => i == bm + fldW (Lvm.X.rd (semXIR I (mark1IR bm m a off) s).M p.1)
        (Lvm.X.rd (semXIR I (mark1IR bm m a off) s).M (p.1 + 1)) p.2 m) =
        ps.any (fun p => i == bm + fldW (Lvm.X.rd s.M p.1) (Lvm.X.rd s.M (p.1 + 1)) p.2 m) :=
      any_congr' fun p hp' => by rw [(hk p hp').1, (hk p hp').2]
    rw [ea, List.any_cons]
    by_cases h1 : i = bm + fldW (Lvm.X.rd s.M a) (Lvm.X.rd s.M (a + 1)) off m
    · simp [h1]
    · rw [show (i == bm + fldW (Lvm.X.rd s.M a) (Lvm.X.rd s.M (a + 1)) off m) = false by simp [h1],
        Bool.false_or, if_neg h1]


/-! ## The bitmaps -/

/-- The levels' bitmaps follow each other from `b`. -/
def BmChain : ℕ → List TLv → Prop
  | _, [] => True
  | b, l :: ls => l.bm = b ∧ BmChain (b + 2 ^ l.m) ls

/-- The end of the bitmaps from `b`. -/
def bmEnd : ℕ → List TLv → ℕ
  | b, [] => b
  | b, l :: ls => bmEnd (b + 2 ^ l.m) ls

theorem le_bmEnd : ∀ (ls : List TLv) (b : ℕ), b ≤ bmEnd b ls
  | [], _ => le_rfl
  | l :: ls, b => le_trans (Nat.le_add_right _ _) (le_bmEnd ls (b + 2 ^ l.m))

/-- **Layer node `x` of level `l` is covered** in the memory `R`: some path's field is `x`. -/
def covW (R : ℕ → Word) (l : TLv) (x : ℕ) : Bool := l.pos.any fun p => x == fldW (R p.1) (R (p.1 + 1)) p.2 l.m

theorem covW_congr {R R' : ℕ → Word} {l : TLv} (h : ∀ p ∈ l.pos, R p.1 = R' p.1 ∧ R (p.1 + 1) = R' (p.1 + 1))
    (x : ℕ) : covW R l x = covW R' l x :=
  any_congr' fun p hp => by rw [(h p hp).1, (h p hp).2]

theorem not_tscr {y : ℕ} (h : regs ≤ y) : ¬ TScr y := fun h' => by
  simp only [TScr, cTmp, tA, tB, tC, tK, regs] at h h'; omega

/-- **The bitmaps** (`bmIR`): level `l`'s cell `x` is `1` iff `x` is covered (in the memory before), the cells
outside the bitmaps but the scratch kept. -/
theorem bmIR_sem (I : Array Word) : ∀ (ls : List TLv) (b : ℕ) (s : St), Lvm.X.Inv s.M → regs ≤ b → BmChain b ls →
    bmEnd b ls ≤ s.M.size → bmEnd b ls < 2 ^ 64 →
    (∀ l ∈ ls, l.m ≤ 64 ∧ ∀ p ∈ l.pos, bmEnd b ls ≤ p.1 ∧ p.1 + 1 < 2 ^ 64 ∧ p.2 < 64) →
    (semXIR I (bmIR ls) s).o = s.o ∧
    (∀ i, ¬ TScr i → (i < b ∨ bmEnd b ls ≤ i) → Lvm.X.rd (semXIR I (bmIR ls) s).M i = Lvm.X.rd s.M i) ∧
    (∀ l ∈ ls, ∀ x < 2 ^ l.m,
      Lvm.X.rd (semXIR I (bmIR ls) s).M (l.bm + x) = if covW (Lvm.X.rd s.M) l x then 1 else 0) ∧
    Lvm.X.Inv (semXIR I (bmIR ls) s).M ∧ (semXIR I (bmIR ls) s).M.size = s.M.size
  | [], b, s, hM, _, _, _, _, _ => ⟨rfl, fun _ _ _ => rfl, fun _ h => by simp at h, hM, rfl⟩
  | l :: ls, b, s, hM, hb, hc, hbs, hb2, hl => by
    obtain ⟨hlb, hc'⟩ := hc
    have hl0 := hl l List.mem_cons_self
    have hE := le_bmEnd ls (b + 2 ^ l.m)
    simp only [bmEnd] at hbs hb2 hl
    have hpos : 0 < 2 ^ l.m := Nat.two_pow_pos l.m
    -- the clear
    obtain ⟨c1, c2, c3, c4⟩ := clrIR_sem I (2 ^ l.m) l.bm (hlb ▸ hb) (by omega) s hM (by omega)
    -- the marks
    obtain ⟨k1, k2, k3, k4⟩ := markIR_sem I l.bm l.m hl0.1 (hlb ▸ hb) (by omega) l.pos _ c3 (by omega)
      fun p hp => by have := hl0.2 p hp; simp only [bmEnd] at this; exact ⟨by omega, this.2⟩
    generalize hs1 : semXIR I (clrIR l.bm (2 ^ l.m)) s = s1 at c1 c2 c3 c4 k1 k2 k3 k4
    generalize hs2 : semXIR I (markIR l.bm l.m l.pos) s1 = s2 at k1 k2 k3 k4
    -- the reads above the bitmaps
    have hr1 : ∀ y, bmEnd (b + 2 ^ l.m) ls ≤ y → Lvm.X.rd s1.M y = Lvm.X.rd s.M y := fun y hy => by
      rw [c2 y (not_tscr (by omega)), if_neg (by omega)]
    have hcov1 : ∀ x, covW (Lvm.X.rd s1.M) l x = covW (Lvm.X.rd s.M) l x := covW_congr fun p hp => by
      have := hl0.2 p hp; simp only [bmEnd] at this
      exact ⟨hr1 _ this.1, hr1 _ (by omega)⟩
    have hk2 : ∀ i, ¬ TScr i → (i < l.bm ∨ l.bm + 2 ^ l.m ≤ i) → Lvm.X.rd s2.M i = Lvm.X.rd s.M i := fun i hi h => by
      rw [k2 i hi]
      have hn : (l.pos.any fun p => i == l.bm + fldW (Lvm.X.rd s1.M p.1) (Lvm.X.rd s1.M (p.1 + 1)) p.2 l.m) = false := by
        rw [List.any_eq_false]; intro p _
        have := fldW_lt (Lvm.X.rd s1.M p.1) (Lvm.X.rd s1.M (p.1 + 1)) p.2 l.m
        simp only [beq_iff_eq]; omega
      rw [hn, if_neg (by decide), c2 i hi, if_neg (by omega)]
    -- the later levels
    obtain ⟨i1, i2, i3, i4, i5⟩ := bmIR_sem I ls (b + 2 ^ l.m) s2 k3 (by omega) hc' (by rw [k4, c4]; exact hbs) hb2
      fun l' hl' => ⟨(hl l' (List.mem_cons_of_mem _ hl')).1, (hl l' (List.mem_cons_of_mem _ hl')).2⟩
    have e : semXIR I (bmIR (l :: ls)) s = semXIR I (bmIR ls) s2 := by
      rw [← hs2, ← hs1]; rfl
    rw [e]
    have hEq : bmEnd b (l :: ls) = bmEnd (b + 2 ^ l.m) ls := rfl
    refine ⟨by rw [i1, k1, c1], fun i hi h => ?_, fun l' hl' x hx => ?_, i4, by rw [i5, k4, c4]⟩
    · rw [hEq] at h
      rw [i2 i hi (by omega), hk2 i hi (by omega)]
    · rcases List.mem_cons.1 hl' with hl' | hl'
      · subst hl'
        have hreg : regs ≤ l'.bm + x := le_trans (hlb ▸ hb) (Nat.le_add_right _ _)
        rw [i2 _ (not_tscr hreg) (.inl (by omega)), k2 _ (not_tscr hreg), c2 _ (not_tscr hreg),
          if_pos (show l'.bm ≤ l'.bm + x ∧ l'.bm + x < l'.bm + 2 ^ l'.m from ⟨by omega, by omega⟩), ← hcov1 x, covW]
        have ea : (l'.pos.any fun p => l'.bm + x == l'.bm + fldW (Lvm.X.rd s1.M p.1) (Lvm.X.rd s1.M (p.1 + 1)) p.2 l'.m) =
            (l'.pos.any fun p => x == fldW (Lvm.X.rd s1.M p.1) (Lvm.X.rd s1.M (p.1 + 1)) p.2 l'.m) :=
          any_congr' fun p _ => by rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, Nat.add_left_cancel_iff]
        rw [ea]
      · rw [i3 l' hl' x hx, covW_congr (R' := Lvm.X.rd s.M) (fun p hp => ?_) x]
        have := (hl l' (List.mem_cons_of_mem _ hl')).2 p hp
        have hE' := le_bmEnd ls (b + 2 ^ l.m)
        exact ⟨hk2 _ (not_tscr (by simp only [regs] at hb ⊢; omega)) (.inr (by omega)),
          hk2 _ (not_tscr (by simp only [regs] at hb ⊢; omega)) (.inr (by omega))⟩

/-! ## The count and the size word -/

/-- The zero cells among `b … b + n − 1`. -/
def cntZ (R : ℕ → Word) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | b, n + 1 => (if R b = 0 then 1 else 0) + cntZ R (b + 1) n

theorem cntZ_le (R : ℕ → Word) : ∀ b n, cntZ R b n ≤ n
  | _, 0 => le_rfl
  | b, n + 1 => by have := cntZ_le R (b + 1) n; unfold cntZ; split_ifs <;> omega

theorem cntZ_congr {R R' : ℕ → Word} : ∀ b n, (∀ x < n, R (b + x) = R' (b + x)) → cntZ R b n = cntZ R' b n
  | _, 0, _ => rfl
  | b, n + 1, h => by
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    have ih := cntZ_congr (R := R) (R' := R') (b + 1) n fun x hx => by
      simpa only [Nat.add_assoc, Nat.add_comm 1 x] using h (x + 1) (by omega)
    rw [cntZ, cntZ, h0, ih]

/-- One cell of the count. -/
def cnt1 (b : ℕ) : XIR :=
  .seq (.blk [.const tA (toWord b)]) (.seq (.load tB tA) (.blk [.const tK 0, .op .eq tB tB tK, .op .add tN tN tB]))

theorem wf_cnt1 (b : ℕ) : WF (cnt1 b) := by simp +decide [cnt1, WF, Prim.dst, tA, tB, tK, tN]

theorem cnt1_sem (I : Array Word) (b : ℕ) (hb : regs ≤ b) (hb2 : b < 2 ^ 64) (s : St) (hM : Lvm.X.Inv s.M) :
    (semXIR I (cnt1 b) s).o = s.o ∧
    (∀ i, ¬ TScr i → i ≠ tN → Lvm.X.rd (semXIR I (cnt1 b) s).M i = Lvm.X.rd s.M i) ∧
    Lvm.X.rd (semXIR I (cnt1 b) s).M tN = Lvm.X.rd s.M tN + toWord (if Lvm.X.rd s.M b = 0 then 1 else 0) := by
  have hs := hM.1
  simp only [regs] at hs hb
  have hA : tA ≠ b := by simp only [tA]; omega
  refine ⟨sem_o I _ s rfl, fun i hi hN => ?_, ?_⟩
  · simp only [TScr, not_or, tA, tB, tC, tK, cTmp] at hi
    simp only [tN] at hN
    simp only [cnt1, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := ((try simp only [ne_eq]); (try simp only [tA, tB, tC, tK, tN]); omega)) only [rd_set_ne]
  · simp (disch := ((try simp only [size_set, ne_eq]); (try simp only [tA, tB, tK, tN]); omega))
      [cnt1, semXIR, runPrims, Prim.run, rd_set_self, rd_set_ne, toNat_toWord hb2, hA, XOp.eval]
    split_ifs <;> rfl

theorem cntIR'_eq (b n : ℕ) : cntIR' b (n + 1) = .seq (cnt1 b) (cntIR' (b + 1) n) := rfl

/-- **The count**: `tN +=` the zero cells among `b … b + n − 1`; the cells but the scratch and `tN` kept. -/
theorem cntIR'_sem (I : Array Word) : ∀ (n b : ℕ), regs ≤ b → b + n < 2 ^ 64 → ∀ (s : St), Lvm.X.Inv s.M →
    (semXIR I (cntIR' b n) s).o = s.o ∧
    (∀ i, ¬ TScr i → i ≠ tN → Lvm.X.rd (semXIR I (cntIR' b n) s).M i = Lvm.X.rd s.M i) ∧
    Lvm.X.rd (semXIR I (cntIR' b n) s).M tN = Lvm.X.rd s.M tN + toWord (cntZ (Lvm.X.rd s.M) b n) ∧
    Lvm.X.Inv (semXIR I (cntIR' b n) s).M ∧ (semXIR I (cntIR' b n) s).M.size = s.M.size
  | 0, b, _, _, s, hM => ⟨rfl, fun _ _ _ => rfl, by
      show Lvm.X.rd s.M tN = Lvm.X.rd s.M tN + toWord 0
      exact (BitVec.add_zero _).symm, hM, rfl⟩
  | n + 1, b, hb, hb2, s, hM => by
    obtain ⟨e1, e2, e3⟩ := cnt1_sem I b hb (by omega) s hM
    have hM1 := inv_sem I (wf_cnt1 b) hM
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := cntIR'_sem I n (b + 1) (by omega) (by omega) _ hM1
    rw [cntIR'_eq, semXIR_seq]
    have hc : cntZ (Lvm.X.rd (semXIR I (cnt1 b) s).M) (b + 1) n = cntZ (Lvm.X.rd s.M) (b + 1) n :=
      cntZ_congr _ _ fun x _ => e2 _ (not_tscr (by simp only [regs] at hb ⊢; omega))
        (by simp only [tN, regs] at hb ⊢; omega)
    refine ⟨ih1.trans e1, fun i hi hN => (ih2 i hi hN).trans (e2 i hi hN), ?_, ih4, ih5.trans (size_sem ..)⟩
    rw [ih3, e3, hc, cntZ, BitVec.add_assoc, toWord_add]

/-- **The count over the levels.** -/
theorem cntAllIR_sem (I : Array Word) : ∀ (ls : List TLv) (s : St), Lvm.X.Inv s.M →
    (∀ l ∈ ls, regs ≤ l.bm ∧ l.bm + 2 ^ l.m < 2 ^ 64) →
    (semXIR I (cntAllIR ls) s).o = s.o ∧
    (∀ i, ¬ TScr i → i ≠ tN → Lvm.X.rd (semXIR I (cntAllIR ls) s).M i = Lvm.X.rd s.M i) ∧
    Lvm.X.rd (semXIR I (cntAllIR ls) s).M tN =
      Lvm.X.rd s.M tN + toWord (ls.map fun l => cntZ (Lvm.X.rd s.M) l.bm (2 ^ l.m)).sum ∧
    Lvm.X.Inv (semXIR I (cntAllIR ls) s).M ∧ (semXIR I (cntAllIR ls) s).M.size = s.M.size
  | [], s, hM, _ => ⟨rfl, fun _ _ _ => rfl, by
      show Lvm.X.rd s.M tN = Lvm.X.rd s.M tN + toWord 0
      exact (BitVec.add_zero _).symm, hM, rfl⟩
  | l :: ls, s, hM, hl => by
    have hl0 := hl l List.mem_cons_self
    obtain ⟨e1, e2, e3, e4, e5⟩ := cntIR'_sem I (2 ^ l.m) l.bm hl0.1 hl0.2 s hM
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := cntAllIR_sem I ls _ e4 fun l' hl' => hl l' (List.mem_cons_of_mem _ hl')
    have e : semXIR I (cntAllIR (l :: ls)) s = semXIR I (cntAllIR ls) (semXIR I (cntIR' l.bm (2 ^ l.m)) s) := rfl
    rw [e]
    have hc : (ls.map fun l' => cntZ (Lvm.X.rd (semXIR I (cntIR' l.bm (2 ^ l.m)) s).M) l'.bm (2 ^ l'.m)) =
        ls.map fun l' => cntZ (Lvm.X.rd s.M) l'.bm (2 ^ l'.m) :=
      List.map_congr_left fun l' hl' => cntZ_congr _ _ fun x _ => by
        have := hl l' (List.mem_cons_of_mem _ hl')
        exact e2 _ (not_tscr (by omega)) (by simp only [tN, regs] at this ⊢; omega)
    refine ⟨ih1.trans e1, fun i hi hN => (ih2 i hi hN).trans (e2 i hi hN), ?_, ih4, ih5.trans e5⟩
    rw [ih3, e3, hc, List.map_cons, List.sum_cons, BitVec.add_assoc, toWord_add]

/-- **The size word**: `pz0 + 32 ·` the zero cells of the levels' bitmaps is output. -/
theorem sizeWIR_sem (I : Array Word) (pz0 : ℕ) (ls : List TLv) (s : St) (hM : Lvm.X.Inv s.M)
    (hl : ∀ l ∈ ls, regs ≤ l.bm ∧ l.bm + 2 ^ l.m < 2 ^ 64)
    (hz : pz0 + 32 * (ls.map fun l => cntZ (Lvm.X.rd s.M) l.bm (2 ^ l.m)).sum < 2 ^ 64) :
    (semXIR I (sizeWIR pz0 ls) s).o.toList =
      s.o.toList ++ [toWord (pz0 + 32 * (ls.map fun l => cntZ (Lvm.X.rd s.M) l.bm (2 ^ l.m)).sum)] ∧
    (∀ i, ¬ TScr i → i ≠ tN → Lvm.X.rd (semXIR I (sizeWIR pz0 ls) s).M i = Lvm.X.rd s.M i) ∧
    Lvm.X.Inv (semXIR I (sizeWIR pz0 ls) s).M ∧ (semXIR I (sizeWIR pz0 ls) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const tN 0]) := by simp +decide [WF, Prim.dst, tN]
  have hM1 := inv_sem I wf0 hM
  have hc : ∀ l ∈ ls, cntZ (Lvm.X.rd (semXIR I (.blk [.const tN 0]) s).M) l.bm (2 ^ l.m) =
      cntZ (Lvm.X.rd s.M) l.bm (2 ^ l.m) := fun l hl' => cntZ_congr _ _ fun x _ => by
    have := hl l hl'
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by simp only [tN, regs] at this ⊢; omega)]
  have h0 : Lvm.X.rd (semXIR I (.blk [.const tN 0]) s).M tN = 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [tN]; omega)]
  obtain ⟨e1, e2, e3, e4, e5⟩ := cntAllIR_sem I ls _ hM1 hl
  rw [List.map_congr_left hc, h0] at e3
  replace e3 := e3.trans (BitVec.zero_add _)
  generalize (ls.map fun l => cntZ (Lvm.X.rd s.M) l.bm (2 ^ l.m)).sum = C at e3 hz
  have wf2 : WF (.blk [.const tK 5, .op .shl tN tN tK, .const tK (toWord pz0), .op .add tN tN tK]) := by
    simp +decide [WF, Prim.dst, tN, tK]
  have o0 : (semXIR I (.blk [.const tN 0]) s).o = s.o := rfl
  have z0 : (semXIR I (.blk [.const tN 0]) s).M.size = s.M.size := size_sem ..
  have f0 : ∀ i, i ≠ tN → Lvm.X.rd (semXIR I (.blk [.const tN 0]) s).M i = Lvm.X.rd s.M i := fun i hi => by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (Ne.symm hi)]
  rw [sizeWIR, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_outB,
    semXIR_blkB I [.const tK 5, .op .shl tN tN tK, .const tK (toWord pz0), .op .add tN tN tK]]
  rw [o0] at e1
  rw [z0] at e5
  have e2' : ∀ i, ¬ TScr i → i ≠ tN →
      Lvm.X.rd (semXIR I (cntAllIR ls) (semXIR I (.blk [.const tN 0]) s)).M i = Lvm.X.rd s.M i :=
    fun i hi hN => (e2 i hi hN).trans (f0 i hN)
  generalize semXIR I (cntAllIR ls) (semXIR I (.blk [.const tN 0]) s) = S at e1 e2' e3 e4 e5
  have hs2 := e4.1
  simp only [regs] at hs2
  refine ⟨?_, fun i hi hN => ?_, inv_sem I wf2 (s := S) e4, by rw [size_runPrims, e5]⟩
  · rw [Array.toList_push, e1]
    apply congrArg (fun v => s.o.toList ++ [v])
    simp (disch := ((try simp only [size_set, ne_eq]); (try simp only [tK, tN]); omega))
      [runPrims, Prim.run, rd_set_self, rd_set_ne, XOp.eval, e3]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, toNat_toWord (by omega), toNat_toWord (by omega),
      toNat_toWord (by omega)]
    rw [Nat.shiftLeft_eq, show C * 2 ^ 5 = 32 * C by ring, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    ring
  · have hi' := hi
    simp only [TScr, not_or, tA, tB, tC, tK, cTmp] at hi'
    simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by simp only [tN] at hN ⊢; omega), rd_set_ne (by simp only [tK]; omega),
      rd_set_ne (by simp only [tN] at hN ⊢; omega), rd_set_ne (by simp only [tK]; omega), e2' i hi hN]

/-! ## The tail words -/

theorem wf_cpWIR : ∀ (a n : ℕ), WF (cpWIR a n)
  | _, 0 => by simp [cpWIR, WF]
  | a, n + 1 => ⟨by simp +decide [WF, Prim.dst, tA, tB], wf_cpWIR (a + 1) n⟩

theorem wf_node1IR (bm x q : ℕ) : WF (node1IR bm x q) :=
  ⟨by simp +decide [WF, Prim.dst, tA, tB], by simp [WF], wf_cpWIR _ _⟩

/-- **One layer node**: if its bitmap cell is `0`, the 4 words of its half. -/
theorem node1IR_sem (I : Array Word) (bm x q : ℕ) (hb : regs ≤ bm + x) (hb2 : bm + x < 2 ^ 64) (hq : regs ≤ q)
    (hq2 : q + 8 < 2 ^ 64) (s : St) (hM : Lvm.X.Inv s.M) :
    (semXIR I (node1IR bm x q) s).o.toList = s.o.toList ++
      (if Lvm.X.rd s.M (bm + x) = 0 then (List.range 4).map (fun k => Lvm.X.rd s.M (q + 4 * (x % 2) + k)) else []) ∧
    (∀ y, y ≠ tA → y ≠ tB → Lvm.X.rd (semXIR I (node1IR bm x q) s).M y = Lvm.X.rd s.M y) := by
  have hs := hM.1
  simp only [regs] at hs hb hq
  have hA : tA ≠ bm + x := by simp only [tA]; omega
  have wf0 : WF (.seq (.blk [.const tA (toWord (bm + x))]) (.load tB tA)) := by simp +decide [WF, Prim.dst, tA, tB]
  have hM1 := inv_sem I wf0 hM
  have r1 : Lvm.X.rd (semXIR I (.seq (.blk [.const tA (toWord (bm + x))]) (.load tB tA)) s).M tB =
      Lvm.X.rd s.M (bm + x) := by
    simp (disch := ((try simp only [size_set, ne_eq]); (try simp only [tA, tB]); omega))
      [semXIR, runPrims, Prim.run, rd_set_self, rd_set_ne, toNat_toWord hb2, hA]
  have r2 : ∀ y, y ≠ tA → y ≠ tB →
      Lvm.X.rd (semXIR I (.seq (.blk [.const tA (toWord (bm + x))]) (.load tB tA)) s).M y = Lvm.X.rd s.M y :=
    fun y h1 h2 => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have o1 : (semXIR I (.seq (.blk [.const tA (toWord (bm + x))]) (.load tB tA)) s).o = s.o := rfl
  have e : semXIR I (node1IR bm x q) s = semXIR I (.ite tB (.blk []) (cpWIR (q + 4 * (x % 2)) 4))
      (semXIR I (.seq (.blk [.const tA (toWord (bm + x))]) (.load tB tA)) s) := rfl
  rw [e]
  generalize semXIR I (.seq (.blk [.const tA (toWord (bm + x))]) (.load tB tA)) s = s1 at hM1 r1 r2 o1
  rw [semXIR_ite, r1]
  have hx2 : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
  split_ifs with h0
  · obtain ⟨c1, c2⟩ := cpWIR_sem I 4 (q + 4 * (x % 2)) (by simp only [regs]; omega) (by omega) s1 hM1
    refine ⟨?_, fun y h1 h2 => by rw [c2 y h1 h2, r2 y h1 h2]⟩
    rw [c1, o1]
    congr 1
    exact List.map_congr_left fun k hk => by
      rw [r2 _ (by simp only [tA]; omega) (by simp only [tB]; omega)]
  · exact ⟨by simp [semXIR, runPrims, o1], fun y h1 h2 => by simp only [semXIR, runPrims, List.foldl]; exact r2 y h1 h2⟩

/-- **The uncovered nodes of a level** in the order of `xs`. -/
theorem nodesIR_sem (I : Array Word) (bm : ℕ) (heap : List ℕ) : ∀ (xs : List ℕ) (s : St), Lvm.X.Inv s.M →
    (∀ x ∈ xs, regs ≤ bm + x ∧ bm + x < 2 ^ 64 ∧ regs ≤ heap.getD (x / 2) 0 ∧ heap.getD (x / 2) 0 + 8 < 2 ^ 64) →
    (semXIR I (nodesIR bm heap xs) s).o.toList = s.o.toList ++ xs.flatMap (fun x =>
      if Lvm.X.rd s.M (bm + x) = 0 then
        (List.range 4).map (fun k => Lvm.X.rd s.M (heap.getD (x / 2) 0 + 4 * (x % 2) + k)) else []) ∧
    (∀ y, y ≠ tA → y ≠ tB → Lvm.X.rd (semXIR I (nodesIR bm heap xs) s).M y = Lvm.X.rd s.M y) ∧
    Lvm.X.Inv (semXIR I (nodesIR bm heap xs) s).M ∧ (semXIR I (nodesIR bm heap xs) s).M.size = s.M.size
  | [], s, hM, _ => ⟨by simp [nodesIR, semXIR, runPrims], fun _ _ _ => by simp [nodesIR, semXIR, runPrims], by
      simpa [nodesIR, semXIR, runPrims], by simp [nodesIR, semXIR, runPrims]⟩
  | x :: xs, s, hM, hx => by
    have h0 := hx x List.mem_cons_self
    obtain ⟨e1, e2⟩ := node1IR_sem I bm x (heap.getD (x / 2) 0) h0.1 h0.2.1 h0.2.2.1 h0.2.2.2 s hM
    have hM1 := inv_sem I (wf_node1IR bm x (heap.getD (x / 2) 0)) hM
    obtain ⟨ih1, ih2, ih3, ih4⟩ := nodesIR_sem I bm heap xs _ hM1 fun y hy => hx y (List.mem_cons_of_mem _ hy)
    have hk : ∀ y, regs ≤ y → Lvm.X.rd (semXIR I (node1IR bm x (heap.getD (x / 2) 0)) s).M y = Lvm.X.rd s.M y :=
      fun y hy => e2 y (by simp only [tA, regs] at hy ⊢; omega) (by simp only [tB, regs] at hy ⊢; omega)
    have e : semXIR I (nodesIR bm heap (x :: xs)) s =
        semXIR I (nodesIR bm heap xs) (semXIR I (node1IR bm x (heap.getD (x / 2) 0)) s) := rfl
    rw [e]
    refine ⟨?_, fun y h1 h2 => (ih2 y h1 h2).trans (e2 y h1 h2), ih3,
      ih4.trans (size_sem I (node1IR bm x (heap.getD (x / 2) 0)) s)⟩
    have hfl : (xs.flatMap fun y => if Lvm.X.rd (semXIR I (node1IR bm x (heap.getD (x / 2) 0)) s).M (bm + y) = 0 then
        (List.range 4).map (fun k => Lvm.X.rd (semXIR I (node1IR bm x (heap.getD (x / 2) 0)) s).M
          (heap.getD (y / 2) 0 + 4 * (y % 2) + k)) else []) =
        xs.flatMap fun y => if Lvm.X.rd s.M (bm + y) = 0 then
          (List.range 4).map (fun k => Lvm.X.rd s.M (heap.getD (y / 2) 0 + 4 * (y % 2) + k)) else [] :=
      List.flatMap_congr fun y hy => by
        have hy' := hx y (List.mem_cons_of_mem _ hy)
        rw [hk _ hy'.1, List.map_congr_left fun k hk' => hk _ (by simp at hk'; omega)]
    rw [ih1, e1, List.flatMap_cons, List.append_assoc, hfl]

/-- **The tail**: per level, the uncovered nodes in ascending `x`. -/
theorem tailIR_sem (I : Array Word) : ∀ (ls : List TLv) (s : St), Lvm.X.Inv s.M →
    (∀ l ∈ ls, ∀ x < 2 ^ l.m, regs ≤ l.bm + x ∧ l.bm + x < 2 ^ 64 ∧ regs ≤ l.heap.getD (x / 2) 0 ∧
      l.heap.getD (x / 2) 0 + 8 < 2 ^ 64) →
    (semXIR I (tailIR ls) s).o.toList = s.o.toList ++ ls.flatMap (fun l => (List.range (2 ^ l.m)).flatMap fun x =>
      if Lvm.X.rd s.M (l.bm + x) = 0 then
        (List.range 4).map (fun k => Lvm.X.rd s.M (l.heap.getD (x / 2) 0 + 4 * (x % 2) + k)) else []) ∧
    (∀ y, y ≠ tA → y ≠ tB → Lvm.X.rd (semXIR I (tailIR ls) s).M y = Lvm.X.rd s.M y) ∧
    Lvm.X.Inv (semXIR I (tailIR ls) s).M ∧ (semXIR I (tailIR ls) s).M.size = s.M.size
  | [], s, hM, _ => ⟨by simp [tailIR, semXIR, runPrims], fun _ _ _ => by simp [tailIR, semXIR, runPrims], by
      simpa [tailIR, semXIR, runPrims], by simp [tailIR, semXIR, runPrims]⟩
  | l :: ls, s, hM, hl => by
    obtain ⟨e1, e2, e3, e4⟩ := nodesIR_sem I l.bm l.heap (List.range (2 ^ l.m)) s hM fun x hx =>
      hl l List.mem_cons_self x (List.mem_range.1 hx)
    obtain ⟨ih1, ih2, ih3, ih4⟩ := tailIR_sem I ls _ e3 fun l' hl' => hl l' (List.mem_cons_of_mem _ hl')
    have hk : ∀ y, regs ≤ y → Lvm.X.rd (semXIR I (nodesIR l.bm l.heap (List.range (2 ^ l.m))) s).M y =
        Lvm.X.rd s.M y :=
      fun y hy => e2 y (by simp only [tA, regs] at hy ⊢; omega) (by simp only [tB, regs] at hy ⊢; omega)
    have e : semXIR I (tailIR (l :: ls)) s =
        semXIR I (tailIR ls) (semXIR I (nodesIR l.bm l.heap (List.range (2 ^ l.m))) s) := rfl
    rw [e]
    refine ⟨?_, fun y h1 h2 => (ih2 y h1 h2).trans (e2 y h1 h2), ih3, ih4.trans e4⟩
    have hfl : (ls.flatMap fun l' => (List.range (2 ^ l'.m)).flatMap fun x =>
        if Lvm.X.rd (semXIR I (nodesIR l.bm l.heap (List.range (2 ^ l.m))) s).M (l'.bm + x) = 0 then
          (List.range 4).map (fun k => Lvm.X.rd (semXIR I (nodesIR l.bm l.heap (List.range (2 ^ l.m))) s).M
            (l'.heap.getD (x / 2) 0 + 4 * (x % 2) + k)) else []) =
        ls.flatMap fun l' => (List.range (2 ^ l'.m)).flatMap fun x =>
          if Lvm.X.rd s.M (l'.bm + x) = 0 then
            (List.range 4).map (fun k => Lvm.X.rd s.M (l'.heap.getD (x / 2) 0 + 4 * (x % 2) + k)) else [] :=
      List.flatMap_congr fun l' hl' => List.flatMap_congr fun x hx => by
        have hx' := hl l' (List.mem_cons_of_mem _ hl') x (List.mem_range.1 hx)
        rw [hk _ hx'.1, List.map_congr_left fun k hk' => hk _ (by omega)]
    rw [ih1, e1, List.flatMap_cons, List.append_assoc, hfl]

end Lvm.XB
