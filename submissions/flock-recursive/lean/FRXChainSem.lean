-- New for `flock-recursive` (BLUEPRINT §6.2, §10 changes 14: the fold challenges; stage S-H2,
-- track L-ext).
import FRXChain

/-!
# The chain scan on the machine: the blocks of one word

The semantics of `wordIR`'s blocks, each on any state satisfying `Inv`, with the registers it
reads given as hypotheses: the length word (`lenIR_sem`), a query word (`qryIR_sem`, against the
expected word `exW`), an answer word (`ansPs_sem`), the record (`recIR_sem`) and the decision after
answer word 3 (`lastIR_sem`). Heap frames: every block but the record writes registers only
(`Lo`); the record writes `ansB + 4p + m` and `hB + m` only.
-/

namespace FR.X

open RecursionFast

attribute [local irreducible] entryK storeM runPrims

/-- The expected word `j` of the current target: header cell `hB + j` below `h`, else the tape
word `o + j − h`. -/
def exW (I : Array Word) (M : Mem) (h o j : ℕ) : Word :=
  if j < h then rd M (hB + j) else I.getD (o + j - h) 0

theorem toWord_sub_one (j : ℕ) (hj : j + 1 < 2 ^ 64) :
    XOp.sub.eval (toWord (j + 1)) 1 = toWord j := by
  have := sub_toWord (a := j + 1) (b := 1) hj (by omega)
  rwa [Nat.add_sub_cancel] at this

/-! ## The length word -/

theorem lo_lenIR : Lo lenIR := by
  simp +decide only [lenIR, ceil8Ps, Lo, Prim.dst, regs, rQw, rWd, rMt, rTl, rEo, rKc, rT2,
    List.cons_append, List.nil_append]

theorem wf_lenIR : WF lenIR := by
  simp +decide only [lenIR, ceil8Ps, WF, Prim.dst, rQw, rMt, rEo, rKc, rT2, List.cons_append,
    List.nil_append]

theorem lenIR_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I lenIR s).M rQw = ceil8 (rd s.M rWd) ∧
    rd (semXIR I lenIR s).M rMt = XOp.eq.eval (rd s.M rWd) (rd s.M rTl) ∧
    rd (semXIR I lenIR s).M rEo = 1 := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [lenIR, ceil8Ps, semXIR, runPrims, List.foldl, List.cons_append, List.nil_append, Prim.run, rKc, rT2, rQw, rWd, rMt, rTl, rEo]
  simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self,
    rd_set_ne]
  exact ⟨by simp only [ceil8, XOp.eval]; rfl, by trivial, by trivial⟩

/-! ## A query word -/

theorem lo_qryIR : Lo qryIR := by
  simp +decide only [qryIR, Lo, Prim.dst, regs, rKj, rZ, rKd, rAd4, rE, rMt, rEo, and_true]

theorem wf_qryIR : WF qryIR := by
  simp +decide only [qryIR, WF, Prim.dst, rKj, rZ, rKd, rAd4, rE, rMt, rEo, and_true]

theorem qryIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {j h o : ℕ} {b : Bool}
    (hj : j + 2 < 2 ^ 64) (hh : h ≤ 16) (ho : o + j < 2 ^ 64)
    (hE : rd s.M rEo = toWord (j + 1)) (hH : rd s.M rTh = toWord h) (hO : rd s.M rTo = toWord o)
    (hT : rd s.M rMt = bW b) :
    rd (semXIR I qryIR s).M rMt = bW (b && decide (rd s.M rWd = exW I s.M h o j)) ∧
    rd (semXIR I qryIR s).M rEo = toWord (j + 2) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have w1 : WF (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) := by
    simp +decide only [WF, Prim.dst, rKj, rZ]
  have hM1 := inv_sem I w1 hM
  have hk1 : rd (semXIR I (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) s).M rKj =
      toWord j := by
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [semXIR,
      runPrims, List.foldl, Prim.run, rd_set_self, rd_set_ne]
    rw [hE, h1, toWord_sub_one j (by omega)]
  have hz1 : rd (semXIR I (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) s).M rZ =
      bW (decide (j < h)) := by
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [semXIR,
      runPrims, List.foldl, Prim.run, rd_set_self, rd_set_ne]
    rw [hE, h1, toWord_sub_one j (by omega), hH, ltW_toWord (by omega) (by omega)]
  have fr1 : ∀ r, r < regs → r ≠ rKj → r ≠ rZ →
      rd (semXIR I (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) s).M r = rd s.M r :=
    fun r hr h1 h2 => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hp1 : ∀ x, regs ≤ x →
      rd (semXIR I (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) s).M x = rd s.M x :=
    fun x hx => hframe I _ s (by simp +decide only [Lo, Prim.dst, regs, rKj, rZ]) x hx
  rw [qryIR, semXIR_seq]
  generalize semXIR I (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh]) s = s1
    at hM1 hk1 hz1 fr1 hp1
  have hs1 := hM1.1
  simp only [regs] at hs1
  -- the expected word
  have hex : rd (semXIR I (.ite rZ (.seq (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj])
      (.load rE rAd4)) (.seq (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh])
      (.input rE rAd4))) s1).M rE = exW I s.M h o j := by
    rw [semXIR_ite, hz1, exW]
    by_cases hjh : j < h
    · rw [if_neg (by rw [decide_eq_true hjh]; decide), if_pos hjh, semXIR_seq]
      have ha : rd (semXIR I (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) s1).M rAd4 =
          toWord (hB + j) := by
        simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [semXIR,
          runPrims, List.foldl, Prim.run, rd_set_self, rd_set_ne]
        rw [hk1, add_toWord]
      have hp : rd (semXIR I (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) s1).M
          (hB + j) = rd s.M (hB + j) := by
        rw [hframe I _ s1 (by simp +decide only [Lo, Prim.dst, regs, rKd, rAd4]) _
            (by simp only [regs, hB_eq]; omega),
          hp1 _ (by simp only [regs, hB_eq]; omega)]
      have z2 := size_sem I (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) s1
      generalize semXIR I (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) s1 = s2
        at ha hp z2
      simp only [semXIR]
      rw [rd_set_self (by simp only [rE]; omega), ha, toNat_toWord (by simp only [hB_eq]; omega), hp]
    · rw [if_pos (by rw [decide_eq_false hjh]; decide), if_neg hjh, semXIR_seq]
      have ha : rd (semXIR I (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh]) s1).M rAd4 =
          toWord (o + j - h) := by
        simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [semXIR,
          runPrims, List.foldl, Prim.run, rd_set_self, rd_set_ne]
        rw [hk1, fr1 rTo (by decide) (by decide) (by decide), hO, add_toWord,
          fr1 rTh (by decide) (by decide) (by decide), hH, sub_toWord (by omega) (by omega)]
      have z2 := size_sem I (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh]) s1
      generalize semXIR I (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh]) s1 = s2 at ha z2
      simp only [semXIR]
      rw [rd_set_self (by simp only [rE]; omega), ha, toNat_toWord (by omega)]
  have fr2 : ∀ r, r < regs → r ≠ rKd → r ≠ rAd4 → r ≠ rE → rd (semXIR I (.ite rZ (.seq (.blk
      [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) (.load rE rAd4)) (.seq (.blk [.op .add rAd4
      rTo rKj, .op .sub rAd4 rAd4 rTh]) (.input rE rAd4))) s1).M r = rd s1.M r :=
    fun r hr a b c =>
      frame I _ s1 (by simp +decide only [WF, Prim.dst, rKd, rAd4, rE, and_true]) hM1 r hr (by
        simp [Writes, Prim.dst]; exact ⟨⟨⟨Ne.symm a, Ne.symm b⟩, c⟩, Ne.symm b, c⟩)
  have hM2 := inv_sem I (P := .ite rZ (.seq (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj])
    (.load rE rAd4)) (.seq (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh]) (.input rE rAd4)))
    (by simp +decide only [WF, Prim.dst, rKd, rAd4, rE, and_true]) hM1
  rw [semXIR_seq]
  generalize semXIR I (.ite rZ (.seq (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj])
    (.load rE rAd4)) (.seq (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh])
    (.input rE rAd4))) s1 = s2 at hex fr2 hM2
  have hs2 := hM2.1
  have h12 : rd s2.M cOne = 1 := hM2.2 0 (by decide)
  simp only [regs] at hs2
  have hw2 : rd s2.M rWd = rd s.M rWd := by
    rw [fr2 rWd (by decide) (by decide) (by decide) (by decide),
      fr1 rWd (by decide) (by decide) (by decide)]
  have hmt2 : rd s2.M rMt = bW b := by
    rw [fr2 rMt (by decide) (by decide) (by decide) (by decide),
      fr1 rMt (by decide) (by decide) (by decide), hT]
  have heo2 : rd s2.M rEo = toWord (j + 1) := by
    rw [fr2 rEo (by decide) (by decide) (by decide) (by decide),
      fr1 rEo (by decide) (by decide) (by decide), hE]
  simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [semXIR,
    runPrims, List.foldl, Prim.run, rd_set_self, rd_set_ne]
  rw [hw2, hex, hmt2, heo2, h12, eq_bW, bW_and, add_one_toWord]
  exact ⟨rfl, rfl⟩


/-! ## An answer word -/

/-- The branch-free selection of `setSPs`. -/
theorem maskSel (x w : Word) (b : Bool) :
    XOp.xor.eval x (XOp.and.eval (XOp.xor.eval x w) (XOp.sub.eval 0 (bW b))) = if b then w else x := by
  cases b
  · simp [XOp.eval, bW]
  · simp only [XOp.eval, bW, if_true]
    rw [show (0 : Word) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]

theorem setSPs_run (M : Mem) (hs : 256 ≤ M.size) {m r k : ℕ} (hr : r ∈ [rS0, rS1, rS2, rS3])
    (hm : m < 4) (hk : rd M rKj = toWord k) (hk2 : k < 2 ^ 64) :
    rd (runPrims (setSPs m r) M) r = (if k = m then rd M rWd else rd M r) ∧
    ∀ i, i ≠ rKd → i ≠ rMk5 → i ≠ r → rd (runPrims (setSPs m r) M) i = rd M i := by
  have hrr : r < 256 ∧ r ≠ rKd ∧ r ≠ rMk5 ∧ r ≠ rKj ∧ r ≠ rWd := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h1, h2, h3, h4, h5⟩ := hrr
  refine ⟨?_, fun i a b c => rd_runPrims_of_not_writes (by
    simp only [setSPs, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [Prim.dst] <;>
      first | exact Ne.symm a | exact Ne.symm b | exact Ne.symm c) _⟩
  simp only [setSPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | omega | (exact Nat.lt_of_lt_of_le (m := 256) h1 (by assumption)) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) h1 (by assumption)) | (exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption)) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne, Ne.symm h2, Ne.symm h3, h4, h5, Ne.symm h4, Ne.symm h5]
  rw [hk, eqW_toWord hk2 (by omega), maskSel]
  by_cases h : k = m <;> simp [h]

theorem lo_ansPs : Lo (.blk ansPs) := by
  simp +decide only [ansPs, setSPs, Lo, Prim.dst, regs, rKj, rKd, rMk5, rS0, rS1, rS2, rS3, rZ]

theorem wf_ansPs : WF (.blk ansPs) := by
  simp +decide only [ansPs, setSPs, WF, Prim.dst, rKj, rKd, rMk5, rS0, rS1, rS2, rS3, rZ]

/-- **An answer word** `m = eo − qw − 1`: `rS_m := w`, `rZ := [m = 3]`. -/
theorem ansPs_sem (I : Array Word) (s : St) (hM : Inv s.M) {qw m : ℕ} (hm : m < 4)
    (hq : 1 + qw + m < 2 ^ 64) (hE : rd s.M rEo = toWord (1 + qw + m))
    (hQ : rd s.M rQw = toWord qw) :
    (∀ i < 4, rd (semXIR I (.blk ansPs) s).M (rS0 + i) =
      if i = m then rd s.M rWd else rd s.M (rS0 + i)) ∧
    rd (semXIR I (.blk ansPs) s).M rZ = bW (decide (m = 3)) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have e : semXIR I (.blk ansPs) s = ⟨runPrims ([.const rKd 3, .op .eq rZ rKj rKd])
      (runPrims (setSPs 3 rS3) (runPrims (setSPs 2 rS2) (runPrims (setSPs 1 rS1)
      (runPrims (setSPs 0 rS0) (runPrims [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] s.M))))),
      s.o⟩ := by
    simp only [semXIR, ansPs, runPrims_append]
  rw [e]
  simp only
  -- the index `m`
  have hk0 : rd (runPrims [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] s.M) rKj = toWord m := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hE, hQ, h1, sub_toWord hq (by omega), show 1 + qw + m - qw = m + 1 by omega,
      toWord_sub_one m (by omega)]
  have hw0 : ∀ i, i ≠ rKj → rd (runPrims [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] s.M) i =
      rd s.M i := fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have z0 := size_runPrims [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] s.M
  generalize runPrims [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] s.M = M0 at hk0 hw0 z0
  have hs0 : 256 ≤ M0.size := by omega
  obtain ⟨a0, b0⟩ := setSPs_run M0 hs0 (m := 0) (r := rS0) (by simp) (by norm_num) hk0 (by omega)
  have z1 := size_runPrims (setSPs 0 rS0) M0
  generalize runPrims (setSPs 0 rS0) M0 = M1 at a0 b0 z1
  have hk1 : rd M1 rKj = toWord m := by rw [b0 _ (by decide) (by decide) (by decide), hk0]
  obtain ⟨a1, b1⟩ := setSPs_run M1 (by omega) (m := 1) (r := rS1) (by simp) (by norm_num) hk1 (by omega)
  have z2 := size_runPrims (setSPs 1 rS1) M1
  generalize runPrims (setSPs 1 rS1) M1 = M2 at a1 b1 z2
  have hk2 : rd M2 rKj = toWord m := by rw [b1 _ (by decide) (by decide) (by decide), hk1]
  obtain ⟨a2, b2⟩ := setSPs_run M2 (by omega) (m := 2) (r := rS2) (by simp) (by norm_num) hk2 (by omega)
  have z3 := size_runPrims (setSPs 2 rS2) M2
  generalize runPrims (setSPs 2 rS2) M2 = M3 at a2 b2 z3
  have hk3 : rd M3 rKj = toWord m := by rw [b2 _ (by decide) (by decide) (by decide), hk2]
  obtain ⟨a3, b3⟩ := setSPs_run M3 (by omega) (m := 3) (r := rS3) (by simp) (by norm_num) hk3 (by omega)
  have z4 := size_runPrims (setSPs 3 rS3) M3
  generalize runPrims (setSPs 3 rS3) M3 = M4 at a3 b3 z4
  have hk4 : rd M4 rKj = toWord m := by rw [b3 _ (by decide) (by decide) (by decide), hk3]
  have hs4 : 256 ≤ M4.size := by omega
  have hfin : ∀ i, i ≠ rKd → i ≠ rZ → rd (runPrims [.const rKd 3, .op .eq rZ rKj rKd] M4) i =
      rd M4 i := fun i a b => rd_runPrims_of_not_writes (by
        simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b⟩) _
  have hw : ∀ i, i ≠ rKj → rd M0 i = rd s.M i := hw0
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hfin _ (by simp only [rS0, rKd]; omega) (by simp only [rS0, rZ]; omega)]
    interval_cases i
    · rw [b3 _ (by decide) (by decide) (by decide), b2 _ (by decide) (by decide) (by decide),
        b1 _ (by decide) (by decide) (by decide), show rS0 + 0 = rS0 from rfl, a0,
        hw _ (by decide), hw _ (by decide)]
      by_cases h : m = 0 <;> simp [h, eq_comm]
    · rw [b3 _ (by decide) (by decide) (by decide), b2 _ (by decide) (by decide) (by decide),
        show rS0 + 1 = rS1 from rfl, a1, b0 _ (by decide) (by decide) (by decide),
        b0 _ (by decide) (by decide) (by decide), hw _ (by decide), hw _ (by decide)]
      by_cases h : m = 1 <;> simp [h, eq_comm]
    · rw [b3 _ (by decide) (by decide) (by decide), show rS0 + 2 = rS2 from rfl, a2,
        b1 _ (by decide) (by decide) (by decide), b0 _ (by decide) (by decide) (by decide),
        b1 _ (by decide) (by decide) (by decide), b0 _ (by decide) (by decide) (by decide),
        hw _ (by decide), hw _ (by decide)]
      by_cases h : m = 2 <;> simp [h, eq_comm]
    · rw [show rS0 + 3 = rS3 from rfl, a3, b2 _ (by decide) (by decide) (by decide),
        b1 _ (by decide) (by decide) (by decide), b0 _ (by decide) (by decide) (by decide),
        b2 _ (by decide) (by decide) (by decide), b1 _ (by decide) (by decide) (by decide),
        b0 _ (by decide) (by decide) (by decide), hw _ (by decide), hw _ (by decide)]
      by_cases h : m = 3 <;> simp [h, eq_comm]
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hk4]
    exact eqW_toWord (b := 3) (by omega) (by norm_num)

/-! ## Stores -/

theorem stNext_sem (I : Array Word) (s : St) (hM : Inv s.M) {a r : ℕ} (hr : r < regs)
    (hr4 : r ≠ cTmp) (hrA : r ≠ rAd4) (hA : rd s.M rAd4 = toWord a) (ha : regs ≤ a + 1)
    (ha2 : a + 1 < 2 ^ 64) (has : a + 1 < s.M.size) :
    rd (semXIR I (stNext r) s).M rAd4 = toWord (a + 1) ∧
    (∀ i, i ≠ cTmp → i ≠ rAd4 →
      rd (semXIR I (stNext r) s).M i = if i = a + 1 then rd s.M r else rd s.M i) ∧
    Inv (semXIR I (stNext r) s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs hr ha
  have hM1 := inv_sem I (P := .blk [.op .add rAd4 rAd4 cOne]) (by simp +decide only [WF, Prim.dst,
    rAd4]) hM
  have ha1 : rd (semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s).M rAd4 = toWord (a + 1) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hA, h1, add_one_toWord]
  have hf1 : ∀ i, i ≠ rAd4 → rd (semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s).M i = rd s.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have z1 := size_sem I (.blk [.op .add rAd4 rAd4 cOne]) s
  rw [stNext, semXIR_seq]
  generalize semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s = s1 at hM1 ha1 hf1 z1
  have e : semXIR I (.store rAd4 r) s1 = ⟨storeM s1.M rAd4 r, s1.o⟩ := rfl
  rw [e]
  refine ⟨?_, fun i hi hiA => ?_, inv_sem I (P := .store rAd4 r) (by simp +decide only [WF, rAd4,
    cTmp]) hM1⟩
  · rw [storeM_frame hM1 (by decide) (by decide) (by decide), ha1]
  · rw [rd_storeM hM1 ha1 ha ha2 (by omega) (by decide) hr4 hi, hf1 r hrA, hf1 i hiA]

/-- **Four stores** of `rS0 … rS3` at `b … b + 3`. -/
theorem st4IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {b : ℕ} (hA : rd s.M rAd4 = toWord b)
    (hb : regs ≤ b) (hb2 : b + 4 < 2 ^ 64) (hbs : b + 4 ≤ s.M.size) :
    rd (semXIR I st4IR s).M rAd4 = toWord (b + 3) ∧
    (∀ i, i ≠ cTmp → i ≠ rAd4 → rd (semXIR I st4IR s).M i =
      if b ≤ i ∧ i < b + 4 then rd s.M (rS0 + (i - b)) else rd s.M i) ∧
    Inv (semXIR I st4IR s).M := by
  have hs := hM.1
  simp only [regs] at hs hb
  have e0 : semXIR I (.store rAd4 rS0) s = ⟨storeM s.M rAd4 rS0, s.o⟩ := rfl
  have hM0 := inv_sem I (P := .store rAd4 rS0) (by simp +decide only [WF, rAd4, cTmp]) hM
  rw [e0] at hM0
  have a0 : rd (storeM s.M rAd4 rS0) rAd4 = toWord b := by
    rw [storeM_frame hM (by decide) (by decide) (by decide), hA]
  have f0 : ∀ i, i ≠ cTmp → rd (storeM s.M rAd4 rS0) i = if i = b then rd s.M rS0 else rd s.M i :=
    fun i hi => rd_storeM hM hA (by simp only [regs]; omega) (by omega) (by omega) (by decide)
      (by decide) hi
  rw [st4IR, semXIR_seq, e0, semXIR_seq]
  generalize hS0 : (⟨storeM s.M rAd4 rS0, s.o⟩ : St) = s0 at hM0
  have a0' : rd s0.M rAd4 = toWord b := by rw [← hS0]; exact a0
  have f0' : ∀ i, i ≠ cTmp → rd s0.M i = if i = b then rd s.M rS0 else rd s.M i := by
    rw [← hS0]; exact f0
  have z0 : s0.M.size = s.M.size := by rw [← hS0]; exact size_storeM ..
  obtain ⟨a1, f1, hM1⟩ := stNext_sem I s0 hM0 (r := rS1) (by decide) (by decide) (by decide) a0'
    (by simp only [regs]; omega) (by omega) (by omega)
  have z1 := size_sem I (stNext rS1) s0
  rw [semXIR_seq]
  generalize semXIR I (stNext rS1) s0 = s1 at a1 f1 hM1 z1
  obtain ⟨a2, f2, hM2⟩ := stNext_sem I s1 hM1 (r := rS2) (by decide) (by decide) (by decide) a1
    (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (stNext rS2) s1
  generalize semXIR I (stNext rS2) s1 = s2 at a2 f2 hM2 z2
  obtain ⟨a3, f3, hM3⟩ := stNext_sem I s2 hM2 (r := rS3) (by decide) (by decide) (by decide) a2
    (by simp only [regs]; omega) (by omega) (by omega)
  refine ⟨by rw [a3, show b + 1 + 1 + 1 = b + 3 by omega], fun i hi hiA => ?_, hM3⟩
  have r1 : rd s0.M rS1 = rd s.M rS1 := by rw [f0' _ (by decide), if_neg (by simp only [rS1]; omega)]
  have r2 : rd s1.M rS2 = rd s.M rS2 := by
    rw [f1 _ (by decide) (by decide), if_neg (by simp only [rS2]; omega), f0' _ (by decide),
      if_neg (by simp only [rS2]; omega)]
  have r3 : rd s2.M rS3 = rd s.M rS3 := by
    rw [f2 _ (by decide) (by decide), if_neg (by simp only [rS3]; omega), f1 _ (by decide) (by decide),
      if_neg (by simp only [rS3]; omega), f0' _ (by decide), if_neg (by simp only [rS3]; omega)]
  rw [f3 i hi hiA, f2 i hi hiA, f1 i hi hiA, f0' i hi, r1, r2, r3]
  split_ifs <;> first | omega | rfl |
    (rw [show rS0 + (i - b) = rS3 by simp only [rS0, rS3]; omega]) |
    (rw [show rS0 + (i - b) = rS2 by simp only [rS0, rS2]; omega]) |
    (rw [show rS0 + (i - b) = rS1 by simp only [rS0, rS1]; omega]) |
    (rw [show i - b = 0 by omega]; rfl)


/-! ## The record -/

theorem mulW_toWord (a b : ℕ) : XOp.mul.eval (toWord a) (toWord b) = toWord (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval, toWord, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod, Nat.mod_mod]

theorem load_sem (I : Array Word) (s : St) (hM : Inv s.M) {d a : ℕ} (hd : d < regs) :
    rd (semXIR I (.load d a) s).M d = rd s.M (rd s.M a).toNat ∧
    ∀ i, i ≠ d → rd (semXIR I (.load d a) s).M i = rd s.M i := by
  have hs := hM.1
  exact ⟨rd_set_self (by simp only [regs] at hs hd; omega), fun i hi => rd_set_ne (Ne.symm hi)⟩

theorem addOne_sem (I : Array Word) (s : St) (hM : Inv s.M) {a : ℕ}
    (hA : rd s.M rAd4 = toWord a) :
    rd (semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s).M rAd4 = toWord (a + 1) ∧
    ∀ i, i ≠ rAd4 → rd (semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s).M i = rd s.M i := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  refine ⟨?_, fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _⟩
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  rw [hA, h1, add_one_toWord]

theorem nextPs_frame (M : Mem) (i : ℕ) (a : i ≠ rPi) (b : i ≠ rKd) (c : i ≠ rAd4) :
    rd (runPrims nextPs M) i = rd M i := by
  apply rd_runPrims_of_not_writes
  simp only [nextPs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro q (rfl | rfl | rfl | rfl | rfl)
  · exact Ne.symm a
  · exact Ne.symm b
  · exact Ne.symm c
  · exact Ne.symm b
  · exact Ne.symm c

/-- **The next target**: `p + 1`, `tl`, `o` and the tag from the table, `h = 5`; the tag in
`H[0]`. -/
theorem nextIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {p : ℕ} (hp : p + 1 < 2 ^ 9)
    (hP : rd s.M rPi = toWord p) (hsz : ansB ≤ s.M.size) :
    rd (semXIR I nextIR s).M rPi = toWord (p + 1) ∧
    rd (semXIR I nextIR s).M rTl = rd s.M (chB + 4 * (p + 1)) ∧
    rd (semXIR I nextIR s).M rTo = rd s.M (chB + 4 * (p + 1) + 1) ∧
    rd (semXIR I nextIR s).M rTh = 5 ∧
    (∀ x, regs ≤ x → rd (semXIR I nextIR s).M x =
      if x = hB then rd s.M (chB + 4 * (p + 1) + 2) else rd s.M x) ∧
    (∀ i < regs, i ≠ cTmp → i ≠ rAd4 → i ≠ rKd → i ≠ rPi → i ≠ rTl → i ≠ rTo → i ≠ rTg →
      i ≠ rTh → rd (semXIR I nextIR s).M i = rd s.M i) ∧
    Inv (semXIR I nextIR s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have hc : chB + 4 * (p + 1) + 3 < hB := by simp only [chB_eq, hB_eq]; omega
  have hcs : hB + 16 ≤ s.M.size := by simp only [hB_eq, ansB_eq] at hsz ⊢; omega
  have e0 : semXIR I nextPre s = ⟨runPrims nextPs s.M, s.o⟩ := rfl
  have w0 : WF nextPre := by simp +decide only [nextPre, nextPs, WF, Prim.dst, rPi, rKd, rAd4]
  have hM0 := inv_sem I w0 hM
  have a0 : rd (semXIR I nextPre s).M rAd4 = toWord (chB + 4 * (p + 1)) ∧
      rd (semXIR I nextPre s).M rPi = toWord (p + 1) := by
    rw [e0]
    simp only [nextPs, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hP, h1, add_one_toWord]
    refine ⟨?_, rfl⟩
    rw [show (4 : Word) = toWord 4 from rfl, mulW_toWord, add_toWord]
    congr 1
    ring
  have f0 : ∀ i, i ≠ rPi → i ≠ rKd → i ≠ rAd4 → rd (semXIR I nextPre s).M i = rd s.M i :=
    fun i a b c => by simp only [e0]; exact nextPs_frame s.M i a b c
  have z0 := size_sem I nextPre s
  rw [nextIR, semXIR_seq]
  generalize semXIR I nextPre s = s0 at hM0 a0 f0 z0
  obtain ⟨a0, p0⟩ := a0
  -- three loads
  obtain ⟨l1, g1⟩ := load_sem I s0 hM0 (d := rTl) (a := rAd4) (by decide)
  have hM1 := inv_sem I (P := .load rTl rAd4) (by simp +decide only [WF, rTl]) hM0
  have z1 := size_sem I (.load rTl rAd4) s0
  rw [semXIR_seq]
  generalize semXIR I (.load rTl rAd4) s0 = s1 at l1 g1 hM1 z1
  obtain ⟨n1, k1⟩ := addOne_sem I s1 hM1 (a := chB + 4 * (p + 1)) (by rw [g1 _ (by decide), a0])
  have hM2 := inv_sem I (P := .blk [.op .add rAd4 rAd4 cOne]) (by simp +decide only [WF, Prim.dst,
    rAd4]) hM1
  have z2 := size_sem I (.blk [.op .add rAd4 rAd4 cOne]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s1 = s2 at n1 k1 hM2 z2
  obtain ⟨l2, g2⟩ := load_sem I s2 hM2 (d := rTo) (a := rAd4) (by decide)
  have hM3 := inv_sem I (P := .load rTo rAd4) (by simp +decide only [WF, rTo]) hM2
  have z3 := size_sem I (.load rTo rAd4) s2
  rw [semXIR_seq]
  generalize semXIR I (.load rTo rAd4) s2 = s3 at l2 g2 hM3 z3
  obtain ⟨n2, k2⟩ := addOne_sem I s3 hM3 (a := chB + 4 * (p + 1) + 1) (by rw [g2 _ (by decide), n1])
  have hM4 := inv_sem I (P := .blk [.op .add rAd4 rAd4 cOne]) (by simp +decide only [WF, Prim.dst,
    rAd4]) hM3
  have z4 := size_sem I (.blk [.op .add rAd4 rAd4 cOne]) s3
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .add rAd4 rAd4 cOne]) s3 = s4 at n2 k2 hM4 z4
  obtain ⟨l3, g3⟩ := load_sem I s4 hM4 (d := rTg) (a := rAd4) (by decide)
  have hM5 := inv_sem I (P := .load rTg rAd4) (by simp +decide only [WF, rTg]) hM4
  have z5 := size_sem I (.load rTg rAd4) s4
  rw [semXIR_seq]
  generalize semXIR I (.load rTg rAd4) s4 = s5 at l3 g3 hM5 z5
  -- the heap is unchanged up to here
  have hh4 : ∀ x, regs ≤ x → rd s4.M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    rw [k2 x (by simp only [rAd4]; omega),
      g2 x (by simp only [rTo]; omega), k1 x (by simp only [rAd4]; omega),
      g1 x (by simp only [rTl]; omega), f0 x (by simp only [rPi]; omega) (by simp only [rKd]; omega)
      (by simp only [rAd4]; omega)]
  have hh5 : ∀ x, regs ≤ x → rd s5.M x = rd s.M x := fun x hx => by
    rw [g3 x (by simp only [regs] at hx; simp only [rTg]; omega), hh4 x hx]
  have hr5 : ∀ i < regs, i ≠ rAd4 → i ≠ rKd → i ≠ rPi → i ≠ rTl → i ≠ rTo → i ≠ rTg →
      rd s5.M i = rd s.M i := fun i _ a b c d e f => by
    rw [g3 i f, k2 i a, g2 i e, k1 i a, g1 i d, f0 i c b a]
  have vTl : rd s5.M rTl = rd s.M (chB + 4 * (p + 1)) := by
    rw [g3 _ (by decide), k2 _ (by decide), g2 _ (by decide), k1 _ (by decide), l1, a0,
      toNat_toWord (by simp only [chB_eq]; omega), f0 _ (by simp only [chB_eq, rPi]; omega)
      (by simp only [chB_eq, rKd]; omega) (by simp only [chB_eq, rAd4]; omega)]
  have vTo : rd s5.M rTo = rd s.M (chB + 4 * (p + 1) + 1) := by
    rw [g3 _ (by decide), k2 _ (by decide), l2, n1, toNat_toWord (by simp only [chB_eq]; omega),
      k1 _ (by simp only [chB_eq, rAd4]; omega), g1 _ (by simp only [chB_eq, rTl]; omega),
      f0 _ (by simp only [chB_eq, rPi]; omega) (by simp only [chB_eq, rKd]; omega)
      (by simp only [chB_eq, rAd4]; omega)]
  have vTg : rd s5.M rTg = rd s.M (chB + 4 * (p + 1) + 2) := by
    rw [l3, n2, toNat_toWord (by simp only [chB_eq]; omega), show chB + 4 * (p + 1) + 1 + 1 =
      chB + 4 * (p + 1) + 2 by omega, hh4 _ (by simp only [chB_eq, regs]; omega)]
  have vPi : rd s5.M rPi = toWord (p + 1) := by
    rw [g3 _ (by decide), k2 _ (by decide), g2 _ (by decide), k1 _ (by decide), g1 _ (by decide), p0]
  -- `h := 5`, then the tag's store
  have hM6 := inv_sem I (P := .blk [.const rTh 5]) (by simp +decide only [WF, Prim.dst, rTh]) hM5
  have t6 : rd (semXIR I (.blk [.const rTh 5]) s5).M rTh = 5 := by
    have := hM5.1; simp only [regs] at this
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rTh]; omega)
  have f6 : ∀ i, i ≠ rTh → rd (semXIR I (.blk [.const rTh 5]) s5).M i = rd s5.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have z6 := size_sem I (.blk [.const rTh 5]) s5
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const rTh 5]) s5 = s6 at hM6 t6 f6 z6
  have hM7 := inv_sem I (P := .blk [.const rAd4 (toWord hB)]) (by simp +decide only [WF, Prim.dst,
    rAd4]) hM6
  have a7 : rd (semXIR I (.blk [.const rAd4 (toWord hB)]) s6).M rAd4 = toWord hB := by
    have := hM6.1; simp only [regs] at this
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rAd4]; omega)
  have f7 : ∀ i, i ≠ rAd4 → rd (semXIR I (.blk [.const rAd4 (toWord hB)]) s6).M i = rd s6.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have z7 := size_sem I (.blk [.const rAd4 (toWord hB)]) s6
  rw [stAt, semXIR_seq]
  generalize semXIR I (.blk [.const rAd4 (toWord hB)]) s6 = s7 at hM7 a7 f7 z7
  have e8 : semXIR I (.store rAd4 rTg) s7 = ⟨storeM s7.M rAd4 rTg, s7.o⟩ := rfl
  rw [e8]
  have st8 : ∀ i, i ≠ cTmp → rd (storeM s7.M rAd4 rTg) i = if i = hB then rd s7.M rTg else rd s7.M i :=
    fun i hi => rd_storeM hM7 a7 (by simp only [hB_eq, regs]; omega) (by simp only [hB_eq]; omega)
      (by omega) (by decide) (by decide) hi
  have r7 : ∀ i, i ≠ rAd4 → i ≠ rTh → rd s7.M i = rd s5.M i := fun i a b => by rw [f7 i a, f6 i b]
  refine ⟨?_, ?_, ?_, ?_, fun x hx => ?_, fun i hi c a k x1 x2 x3 x4 x5 => ?_,
    inv_sem I (P := .store rAd4 rTg) (by simp +decide only [WF, rAd4, cTmp]) hM7⟩
  · rw [st8 _ (by decide), if_neg (by simp only [rPi, hB_eq]; omega), r7 _ (by decide) (by decide), vPi]
  · rw [st8 _ (by decide), if_neg (by simp only [rTl, hB_eq]; omega), r7 _ (by decide) (by decide), vTl]
  · rw [st8 _ (by decide), if_neg (by simp only [rTo, hB_eq]; omega), r7 _ (by decide) (by decide), vTo]
  · rw [st8 _ (by decide), if_neg (by simp only [rTh, hB_eq]; omega), f7 _ (by decide), t6]
  · simp only [regs] at hx
    rw [st8 _ (by simp only [cTmp]; omega), r7 _ (by decide) (by decide), vTg,
      r7 _ (by simp only [rAd4]; omega) (by simp only [rTh]; omega), hh5 x (by simp only [regs]; omega)]
  · simp only [regs] at hi
    rw [st8 _ c, if_neg (by simp only [hB_eq]; omega), r7 _ a x5, hr5 i (by simp only [regs]; omega)
      a k x1 x2 x3 x4]


theorem recPs_frame (M : Mem) (i : ℕ) (b : i ≠ rKd) (c : i ≠ rAd4) :
    rd (runPrims recPs M) i = rd M i := by
  apply rd_runPrims_of_not_writes
  simp only [recPs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro q (rfl | rfl | rfl | rfl)
  · exact Ne.symm b
  · exact Ne.symm c
  · exact Ne.symm b
  · exact Ne.symm c

/-- **The record**: the answer registers at `ansB + 4p … + 3` and at `hB + 1 … hB + 4`, the next
target's tag at `hB`; `p + 1`, `tl`, `o` from the table, `h = 5`. -/
theorem recIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {p : ℕ} (hp : p + 1 < 2 ^ 9)
    (hP : rd s.M rPi = toWord p) (hsz : chEnd ≤ s.M.size) :
    rd (semXIR I recIR s).M rPi = toWord (p + 1) ∧
    rd (semXIR I recIR s).M rTl = rd s.M (chB + 4 * (p + 1)) ∧
    rd (semXIR I recIR s).M rTo = rd s.M (chB + 4 * (p + 1) + 1) ∧
    rd (semXIR I recIR s).M rTh = 5 ∧
    (∀ x, regs ≤ x → rd (semXIR I recIR s).M x =
      if ansB + 4 * p ≤ x ∧ x < ansB + 4 * p + 4 then rd s.M (rS0 + (x - (ansB + 4 * p)))
      else if hB + 1 ≤ x ∧ x < hB + 5 then rd s.M (rS0 + (x - (hB + 1)))
      else if x = hB then rd s.M (chB + 4 * (p + 1) + 2) else rd s.M x) ∧
    (∀ i < regs, i ≠ cTmp → i ≠ rAd4 → i ≠ rKd → i ≠ rPi → i ≠ rTl → i ≠ rTo → i ≠ rTg →
      i ≠ rTh → rd (semXIR I recIR s).M i = rd s.M i) ∧
    Inv (semXIR I recIR s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have q1 : regs ≤ ansB + 4 * p := by rw [ansB_eq]; simp only [regs]; omega
  have q2 : ansB + 4 * p + 4 < 2 ^ 64 := by rw [ansB_eq]; omega
  have q3 : ansB + 4 * p + 4 ≤ s.M.size := by rw [ansB_eq]; simp only [chEnd] at hsz; omega
  have q4 : regs ≤ hB + 1 := by rw [hB_eq]; simp only [regs]; omega
  have q5 : hB + 1 + 4 < 2 ^ 64 := by rw [hB_eq]; omega
  have q6 : hB + 1 + 4 ≤ s.M.size := by rw [hB_eq]; simp only [chEnd] at hsz; omega
  have q7 : ∀ k < 3, regs ≤ chB + 4 * (p + 1) + k := fun k _ => by rw [chB_eq]; simp only [regs]; omega
  have e0 : semXIR I recPre s = ⟨runPrims recPs s.M, s.o⟩ := rfl
  have hM0 :=
    inv_sem I (P := recPre) (by simp +decide only [recPre, recPs, WF, Prim.dst, rKd, rAd4]) hM
  have a0 : rd (semXIR I recPre s).M rAd4 = toWord (ansB + 4 * p) := by
    simp only [e0, recPs, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hP, show (4 : Word) = toWord 4 from rfl, mulW_toWord, add_toWord]
    congr 1
    ring
  have f0 : ∀ i, i ≠ rKd → i ≠ rAd4 → rd (semXIR I recPre s).M i = rd s.M i :=
    fun i b c => by simp only [e0]; exact recPs_frame s.M i b c
  have z0 := size_sem I recPre s
  rw [recIR, semXIR_seq]
  generalize semXIR I recPre s = s0 at hM0 a0 f0 z0
  -- the answer at `ansB + 4p`
  obtain ⟨a1, f1, hM1⟩ := st4IR_sem I s0 hM0 (b := ansB + 4 * p) a0 q1 q2
    (by rw [z0]; exact q3)
  have z1 := size_sem I st4IR s0
  rw [semXIR_seq]
  generalize semXIR I st4IR s0 = s1 at a1 f1 hM1 z1
  -- `rAd4 := hB + 1`
  have hM2 := inv_sem I (P := .blk [.const rAd4 (toWord (hB + 1))]) (by simp +decide only [WF,
    Prim.dst, rAd4])
    hM1
  have a2 : rd (semXIR I (.blk [.const rAd4 (toWord (hB + 1))]) s1).M rAd4 = toWord (hB + 1) := by
    have := hM1.1; simp only [regs] at this
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rAd4]; omega)
  have f2 : ∀ i, i ≠ rAd4 → rd (semXIR I (.blk [.const rAd4 (toWord (hB + 1))]) s1).M i =
      rd s1.M i := fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have z2 := size_sem I (.blk [.const rAd4 (toWord (hB + 1))]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const rAd4 (toWord (hB + 1))]) s1 = s2 at hM2 a2 f2 z2
  -- the answer at `hB + 1`
  obtain ⟨a3, f3, hM3⟩ := st4IR_sem I s2 hM2 (b := hB + 1) a2 q4 q5
    (by rw [z2, z1, z0]; exact q6)
  have z3 := size_sem I st4IR s2
  rw [semXIR_seq]
  generalize semXIR I st4IR s2 = s3 at a3 f3 hM3 z3
  -- registers kept so far
  have r3 : ∀ i < regs, i ≠ cTmp → i ≠ rAd4 → i ≠ rKd → rd s3.M i = rd s.M i := fun i hi c a k => by
    simp only [regs] at hi
    rw [f3 i c a, if_neg (by simp only [hB_eq]; omega), f2 i a, f1 i c a,
      if_neg (by simp only [ansB_eq]; omega), f0 i k a]
  have hS : ∀ j < 4, rd s2.M (rS0 + j) = rd s.M (rS0 + j) := fun j hj => by
    rw [f2 _ (by simp only [rS0, rAd4]; omega), f1 _ (by simp only [rS0, cTmp]; omega)
      (by simp only [rS0, rAd4]; omega), if_neg (by simp only [rS0, ansB_eq]; omega),
      f0 _ (by simp only [rS0, rKd]; omega) (by simp only [rS0, rAd4]; omega)]
  have h3 : ∀ x, regs ≤ x → rd s3.M x =
      if ansB + 4 * p ≤ x ∧ x < ansB + 4 * p + 4 then rd s.M (rS0 + (x - (ansB + 4 * p)))
      else if hB + 1 ≤ x ∧ x < hB + 5 then rd s.M (rS0 + (x - (hB + 1))) else rd s.M x :=
    fun x hx => by
      simp only [regs] at hx
      rw [f3 x (by simp only [cTmp]; omega) (by simp only [rAd4]; omega),
        f2 x (by simp only [rAd4]; omega), f1 x (by simp only [cTmp]; omega)
        (by simp only [rAd4]; omega)]
      by_cases hA : ansB + 4 * p ≤ x ∧ x < ansB + 4 * p + 4
      · rw [if_neg (by simp only [hB_eq, ansB_eq] at hA ⊢; omega), if_pos hA, if_pos hA,
          f0 _ (by simp only [rS0, rKd]; omega) (by simp only [rS0, rAd4]; omega)]
      · rw [if_neg hA, if_neg hA]
        by_cases hH : hB + 1 ≤ x ∧ x < hB + 5
        · rw [if_pos (by omega), if_pos hH, hS _ (by omega)]
        · rw [if_neg (by omega), if_neg hH, f0 x (by simp only [rKd]; omega)
            (by simp only [rAd4]; omega)]
  have hP3 : rd s3.M rPi = toWord p := by
    rw [r3 _ (by decide) (by decide) (by decide) (by decide), hP]
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := nextIR_sem I s3 hM3 hp hP3 (by
    simp only [ansB_eq, chEnd] at hsz ⊢; omega)
  have hT : ∀ k < 3, rd s3.M (chB + 4 * (p + 1) + k) = rd s.M (chB + 4 * (p + 1) + k) :=
    fun k hk => by
      have hx : regs ≤ chB + 4 * (p + 1) + k := q7 k hk
      have h1 : ¬ (ansB + 4 * p ≤ chB + 4 * (p + 1) + k ∧ chB + 4 * (p + 1) + k < ansB + 4 * p + 4) :=
        by simp only [chB_eq, ansB_eq]; omega
      have h2 : ¬ (hB + 1 ≤ chB + 4 * (p + 1) + k ∧ chB + 4 * (p + 1) + k < hB + 5) := by
        simp only [chB_eq, hB_eq]; omega
      rw [h3 _ hx, if_neg h1, if_neg h2]
  refine ⟨n1, ?_, ?_, n4, fun x hx => ?_, fun i hi c a k x1 x2 x3 x4 x5 => ?_, n7⟩
  · rw [n2]; exact hT 0 (by norm_num)
  · rw [n3, hT 1 (by norm_num)]
  · rw [n5 x hx]
    by_cases hx0 : x = hB
    · rw [if_pos hx0, if_neg (by simp only [hB_eq, ansB_eq] at hx0 ⊢; omega),
        if_neg (by omega), if_pos hx0, hT 2 (by norm_num)]
    · rw [if_neg hx0, h3 x hx, if_neg hx0]
  · rw [n6 i hi c a k x1 x2 x3 x4 x5, r3 i hi c a k]


/-! ## After answer word 3 -/

/-- The test before the record: `rZ := [p < N] ∧ rMt`. -/
def lastPs (N : ℕ) : List Prim := [.const rKd (toWord N), .op .ltu rZ rPi rKd, .op .and rZ rZ rMt]

theorem lastIR_eq (N : ℕ) : lastIR N =
    .seq (.blk (lastPs N)) (.seq (.ite rZ recIR (.blk [])) (.blk [.const rEo 0])) := rfl

/-- **The decision after answer word 3**: the test block leaves a state `s₁` equal to `s` but for
`rKd` and `rZ`; then the record runs on `s₁` iff `p < N` and the flag is set; then `eo := 0`. -/
theorem lastIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N p : ℕ} {b : Bool}
    (hN : N < 2 ^ 64) (hp : p < 2 ^ 64) (hP : rd s.M rPi = toWord p) (hT : rd s.M rMt = bW b) :
    ∃ s₁ : St, Inv s₁.M ∧ s₁.M.size = s.M.size ∧
      (∀ i, i ≠ rKd → i ≠ rZ → rd s₁.M i = rd s.M i) ∧
      semXIR I (lastIR N) s = semXIR I (.blk [.const rEo 0])
        (if p < N ∧ b = true then semXIR I recIR s₁ else s₁) := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨semXIR I (.blk (lastPs N)) s, inv_sem I (by simp +decide only [lastPs, WF, Prim.dst, rKd,
    rZ, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]) hM,
    size_sem .., fun i a b => rd_runPrims_of_not_writes (by
      simp only [lastPs, List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl | rfl)
      · exact Ne.symm a
      · exact Ne.symm b
      · exact Ne.symm b) _, ?_⟩
  have hz : rd (semXIR I (.blk (lastPs N)) s).M rZ = bW (decide (p < N) && b) := by
    simp only [semXIR, lastPs, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hP, ltW_toWord hp hN, hT, bW_and]
  rw [lastIR_eq, semXIR_seq, semXIR_seq, semXIR_ite, hz]
  by_cases h : p < N ∧ b = true
  · rw [if_pos h, if_neg (by rw [decide_eq_true h.1, h.2]; decide)]
  · rw [if_neg h, if_pos (by
      by_cases h1 : p < N
      · have : b = false := by simpa [h1] using h
        rw [this]; simp; rfl
      · rw [decide_eq_false h1]; rfl)]
    with_unfolding_all rfl

end FR.X
