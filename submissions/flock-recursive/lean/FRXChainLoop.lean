-- New for `flock-recursive` (BLUEPRINT §6.2, §10 changes 14: the fold challenges; stage S-H2,
-- track L-ext).
import FRXChainSem

/-!
# The chain scan on the machine: the loop

* `Stat`: what the loop keeps between entries and inside one: the target index `p` and the
  answers found (`ansB + 4q`), the current target's length and words (`exW`), the heap outside
  `H` and the answers.
* `TabOK`: the table and the tape realise the targets `T p st` for `0 < p < N` (tag word, the
  previous answer, then tape words).
* The four cases of one word (`word_len`, `word_qry`, `word_ans`, `word_last`), then one entry
  (`entry_sem`: `qWords e` iterations do `scanStep`), then the log (`scan_sem`).
-/

namespace FR.X

open RecursionFast

/-! ## The invariant -/

/-- **What the loop keeps**: `p` and the answers found; the current target (when `p < N`):
its length in `rTl`, its words `exW` (header `h ≤ 16`, tape offset `o < 2^62`); the heap outside
`H` and the answers is the loop's initial heap `M₀`. -/
structure Stat (I : Array Word) (T : ℕ → Digest → ByteArray) (N : ℕ) (M₀ : Mem) (x : SS)
    (s : St) : Prop where
  inv : Inv s.M
  size : chEnd ≤ s.M.size
  pi : rd s.M rPi = toWord x.1
  pN : x.1 ≤ N
  len : x.2.2.length = x.1
  th : (rd s.M rTh).toNat ≤ 16
  tof : (rd s.M rTo).toNat < 2 ^ 62
  tg : x.1 < N → rd s.M rTl = toWord (T x.1 x.2.1).size ∧ (T x.1 x.2.1).size < 2 ^ 64 ∧
    ∀ j < ((T x.1 x.2.1).size + 7) / 8, (packBytes (T x.1 x.2.1).data.toList).getD j 0 =
      exW I s.M (rd s.M rTh).toNat (rd s.M rTo).toNat j
  ans : ∀ q < x.1, ∀ m < 4,
    rd s.M (ansB + 4 * q + m) = (packBytes (x.2.2.getD q default).toList).getD m 0
  heap : ∀ y, regs ≤ y → (y < hB ∨ hB + 16 ≤ y) → (y < ansB ∨ chEnd ≤ y) → rd s.M y = rd M₀ y

/-- **The table realises the targets** `T p st` for `0 < p < N`: the length at `chB + 4p`, the
tape offset at `chB + 4p + 1`, and the words: the tag at `chB + 4p + 2`, the state, then the tape
from the offset. Entry `N` has an offset below `2^62` too (it is loaded after the last record). -/
def TabOK (I : Array Word) (T : ℕ → Digest → ByteArray) (N : ℕ) (M₀ : Mem) : Prop :=
  ∀ p, 0 < p → p ≤ N → (rd M₀ (chB + 4 * p + 1)).toNat < 2 ^ 62 ∧ (p < N → ∀ st : Digest,
    rd M₀ (chB + 4 * p) = toWord (T p st).size ∧ (T p st).size < 2 ^ 64 ∧
    ∀ j < ((T p st).size + 7) / 8, (packBytes (T p st).data.toList).getD j 0 =
      if j < 5 then (if j = 0 then rd M₀ (chB + 4 * p + 2) else (packBytes st.toList).getD (j - 1) 0)
      else I.getD ((rd M₀ (chB + 4 * p + 1)).toNat + (j - 5)) 0)

theorem exW_congr {I : Array Word} {M M' : Mem} (h : ∀ y, regs ≤ y → rd M' y = rd M y)
    (hh o j : ℕ) : exW I M' hh o j = exW I M hh o j := by
  unfold exW; split_ifs
  · exact h _ (by simp only [hB_eq, regs]; omega)
  · rfl

/-- `Stat` survives code that keeps `rPi, rTl, rTh, rTo` and the heap. -/
theorem Stat.frame {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s s' : St} (h : Stat I T N M₀ x s) (hM : Inv s'.M) (hsz : s'.M.size = s.M.size)
    (hr : ∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo) → rd s'.M r = rd s.M r)
    (hh : ∀ y, regs ≤ y → rd s'.M y = rd s.M y) : Stat I T N M₀ x s' where
  inv := hM
  size := hsz ▸ h.size
  pi := (hr _ (.inl rfl)).trans h.pi
  pN := h.pN
  len := h.len
  th := (hr rTh (.inr (.inr (.inl rfl)))).symm ▸ h.th
  tof := (hr rTo (.inr (.inr (.inr rfl)))).symm ▸ h.tof
  tg := fun hp => by
    obtain ⟨a, b, c⟩ := h.tg hp
    refine ⟨(hr _ (.inr (.inl rfl))).trans a, b, fun j hj => ?_⟩
    rw [c j hj, hr rTh (.inr (.inr (.inl rfl))), hr rTo (.inr (.inr (.inr rfl))), exW_congr hh]
  ans := fun q hq m hm => (hh _ (by simp only [ansB_eq, regs]; omega)).trans (h.ans q hq m hm)
  heap := fun y hy h1 h2 => (hh y hy).trans (h.heap y hy h1 h2)

/-- Code that keeps `rPi, rTl, rTh, rTo` and the heap. -/
def Keep (s s' : St) : Prop :=
  (∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo) → rd s'.M r = rd s.M r) ∧
    ∀ y, regs ≤ y → rd s'.M y = rd s.M y

/-! ## The pieces of one word -/

/-- The test of the length word. -/
def w2Ps : List Prim := [.const rKd 0, .op .eq rZ rEo rKd]

/-- The query or answer word. -/
def restIR (N : ℕ) : XIR := .seq (.blk [.op .ltu rZ rQw rEo]) (.ite rZ (ansIR N) qryIR)

/-- The next word. -/
def incPs : List Prim := [.op .add rWp rWp cOne]

theorem wordIR_eq (N : ℕ) : wordIR N =
    .seq (.input rWd rWp) (.seq (.blk w2Ps) (.seq (.ite rZ lenIR (restIR N)) (.blk incPs))) := rfl

theorem pre_sem (I : Array Word) (s : St) (hM : Inv s.M) {pos : ℕ} (hW : rd s.M rWp = toWord pos)
    (hpos : pos < 2 ^ 64) :
    rd (semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s)).M rWd = I.getD pos 0 ∧
    rd (semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s)).M rZ =
      bW (decide (rd s.M rEo = 0)) ∧
    (∀ i, i ≠ rWd → i ≠ rKd → i ≠ rZ →
      rd (semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s)).M i = rd s.M i) ∧
    Inv (semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s)).M := by
  have hs := hM.1
  simp only [regs] at hs
  have hM1 := inv_sem I (P := .input rWd rWp) (by simp +decide only [WF, rWd]) hM
  have i1 : rd (semXIR I (.input rWd rWp) s).M rWd = I.getD pos 0 := by
    simp only [semXIR]
    rw [rd_set_self (by simp only [rWd]; omega), hW, toNat_toWord hpos]
  have f1 : ∀ i, i ≠ rWd → rd (semXIR I (.input rWd rWp) s).M i = rd s.M i :=
    fun i hi => rd_set_ne (Ne.symm hi)
  generalize semXIR I (.input rWd rWp) s = s1 at hM1 i1 f1
  have hs1 := hM1.1
  simp only [regs] at hs1
  have e : semXIR I (.blk w2Ps) s1 = ⟨runPrims w2Ps s1.M, s1.o⟩ := rfl
  refine ⟨?_, ?_, fun i a b c => ?_,
    inv_sem I (by simp +decide only [w2Ps, WF, Prim.dst, rKd, rZ]) hM1⟩
  · simp only [e]
    rw [rd_runPrims_of_not_writes (by simp [w2Ps, Prim.dst, rKd, rZ, rWd]) _]; exact i1
  · rw [e]
    simp only [w2Ps, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, rZ]; omega), rd_set_self (by simp only [rKd]; omega),
      rd_set_ne (by decide), f1 _ (by decide), eq_bW]
  · simp only [e]
    rw [rd_runPrims_of_not_writes (by
      simp only [w2Ps, List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm b
      · exact Ne.symm c) _, f1 i a]

theorem inc_sem (I : Array Word) (s : St) (hM : Inv s.M) {pos : ℕ} (hW : rd s.M rWp = toWord pos) :
    rd (semXIR I (.blk incPs) s).M rWp = toWord (pos + 1) ∧
    (∀ i, i ≠ rWp → rd (semXIR I (.blk incPs) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk incPs) s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  refine ⟨?_, fun i hi => rd_runPrims_of_not_writes (by simp [incPs, Prim.dst]; exact Ne.symm hi) _,
    inv_sem I (by simp +decide only [incPs, WF, Prim.dst, rWp]) hM⟩
  simp only [semXIR, incPs, runPrims, List.foldl, Prim.run]
  rw [rd_set_self (by simp only [rWp]; omega), hW, h1, add_one_toWord]

/-- The heap is kept by every block of a word but the record. -/
theorem lo_restQ : Lo qryIR := lo_qryIR


theorem toWord_toNat (w : Word) : toWord w.toNat = w := by simp [toWord]

/-- The common head of a word: the word read, the test `eo = 0`. -/
theorem word_head (I : Array Word) (s : St) (hM : Inv s.M) (N : ℕ) :
    semXIR I (wordIR N) s = semXIR I (.blk incPs) (semXIR I (.ite rZ lenIR (restIR N))
      (semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s))) := by
  rw [wordIR_eq]; rfl

/-! ## The four cases of one word -/

/-- **The length word.** -/
theorem word_len {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) {pos : ℕ} (hW : rd s.M rWp = toWord pos)
    (hpos : pos < 2 ^ 64) (hE : rd s.M rEo = 0) :
    Keep s (semXIR I (wordIR N) s) ∧ Stat I T N M₀ x (semXIR I (wordIR N) s) ∧
    rd (semXIR I (wordIR N) s).M rWp = toWord (pos + 1) ∧
    rd (semXIR I (wordIR N) s).M rEo = 1 ∧
    rd (semXIR I (wordIR N) s).M rQw = ceil8 (I.getD pos 0) ∧
    rd (semXIR I (wordIR N) s).M rMt = XOp.eq.eval (I.getD pos 0) (rd s.M rTl) := by
  have hM := h.inv
  obtain ⟨p1, p2, p3, p4⟩ := pre_sem I s hM hW (by omega)
  have hh2 := hframe I (.seq (.input rWd rWp) (.blk w2Ps)) s (by
    simp +decide only [Lo, w2Ps, Prim.dst, regs, rWd, rKd, rZ, and_true])
  have z2 := size_sem I (.seq (.input rWd rWp) (.blk w2Ps)) s
  simp only [semXIR_seq] at hh2 z2
  rw [word_head I s hM N]
  generalize semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s) = s2 at p1 p2 p3 p4 hh2 z2
  rw [semXIR_ite, p2, hE, if_neg (by decide)]
  obtain ⟨l1, l2, l3⟩ := lenIR_sem I s2 p4
  have hh3 := hframe I lenIR s2 lo_lenIR
  have z3 := size_sem I lenIR s2
  have hM3 := inv_sem I wf_lenIR p4
  have f3 : ∀ i < regs, ¬ Writes lenIR i → rd (semXIR I lenIR s2).M i = rd s2.M i :=
    fun i hi hw => frame I lenIR s2 wf_lenIR p4 i hi hw
  generalize semXIR I lenIR s2 = s3 at l1 l2 l3 hh3 z3 hM3 f3
  have w3 : rd s3.M rWp = toWord pos := by
    rw [f3 _ (by decide) (by simp +decide only [lenIR, ceil8Ps, Writes, Prim.dst, rWp, rQw, rMt,
      rEo, rKc, rT2, List.cons_append, List.nil_append]),
      p3 _ (by decide) (by decide) (by decide), hW]
  obtain ⟨i1, i2, hM4⟩ := inc_sem I s3 hM3 w3
  have hl : ∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo) → rd (semXIR I (.blk incPs) s3).M r =
      rd s.M r := fun r hr => by
    have hr' : r < regs ∧ ¬ Writes lenIR r ∧ r ≠ rWd ∧ r ≠ rKd ∧ r ≠ rZ ∧ r ≠ rWp := by
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp +decide only [lenIR, ceil8Ps, Writes, Prim.dst, regs, rWp, rQw, rMt, rEo, rKc, rT2,
          rPi, rTl, rTh, rTo, rWd, rKd, rZ, and_true, List.cons_append, List.nil_append]
    rw [i2 r hr'.2.2.2.2.2, f3 r hr'.1 hr'.2.1, p3 r hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2.1]
  have hH : ∀ y, regs ≤ y → rd (semXIR I (.blk incPs) s3).M y = rd s.M y := fun y hy => by
    rw [i2 y (by simp only [rWp, regs] at hy ⊢; omega), hh3 y hy, hh2 y hy]
  refine ⟨⟨hl, hH⟩, h.frame hM4 (by rw [size_sem, z3, z2]) hl hH, i1, ?_, ?_, ?_⟩
  · rw [i2 _ (by decide), l3]
  · rw [i2 _ (by decide), l1, p1]
  · rw [i2 _ (by decide), l2, p1, p3 _ (by decide) (by decide) (by decide)]

/-- **A query word** `j < qw`. -/
theorem word_qry {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) {pos j qw : ℕ} {b : Bool} (hW : rd s.M rWp = toWord pos)
    (hpos : pos < 2 ^ 64) (hj : j < qw) (hqw : qw < 2 ^ 62)
    (hE : rd s.M rEo = toWord (j + 1)) (hQ : rd s.M rQw = toWord qw) (hT : rd s.M rMt = bW b) :
    Keep s (semXIR I (wordIR N) s) ∧ Stat I T N M₀ x (semXIR I (wordIR N) s) ∧
    rd (semXIR I (wordIR N) s).M rWp = toWord (pos + 1) ∧
    rd (semXIR I (wordIR N) s).M rEo = toWord (j + 2) ∧
    rd (semXIR I (wordIR N) s).M rQw = toWord qw ∧
    rd (semXIR I (wordIR N) s).M rMt =
      bW (b && decide (I.getD pos 0 = exW I s.M (rd s.M rTh).toNat (rd s.M rTo).toNat j)) := by
  have hM := h.inv
  obtain ⟨p1, p2, p3, p4⟩ := pre_sem I s hM hW (by omega)
  have hh2 := hframe I (.seq (.input rWd rWp) (.blk w2Ps)) s (by
    simp +decide only [Lo, w2Ps, Prim.dst, regs, rWd, rKd, rZ, and_true])
  have z2 := size_sem I (.seq (.input rWd rWp) (.blk w2Ps)) s
  simp only [semXIR_seq] at hh2 z2
  rw [word_head I s hM N]
  generalize semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s) = s2 at p1 p2 p3 p4 hh2 z2
  have hne : rd s.M rEo ≠ 0 := by
    rw [hE]; intro e
    have := congrArg BitVec.toNat e
    rw [toNat_toWord (by omega)] at this
    simp at this
  rw [semXIR_ite, p2, decide_eq_false hne, if_pos (by decide), restIR, semXIR_seq]
  -- the phase test: a query word
  have hs2 := p4.1
  simp only [regs] at hs2
  have q1 : rd (semXIR I (.blk [.op .ltu rZ rQw rEo]) s2).M rZ = 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rZ]; omega), p3 _ (by decide) (by decide) (by decide),
      p3 _ (by decide) (by decide) (by decide), hQ, hE, ltW_toWord (by omega) (by omega),
      decide_eq_false (by omega)]
    rfl
  have g1 : ∀ i, i ≠ rZ → rd (semXIR I (.blk [.op .ltu rZ rQw rEo]) s2).M i = rd s2.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have hM5 :=
    inv_sem I (P := .blk [.op .ltu rZ rQw rEo]) (by simp +decide only [WF, Prim.dst, rZ]) p4
  have hh5 := hframe I (.blk [.op .ltu rZ rQw rEo]) s2 (by simp +decide only [Lo, Prim.dst, regs,
    rZ])
  have z5 := size_sem I (.blk [.op .ltu rZ rQw rEo]) s2
  generalize semXIR I (.blk [.op .ltu rZ rQw rEo]) s2 = s5 at q1 g1 hM5 hh5 z5
  rw [semXIR_ite, q1, if_pos rfl]
  have r5 : ∀ r, r ≠ rZ → r ≠ rWd → r ≠ rKd → rd s5.M r = rd s.M r := fun r a b c => by
    rw [g1 r a, p3 r b c a]
  have hth : (rd s.M rTh).toNat ≤ 16 := h.th
  have hto : (rd s.M rTo).toNat < 2 ^ 62 := h.tof
  obtain ⟨k1, k2⟩ := qryIR_sem I s5 hM5 (j := j) (h := (rd s.M rTh).toNat) (o := (rd s.M rTo).toNat)
    (b := b) (by omega) hth (by omega)
    (by rw [r5 _ (by decide) (by decide) (by decide), hE])
    (by rw [r5 _ (by decide) (by decide) (by decide), toWord_toNat])
    (by rw [r5 _ (by decide) (by decide) (by decide), toWord_toNat])
    (by rw [r5 _ (by decide) (by decide) (by decide), hT])
  have hh6 := hframe I qryIR s5 lo_qryIR
  have z6 := size_sem I qryIR s5
  have hM6 := inv_sem I wf_qryIR hM5
  have f6 : ∀ i < regs, ¬ Writes qryIR i → rd (semXIR I qryIR s5).M i = rd s5.M i :=
    fun i hi hw => frame I qryIR s5 wf_qryIR hM5 i hi hw
  have wd : rd s5.M rWd = I.getD pos 0 := by rw [g1 _ (by decide), p1]
  have ex : exW I s5.M (rd s.M rTh).toNat (rd s.M rTo).toNat j =
      exW I s.M (rd s.M rTh).toNat (rd s.M rTo).toNat j :=
    exW_congr (fun y hy => by rw [hh5 y hy, hh2 y hy]) _ _ _
  rw [wd, ex] at k1
  generalize semXIR I qryIR s5 = s6 at k1 k2 hh6 z6 hM6 f6
  have w6 : rd s6.M rWp = toWord pos := by
    rw [f6 _ (by decide) (by simp +decide only [qryIR, Writes, Prim.dst, rWp, rKj, rZ, rKd, rAd4,
      rE, rMt, rEo, or_false]),
      r5 _ (by decide) (by decide) (by decide), hW]
  obtain ⟨i1, i2, hM7⟩ := inc_sem I s6 hM6 w6
  have hl : ∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo ∨ r = rQw) →
      rd (semXIR I (.blk incPs) s6).M r = rd s.M r := fun r hr => by
    have hr' : r < regs ∧ ¬ Writes qryIR r ∧ r ≠ rWd ∧ r ≠ rKd ∧ r ≠ rZ ∧ r ≠ rWp := by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp +decide only [qryIR, Writes, Prim.dst, regs, rWp, rKj, rZ, rKd, rAd4, rE, rMt, rEo,
          rPi, rTl, rTh, rTo, rWd, rQw, or_false, and_true]
    rw [i2 r hr'.2.2.2.2.2, f6 r hr'.1 hr'.2.1, r5 r hr'.2.2.2.2.1 hr'.2.2.1 hr'.2.2.2.1]
  have hH : ∀ y, regs ≤ y → rd (semXIR I (.blk incPs) s6).M y = rd s.M y := fun y hy => by
    rw [i2 y (by simp only [rWp, regs] at hy ⊢; omega), hh6 y hy, hh5 y hy, hh2 y hy]
  have hl4 : ∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo) →
      rd (semXIR I (.blk incPs) s6).M r = rd s.M r :=
    fun r hr => hl r (by rcases hr with h | h | h | h <;> simp [h])
  refine ⟨⟨hl4, hH⟩, h.frame hM7 (by rw [size_sem, z6, z5, z2]) hl4 hH, i1, ?_, ?_, ?_⟩
  · rw [i2 _ (by decide), k2]
  · rw [hl _ (.inr (.inr (.inr (.inr rfl)))), hQ]
  · rw [i2 _ (by decide), k1]


/-- The path to an answer word: past the length test and the phase test, then `ansPs`. -/
theorem word_ans_path {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) {pos qw m : ℕ} (hW : rd s.M rWp = toWord pos)
    (hpos : pos < 2 ^ 64) (hm : m < 4) (hqw : qw < 2 ^ 62)
    (hE : rd s.M rEo = toWord (1 + qw + m)) (hQ : rd s.M rQw = toWord qw) :
    ∃ s3 : St, Inv s3.M ∧ s3.M.size = s.M.size ∧ (∀ y, regs ≤ y → rd s3.M y = rd s.M y) ∧
      (∀ i < 4, rd s3.M (rS0 + i) = if i = m then I.getD pos 0 else rd s.M (rS0 + i)) ∧
      rd s3.M rZ = bW (decide (m = 3)) ∧
      (∀ r, r < regs → r ≠ rWd → r ≠ rKd → r ≠ rZ → r ≠ rKj → r ≠ rMk5 → r ≠ rS0 → r ≠ rS1 →
        r ≠ rS2 → r ≠ rS3 → rd s3.M r = rd s.M r) ∧
      semXIR I (wordIR N) s = semXIR I (.blk incPs)
        (semXIR I (.ite rZ (lastIR N) (.blk [.op .add rEo rEo cOne])) s3) := by
  have hM := h.inv
  obtain ⟨p1, p2, p3, p4⟩ := pre_sem I s hM hW (by omega)
  have hh2 := hframe I (.seq (.input rWd rWp) (.blk w2Ps)) s (by
    simp +decide only [Lo, w2Ps, Prim.dst, regs, rWd, rKd, rZ, and_true])
  have z2 := size_sem I (.seq (.input rWd rWp) (.blk w2Ps)) s
  simp only [semXIR_seq] at hh2 z2
  rw [word_head I s hM N]
  generalize semXIR I (.blk w2Ps) (semXIR I (.input rWd rWp) s) = s2 at p1 p2 p3 p4 hh2 z2
  have hne : rd s.M rEo ≠ 0 := by
    rw [hE]; intro e
    have := congrArg BitVec.toNat e
    rw [toNat_toWord (by omega)] at this
    simp at this
  rw [semXIR_ite, p2, decide_eq_false hne, if_pos (by decide), restIR, semXIR_seq]
  have hs2 := p4.1
  simp only [regs] at hs2
  have q1 : rd (semXIR I (.blk [.op .ltu rZ rQw rEo]) s2).M rZ = bW true := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rZ]; omega), p3 _ (by decide) (by decide) (by decide),
      p3 _ (by decide) (by decide) (by decide), hQ, hE, ltW_toWord (by omega) (by omega),
      decide_eq_true (by omega)]
  have g1 : ∀ i, i ≠ rZ → rd (semXIR I (.blk [.op .ltu rZ rQw rEo]) s2).M i = rd s2.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have hM5 :=
    inv_sem I (P := .blk [.op .ltu rZ rQw rEo]) (by simp +decide only [WF, Prim.dst, rZ]) p4
  have hh5 := hframe I (.blk [.op .ltu rZ rQw rEo]) s2 (by simp +decide only [Lo, Prim.dst, regs,
    rZ])
  have z5 := size_sem I (.blk [.op .ltu rZ rQw rEo]) s2
  generalize semXIR I (.blk [.op .ltu rZ rQw rEo]) s2 = s5 at q1 g1 hM5 hh5 z5
  rw [semXIR_ite, q1, if_neg (by decide), ansIR, semXIR_seq]
  have r5 : ∀ r, r ≠ rZ → r ≠ rWd → r ≠ rKd → rd s5.M r = rd s.M r := fun r a b c => by
    rw [g1 r a, p3 r b c a]
  obtain ⟨a1, a2⟩ := ansPs_sem I s5 hM5 (qw := qw) (m := m) hm (by omega) (by rw [r5 _ (by decide) (by decide)
    (by decide), hE]) (by rw [r5 _ (by decide) (by decide) (by decide), hQ])
  refine ⟨semXIR I (.blk ansPs) s5, inv_sem I wf_ansPs hM5, by rw [size_sem, z5, z2],
    fun y hy => by rw [hframe I _ s5 lo_ansPs y hy, hh5 y hy, hh2 y hy], fun i hi => ?_, a2,
    fun r hr a b c d e f g k l => ?_, rfl⟩
  · rw [a1 i hi, g1 rWd (by decide), p1, g1 (rS0 + i) (by simp only [rS0, rZ]; omega),
      p3 (rS0 + i) (by simp only [rS0, rWd]; omega) (by simp only [rS0, rKd]; omega)
      (by simp only [rS0, rZ]; omega)]
  · rw [frame I _ s5 wf_ansPs hM5 r hr (by
      simp +decide only [Writes, ansPs, setSPs, Prim.dst, List.mem_cons, List.mem_nil_iff,
        exists_eq_or_imp, exists_eq_left, or_false, List.cons_append, List.nil_append]
      simp only [rKj, rKd, rMk5, rS0, rS1, rS2, rS3, rZ] at *
      omega), r5 r c a b]

/-- **A non-final answer word** `m < 3`. -/
theorem word_ans {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) {pos qw m : ℕ} (hW : rd s.M rWp = toWord pos)
    (hpos : pos < 2 ^ 64) (hm : m < 3) (hqw : qw < 2 ^ 62)
    (hE : rd s.M rEo = toWord (1 + qw + m)) (hQ : rd s.M rQw = toWord qw) :
    Keep s (semXIR I (wordIR N) s) ∧ Stat I T N M₀ x (semXIR I (wordIR N) s) ∧
    rd (semXIR I (wordIR N) s).M rWp = toWord (pos + 1) ∧
    rd (semXIR I (wordIR N) s).M rEo = toWord (1 + qw + (m + 1)) ∧
    rd (semXIR I (wordIR N) s).M rQw = toWord qw ∧
    rd (semXIR I (wordIR N) s).M rMt = rd s.M rMt ∧
    ∀ i < 4, rd (semXIR I (wordIR N) s).M (rS0 + i) =
      if i = m then I.getD pos 0 else rd s.M (rS0 + i) := by
  obtain ⟨s3, hM3, z3, hh3, hS3, hZ3, hr3, e⟩ :=
    word_ans_path h hW hpos (by omega) hqw hE hQ
  rw [e, semXIR_ite, hZ3, decide_eq_false (by omega), if_pos (by decide)]
  have hs3 := hM3.1
  have h13 : rd s3.M cOne = 1 := hM3.2 0 (by decide)
  simp only [regs] at hs3
  have k1 : rd (semXIR I (.blk [.op .add rEo rEo cOne]) s3).M rEo = toWord (1 + qw + (m + 1)) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rEo]; omega), hr3 _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hE, h13,
      add_one_toWord, Nat.add_assoc]
  have g1 : ∀ i, i ≠ rEo → rd (semXIR I (.blk [.op .add rEo rEo cOne]) s3).M i = rd s3.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have hM4 := inv_sem I (P := .blk [.op .add rEo rEo cOne]) (by simp +decide only [WF, Prim.dst,
    rEo]) hM3
  have hh4 := hframe I (.blk [.op .add rEo rEo cOne]) s3 (by simp +decide only [Lo, Prim.dst, regs,
    rEo])
  have z4 := size_sem I (.blk [.op .add rEo rEo cOne]) s3
  generalize semXIR I (.blk [.op .add rEo rEo cOne]) s3 = s4 at k1 g1 hM4 hh4 z4
  have w4 : rd s4.M rWp = toWord pos := by
    rw [g1 _ (by decide), hr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hW]
  obtain ⟨i1, i2, hM5⟩ := inc_sem I s4 hM4 w4
  have keep : ∀ r, r < regs → r ≠ rWd → r ≠ rKd → r ≠ rZ → r ≠ rKj → r ≠ rMk5 → r ≠ rS0 →
      r ≠ rS1 → r ≠ rS2 → r ≠ rS3 → r ≠ rEo → r ≠ rWp →
      rd (semXIR I (.blk incPs) s4).M r = rd s.M r := fun r hr a b c d e f g k l n o => by
    rw [i2 r o, g1 r n, hr3 r hr a b c d e f g k l]
  have hl4 : ∀ r, (r = rPi ∨ r = rTl ∨ r = rTh ∨ r = rTo) →
      rd (semXIR I (.blk incPs) s4).M r = rd s.M r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hH : ∀ y, regs ≤ y → rd (semXIR I (.blk incPs) s4).M y = rd s.M y := fun y hy => by
    rw [i2 y (by simp only [rWp, regs] at hy ⊢; omega), hh4 y hy, hh3 y hy]
  refine ⟨⟨hl4, hH⟩, h.frame hM5 (by rw [size_sem, z4, z3]) hl4 hH, i1,
    by rw [i2 _ (by decide), k1], ?_, ?_, fun i hi => ?_⟩
  · rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hQ]
  · exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [i2 _ (by simp only [rS0, rWp]; omega), g1 _ (by simp only [rS0, rEo]; omega), hS3 i hi]


/-- `eo := 0` then the next word. -/
theorem word_tail (I : Array Word) (s : St) (hM : Inv s.M) {pos : ℕ} (hW : rd s.M rWp = toWord pos) :
    rd (semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s)).M rWp = toWord (pos + 1) ∧
    rd (semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s)).M rEo = 0 ∧
    (∀ i, i ≠ rWp → i ≠ rEo → rd (semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s)).M i =
      rd s.M i) ∧
    Inv (semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s)).M ∧
    (semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s)).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs
  have hM1 := inv_sem I (P := .blk [.const rEo 0]) (by simp +decide only [WF, Prim.dst, rEo]) hM
  have e1 : rd (semXIR I (.blk [.const rEo 0]) s).M rEo = 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rEo]; omega)
  have g1 : ∀ i, i ≠ rEo → rd (semXIR I (.blk [.const rEo 0]) s).M i = rd s.M i :=
    fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _
  have z1 := size_sem I (.blk [.const rEo 0]) s
  generalize semXIR I (.blk [.const rEo 0]) s = s1 at hM1 e1 g1 z1
  obtain ⟨i1, i2, hM2⟩ := inc_sem I s1 hM1 (by rw [g1 _ (by decide), hW])
  exact ⟨i1, by rw [i2 _ (by decide), e1], fun i a b => by rw [i2 i a, g1 i b], hM2,
    by rw [size_sem, z1]⟩

/-- **The last answer word**: after it, `eo = 0`, and the scan state advances iff `p < N` and the
flag is set (the record), with the answer `a` whose words are the four answer words. -/
theorem word_last {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) (hTab : TabOK I T N M₀) (hN : N < 2 ^ 9) {pos qw : ℕ}
    {b : Bool} (hW : rd s.M rWp = toWord pos) (hpos : pos < 2 ^ 64) (hqw : qw < 2 ^ 62)
    (hE : rd s.M rEo = toWord (1 + qw + 3)) (hQ : rd s.M rQw = toWord qw)
    (hT : rd s.M rMt = bW b) (a : Digest)
    (hA : ∀ i < 4, (if i = 3 then I.getD pos 0 else rd s.M (rS0 + i)) =
      (packBytes a.toList).getD i 0) :
    rd (semXIR I (wordIR N) s).M rWp = toWord (pos + 1) ∧
    rd (semXIR I (wordIR N) s).M rEo = 0 ∧
    Stat I T N M₀ (if x.1 < N ∧ b = true then (x.1 + 1, a, x.2.2 ++ [a]) else x)
      (semXIR I (wordIR N) s) := by
  obtain ⟨s3, hM3, z3, hh3, hS3, hZ3, hr3, e⟩ := word_ans_path h hW hpos (m := 3) (by omega) hqw hE hQ
  rw [e, semXIR_ite, hZ3, decide_eq_true rfl, if_neg (by decide)]
  have hp : x.1 ≤ N := h.pN
  have hP3 : rd s3.M rPi = toWord x.1 := by
    rw [hr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h.pi]
  have hT3 : rd s3.M rMt = bW b := by
    rw [hr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hT]
  obtain ⟨s₁, hM₁, z₁, f₁, e₁⟩ := lastIR_sem I s3 hM3 (N := N) (p := x.1) (b := b) (by omega)
    (by omega) hP3 hT3
  rw [e₁]
  have w₁ : ∀ r, r ≠ rKd → r ≠ rZ → r < regs → r ≠ rWd → r ≠ rKj → r ≠ rMk5 → r ≠ rS0 → r ≠ rS1 →
      r ≠ rS2 → r ≠ rS3 → rd s₁.M r = rd s.M r := fun r a b c d e f g k l m => by
    rw [f₁ r a b, hr3 r c d a b e f g k l m]
  have hh₁ : ∀ y, regs ≤ y → rd s₁.M y = rd s.M y := fun y hy => by
    rw [f₁ y (by simp only [rKd, regs] at hy ⊢; omega) (by simp only [rZ, regs] at hy ⊢; omega),
      hh3 y hy]
  have hS₁ : ∀ i < 4, rd s₁.M (rS0 + i) = (packBytes a.toList).getD i 0 := fun i hi => by
    rw [f₁ _ (by simp only [rS0, rKd]; omega) (by simp only [rS0, rZ]; omega), hS3 i hi, ← hA i hi]
  by_cases hc : x.1 < N ∧ b = true
  · rw [if_pos hc, if_pos hc]
    obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := recIR_sem I s₁ hM₁ (p := x.1) (by omega)
      (by rw [w₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), h.pi]) (by rw [z₁, z3]; exact h.size)
    have z6 := size_sem I recIR s₁
    generalize semXIR I recIR s₁ = s6 at n1 n2 n3 n4 n5 n6 n7 z6
    have w6 : rd s6.M rWp = toWord pos := by
      rw [n6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), w₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), hW]
    obtain ⟨t1, t2, t3, t4, t5⟩ := word_tail I s6 n7 w6
    generalize semXIR I (.blk incPs) (semXIR I (.blk [.const rEo 0]) s6) = s8 at t1 t2 t3 t4 t5
    -- the table entry `p + 1` is `M₀`'s
    have hM0 : ∀ k < 3, rd s₁.M (chB + 4 * (x.1 + 1) + k) = rd M₀ (chB + 4 * (x.1 + 1) + k) :=
      fun k hk => by
        rw [hh₁ _ (by simp only [chB_eq, regs]; omega), h.heap _ (by simp only [chB_eq, regs]; omega)
          (.inl (by simp only [chB_eq, hB_eq]; omega)) (.inl (by simp only [chB_eq, ansB_eq]; omega))]
    obtain ⟨hto, htg⟩ := hTab (x.1 + 1) (by omega) (by omega)
    have r8 : ∀ r, r ≠ rWp → r ≠ rEo → rd s8.M r = rd s6.M r := t3
    refine ⟨t1, t2, ?_⟩
    have tl8 : rd s8.M rTl = rd M₀ (chB + 4 * (x.1 + 1)) := by
      rw [r8 _ (by decide) (by decide), n2]; exact hM0 0 (by norm_num)
    have to8 : rd s8.M rTo = rd M₀ (chB + 4 * (x.1 + 1) + 1) := by
      rw [r8 _ (by decide) (by decide), n3, hM0 1 (by norm_num)]
    have th8 : rd s8.M rTh = 5 := by rw [r8 _ (by decide) (by decide), n4]
    have heap8 : ∀ y, regs ≤ y → rd s8.M y =
        if ansB + 4 * x.1 ≤ y ∧ y < ansB + 4 * x.1 + 4 then (packBytes a.toList).getD
          (y - (ansB + 4 * x.1)) 0
        else if hB + 1 ≤ y ∧ y < hB + 5 then (packBytes a.toList).getD (y - (hB + 1)) 0
        else if y = hB then rd M₀ (chB + 4 * (x.1 + 1) + 2) else rd s.M y := fun y hy => by
      rw [r8 y (by simp only [rWp, regs] at hy ⊢; omega) (by simp only [rEo, regs] at hy ⊢; omega),
        n5 y hy]
      split_ifs with q1 q2 q3
      · exact hS₁ _ (by omega)
      · exact hS₁ _ (by omega)
      · rw [hM0 2 (by norm_num)]
      · exact hh₁ y hy
    exact {
      inv := t4
      size := by rw [t5, z6, z₁, z3]; exact h.size
      pi := by rw [r8 _ (by decide) (by decide), n1]
      pN := by simp only; omega
      len := by simp [h.len]
      th := by rw [th8]; decide
      tof := by rw [to8]; exact hto
      tg := fun hlt => by
        obtain ⟨g1, g2, g3⟩ := htg hlt a
        refine ⟨by rw [tl8, g1], g2, fun j hj => ?_⟩
        rw [g3 j hj, th8, to8, show (5 : Word).toNat = 5 from rfl, exW]
        by_cases hj5 : j < 5
        · rw [if_pos hj5, if_pos hj5, heap8 (hB + j) (by simp only [hB_eq, regs]; omega),
            if_neg (show ¬ (ansB + 4 * x.1 ≤ hB + j ∧ hB + j < ansB + 4 * x.1 + 4) by
              simp only [hB_eq, ansB_eq]; omega)]
          by_cases hj0 : j = 0
          · rw [if_pos hj0, if_neg (show ¬ (hB + 1 ≤ hB + j ∧ hB + j < hB + 5) by omega),
              if_pos (show hB + j = hB by omega)]
          · rw [if_neg hj0, if_pos (show hB + 1 ≤ hB + j ∧ hB + j < hB + 5 by omega),
              show hB + j - (hB + 1) = j - 1 by omega]
        · rw [if_neg hj5, if_neg hj5, show (rd M₀ (chB + 4 * (x.1 + 1) + 1)).toNat + j - 5 =
            (rd M₀ (chB + 4 * (x.1 + 1) + 1)).toNat + (j - 5) by omega]
      ans := fun q hq m hm => by
        simp only at hq ⊢
        rw [heap8 (ansB + 4 * q + m) (by simp only [ansB_eq, regs]; omega)]
        by_cases hqx : q = x.1
        · subst hqx
          rw [if_pos (by omega), show ansB + 4 * x.1 + m - (ansB + 4 * x.1) = m by omega,
            List.getD_append_right _ _ _ _ (by rw [h.len]), h.len, Nat.sub_self]
          rfl
        · rw [if_neg (by omega), if_neg (by simp only [ansB_eq, hB_eq]; omega),
            if_neg (by simp only [ansB_eq, hB_eq]; omega),
            List.getD_append _ _ _ _ (by rw [h.len]; omega)]
          exact h.ans q (by omega) m hm
      heap := fun y hy h1 h2 => by
        rw [heap8 y hy, if_neg (by simp only [ansB_eq, chEnd] at h2 ⊢; omega),
          if_neg (by simp only [hB_eq] at h1 ⊢; omega), if_neg (by simp only [hB_eq] at h1 ⊢; omega)]
        exact h.heap y hy h1 h2 }
  · rw [if_neg hc, if_neg hc]
    have w₁' : rd s₁.M rWp = toWord pos := by
      rw [w₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hW]
    obtain ⟨t1, t2, t3, t4, t5⟩ := word_tail I s₁ hM₁ w₁'
    refine ⟨t1, t2, h.frame t4 (by rw [t5, z₁, z3]) (fun r hr => ?_) (fun y hy => ?_)⟩
    · rcases hr with rfl | rfl | rfl | rfl <;>
        rw [t3 _ (by decide) (by decide), w₁ _ (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [t3 y (by simp only [rWp, regs] at hy ⊢; omega) (by simp only [rEo, regs] at hy ⊢; omega),
        hh₁ y hy]


/-! ## One entry -/

theorem iterL_add (f : St → St) (c : ℕ) : ∀ (a b : ℕ) (s : St),
    iterL f c (a + b) s = iterL f c b (iterL f c a s)
  | 0, b, s => by simp [iterL]
  | a + 1, b, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [iterL]
    exact iterL_add f c a b _

theorem iterL_one (f : St → St) (c : ℕ) (s : St) : iterL f c 1 s = decS c (f s) := rfl

theorem Keep.trans {s₀ s s' : St} (h : Keep s₀ s) (h' : Keep s s') : Keep s₀ s' :=
  ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr), fun y hy => (h'.2 y hy).trans (h.2 y hy)⟩

theorem Keep.refl (s : St) : Keep s s := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem keep_decS (s : St) : Keep s (decS rCC s) :=
  ⟨fun r hr => rd_decS (by rcases hr with rfl | rfl | rfl | rfl <;> decide) s,
    fun y hy => rd_decS (by simp only [rCC, regs] at hy ⊢; omega) s⟩

theorem Stat.decS {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) : Stat I T N M₀ x (FR.X.decS rCC s) :=
  h.frame (inv_of_frame h.inv (size_decS ..) fun i hi => rd_decS (by
    simp only [rCC]; omega) _) (size_decS ..) (keep_decS s).1 (keep_decS s).2

/-- **The tape holds entry `e` at `pos`**: `|q|`, its packed words, its answer's 4 words. -/
structure EntryAt (I : Array Word) (pos : ℕ) (e : ByteArray × Digest) : Prop where
  len : I.getD pos 0 = toWord e.1.size
  lt : e.1.size < 2 ^ 64
  qry : ∀ j < (e.1.size + 7) / 8, I.getD (pos + 1 + j) 0 = (packBytes e.1.data.toList).getD j 0
  ans : ∀ m < 4, I.getD (pos + 1 + (e.1.size + 7) / 8 + m) 0 = (packBytes e.2.toList).getD m 0
  fit : pos + qWords e ≤ 2 ^ 64

/-- **Byte strings of one length with the same packed words are equal.** -/
theorem eq_of_packBytes {q Q : ByteArray} (hs : q.size = Q.size)
    (hw : ∀ j < (q.size + 7) / 8, (packBytes q.data.toList).getD j 0 =
      (packBytes Q.data.toList).getD j 0) : q = Q := by
  have hl : q.data.toList = Q.data.toList := by
    refine List.ext_getElem (by simp only [Array.length_toList]; exact hs) fun i h1 h2 => ?_
    have hi : i < q.size := by simpa using h1
    have e1 := wordByte_packBytes q.data.toList i
    have e2 := wordByte_packBytes Q.data.toList i
    rw [List.getD_eq_getElem _ _ h1] at e1
    rw [List.getD_eq_getElem _ _ h2] at e2
    rw [← e1, ← e2]
    unfold wordByte
    rw [hw (i / 8) (by omega)]
  obtain ⟨d⟩ := q
  obtain ⟨D⟩ := Q
  simp only [ByteArray.mk.injEq]
  exact Array.toList_inj.mp hl

/-- The query phase: from word `j` to word `qw`, the flag is the conjunction so far. -/
theorem qry_loop {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    (s₀ : St) (A : Prop) [Decidable A] {pos qw : ℕ} (hqw : qw < 2 ^ 62)
    (hpos : pos + 1 + qw < 2 ^ 64) :
    ∀ k j (s : St), j + k = qw → Stat I T N M₀ x s → Keep s₀ s →
      rd s.M rWp = toWord (pos + 1 + j) → rd s.M rEo = toWord (1 + j) →
      rd s.M rQw = toWord qw →
      rd s.M rMt = bW (decide (A ∧ ∀ j' < j, I.getD (pos + 1 + j') 0 =
        exW I s₀.M (rd s₀.M rTh).toNat (rd s₀.M rTo).toNat j')) →
      Stat I T N M₀ x (iterL (semXIR I (wordIR N)) rCC k s) ∧
      Keep s₀ (iterL (semXIR I (wordIR N)) rCC k s) ∧
      rd (iterL (semXIR I (wordIR N)) rCC k s).M rWp = toWord (pos + 1 + qw) ∧
      rd (iterL (semXIR I (wordIR N)) rCC k s).M rEo = toWord (1 + qw) ∧
      rd (iterL (semXIR I (wordIR N)) rCC k s).M rQw = toWord qw ∧
      rd (iterL (semXIR I (wordIR N)) rCC k s).M rMt = bW (decide (A ∧ ∀ j' < qw,
        I.getD (pos + 1 + j') 0 = exW I s₀.M (rd s₀.M rTh).toNat (rd s₀.M rTo).toNat j'))
  | 0, j, s, hj, h, hk, hW, hE, hQ, hT => by
    simp only [iterL]
    obtain rfl : j = qw := by omega
    exact ⟨h, hk, hW, hE, hQ, hT⟩
  | k + 1, j, s, hj, h, hk, hW, hE, hQ, hT => by
    obtain ⟨K, h1, w1, e1, q1, t1⟩ := word_qry (N := N) h hW (by omega) (j := j) (qw := qw)
      (by omega) hqw (by rw [hE, Nat.add_comm]) hQ hT
    have hK : Keep s₀ (FR.X.decS rCC (semXIR I (wordIR N) s)) :=
      (hk.trans K).trans (keep_decS _)
    simp only [iterL]
    refine qry_loop s₀ A hqw hpos k (j + 1) _ (by omega) h1.decS hK ?_ ?_ ?_ ?_
    · rw [rd_decS (by decide), w1, Nat.add_assoc]
    · rw [rd_decS (by decide), e1, Nat.add_comm 1 (j + 1)]
    · rw [rd_decS (by decide), q1]
    · rw [rd_decS (by decide), t1, hk.1 _ (.inr (.inr (.inl rfl))), hk.1 _ (.inr (.inr (.inr rfl))),
        exW_congr hk.2]
      refine congrArg bW ?_
      rw [← Bool.decide_and, decide_eq_decide]
      constructor
      · rintro ⟨⟨hA, hall⟩, hj'⟩
        refine ⟨hA, fun j' h => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
        · exact hall j' h
        · exact hj'
      · rintro ⟨hA, hall⟩
        exact ⟨⟨hA, fun j' h => hall j' (by omega)⟩, hall j (by omega)⟩


theorem ceil8_toWord {a : ℕ} (h : a < 2 ^ 64) : ceil8 (toWord a) = toWord ((a + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ceil8 h, toNat_toWord (by omega)]

/-- **One entry**: its `qWords e` words do `scanStep` on the scan state. -/
theorem entry_sem {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem} {x : SS}
    {s : St} (h : Stat I T N M₀ x s) (hTab : TabOK I T N M₀) (hN : N < 2 ^ 9) {pos : ℕ}
    {e : ByteArray × Digest} (hW : rd s.M rWp = toWord pos) (hE : rd s.M rEo = 0)
    (he : EntryAt I pos e) :
    Stat I T N M₀ (scanStep T N x e) (iterL (semXIR I (wordIR N)) rCC (qWords e) s) ∧
    rd (iterL (semXIR I (wordIR N)) rCC (qWords e) s).M rWp = toWord (pos + qWords e) ∧
    rd (iterL (semXIR I (wordIR N)) rCC (qWords e) s).M rEo = 0 := by
  have hfit := he.fit
  simp only [qWords] at hfit ⊢
  generalize hqw : (e.1.size + 7) / 8 = qw at hfit he
  have hqw62 : qw < 2 ^ 62 := by have := he.lt; omega
  have hp6 : pos + 1 + qw + 1 + 1 + 1 < 2 ^ 64 := by omega
  rw [show 5 + qw = 1 + qw + 1 + 1 + 1 + 1 by omega, iterL_add, iterL_add, iterL_add, iterL_add,
    iterL_add, iterL_one, iterL_one, iterL_one, iterL_one, iterL_one]
  -- the length word
  obtain ⟨K1, h1, w1, e1, q1, t1⟩ := word_len (N := N) h hW (by omega) hE
  rw [he.len, ceil8_toWord he.lt, hqw] at q1
  rw [he.len, eq_bW] at t1
  generalize semXIR I (wordIR N) s = s1 at K1 h1 w1 e1 q1 t1
  -- the query words
  obtain ⟨h2, K2, w2, e2, q2, t2⟩ := qry_loop (N := N) s (toWord e.1.size = rd s.M rTl) (pos := pos)
    hqw62 (by omega) qw 0 (FR.X.decS rCC s1) (by omega) h1.decS (K1.trans (keep_decS _))
    (by rw [rd_decS (by decide), w1, Nat.add_zero]) (by rw [rd_decS (by decide), e1]; rfl)
    (by rw [rd_decS (by decide), q1]) (by
      rw [rd_decS (by decide), t1]
      exact congrArg bW (decide_eq_decide.mpr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
        fun h => h.1⟩))
  generalize iterL (semXIR I (wordIR N)) rCC qw (FR.X.decS rCC s1) = s2 at h2 K2 w2 e2 q2 t2
  -- the flag means `q = T p st`
  set b := decide (toWord e.1.size = rd s.M rTl ∧ ∀ j' < qw, I.getD (pos + 1 + j') 0 =
    exW I s.M (rd s.M rTh).toNat (rd s.M rTo).toNat j') with hb
  have hbT : x.1 < N → (b = true ↔ e.1 = T x.1 x.2.1) := fun hx => by
    obtain ⟨g1, g2, g3⟩ := h.tg hx
    rw [hb, decide_eq_true_iff, g1]
    constructor
    · rintro ⟨hA, hall⟩
      have hs : e.1.size = (T x.1 x.2.1).size := by
        have := congrArg BitVec.toNat hA
        rwa [toNat_toWord he.lt, toNat_toWord g2] at this
      refine eq_of_packBytes hs fun j hj => ?_
      rw [← he.qry j (by omega), hall j (by omega), g3 j (by omega)]
    · intro hq
      refine ⟨by rw [hq], fun j' hj' => ?_⟩
      rw [he.qry j' (by omega), ← g3 j' (by rw [← hq]; omega), hq]
  -- the answer words
  obtain ⟨K3, h3, w3, e3, q3, t3, S3⟩ := word_ans (N := N) h2 w2 (by omega) (m := 0) (by omega)
    hqw62 (by rw [e2, Nat.add_zero]) q2
  generalize semXIR I (wordIR N) s2 = s3 at K3 h3 w3 e3 q3 t3 S3
  obtain ⟨K4, h4, w4, e4, q4, t4, S4⟩ := word_ans (N := N) h3.decS (pos := pos + 1 + qw + 1)
    (by rw [rd_decS (by decide), w3]) (by omega) (m := 1) (by omega) hqw62
    (by rw [rd_decS (by decide), e3]) (by rw [rd_decS (by decide), q3])
  generalize semXIR I (wordIR N) (FR.X.decS rCC s3) = s4 at K4 h4 w4 e4 q4 t4 S4
  obtain ⟨K5, h5, w5, e5, q5, t5, S5⟩ := word_ans (N := N) h4.decS (pos := pos + 1 + qw + 1 + 1)
    (by rw [rd_decS (by decide), w4]) (by omega) (m := 2) (by omega) hqw62
    (by rw [rd_decS (by decide), e4]) (by rw [rd_decS (by decide), q4])
  generalize semXIR I (wordIR N) (FR.X.decS rCC s4) = s5 at K5 h5 w5 e5 q5 t5 S5
  have hS : ∀ i < 4, (if i = 3 then I.getD (pos + 1 + qw + 1 + 1 + 1) 0
      else rd (FR.X.decS rCC s5).M (rS0 + i)) = (packBytes e.2.toList).getD i 0 := fun i hi => by
    have a0 := he.ans
    rw [hqw] at a0
    interval_cases i
    · rw [if_neg (by omega), rd_decS (by decide), S5 0 (by omega), if_neg (by omega),
        rd_decS (by decide), S4 0 (by omega), if_neg (by omega), rd_decS (by decide), S3 0 (by omega),
        if_pos rfl, ← a0 0 (by omega)]
      rfl
    · rw [if_neg (by omega), rd_decS (by decide), S5 1 (by omega), if_neg (by omega),
        rd_decS (by decide), S4 1 (by omega), if_pos rfl, ← a0 1 (by omega)]
    · rw [if_neg (by omega), rd_decS (by decide), S5 2 (by omega), if_pos rfl, ← a0 2 (by omega),
        show pos + 1 + qw + 1 + 1 = pos + 1 + qw + 2 by omega]
    · rw [if_pos rfl, ← a0 3 (by omega), show pos + 1 + qw + 1 + 1 + 1 = pos + 1 + qw + 3 by omega]
  have hT5 : rd (FR.X.decS rCC s5).M rMt = bW b := by
    rw [rd_decS (by decide), t5, rd_decS (by decide), t4, rd_decS (by decide), t3, t2]
  obtain ⟨w6, e6, h6⟩ := word_last (N := N) h5.decS hTab hN (pos := pos + 1 + qw + 1 + 1 + 1)
    (qw := qw) (b := b) (by rw [rd_decS (by decide), w5]) hp6 hqw62
    (by rw [rd_decS (by decide), e5]) (by rw [rd_decS (by decide), q5]) hT5 e.2 hS
  have hx : (if x.1 < N ∧ b = true then (x.1 + 1, e.2, x.2.2 ++ [e.2]) else x) =
      scanStep T N x e := by
    unfold scanStep
    by_cases hx : x.1 < N
    · by_cases hq : e.1 = T x.1 x.2.1
      · rw [if_pos ⟨hx, (hbT hx).mpr hq⟩, if_pos ⟨hx, hq⟩]
      · rw [if_neg fun ⟨_, h⟩ => hq ((hbT hx).mp h), if_neg fun ⟨_, h⟩ => hq h]
    · rw [if_neg fun ⟨h, _⟩ => hx h, if_neg fun ⟨h, _⟩ => hx h]
  rw [hx] at h6
  refine ⟨h6.decS, ?_, ?_⟩
  · rw [rd_decS (by decide), w6, show pos + 1 + qw + 1 + 1 + 1 + 1 = pos + (1 + qw + 1 + 1 + 1 + 1) by
      omega]
  · rw [rd_decS (by decide), e6]


/-! ## The log -/

/-- The tape holds the entries `L` from `pos` on, one after the other. -/
def EntriesAt (I : Array Word) : ℕ → Log → Prop
  | _, [] => True
  | pos, e :: L => EntryAt I pos e ∧ EntriesAt I (pos + qWords e) L

/-- The words of the entries `L`. -/
def wordsOf (L : Log) : ℕ := (L.map qWords).sum

/-- **The loop over the log's words** runs the scan over its entries. -/
theorem scan_sem {I : Array Word} {T : ℕ → Digest → ByteArray} {N : ℕ} {M₀ : Mem}
    (hTab : TabOK I T N M₀) (hN : N < 2 ^ 9) :
    ∀ (L : Log) (x : SS) (s : St) (pos : ℕ), Stat I T N M₀ x s → rd s.M rWp = toWord pos →
      rd s.M rEo = 0 → EntriesAt I pos L →
      Stat I T N M₀ (L.foldl (scanStep T N) x) (iterL (semXIR I (wordIR N)) rCC (wordsOf L) s) ∧
      rd (iterL (semXIR I (wordIR N)) rCC (wordsOf L) s).M rWp = toWord (pos + wordsOf L) ∧
      rd (iterL (semXIR I (wordIR N)) rCC (wordsOf L) s).M rEo = 0
  | [], x, s, pos, h, hW, hE, _ => by
    simp only [wordsOf, List.map_nil, List.sum_nil, iterL, List.foldl_nil, Nat.add_zero]
    exact ⟨h, hW, hE⟩
  | e :: L, x, s, pos, h, hW, hE, hL => by
    have hw : wordsOf (e :: L) = qWords e + wordsOf L := by simp [wordsOf]
    rw [hw, iterL_add, List.foldl_cons]
    obtain ⟨h1, w1, e1⟩ := entry_sem h hTab hN hW hE hL.1
    obtain ⟨h2, w2, e2⟩ := scan_sem hTab hN L _ _ _ h1 w1 e1 hL.2
    exact ⟨h2, by rw [w2, Nat.add_assoc], e2⟩

/-- **The extractor's tape holds the log's entries** from `posL + 1` on (`tape_entry`,
`tape_query`, `tape_answer`). -/
theorem entriesAt_tape (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    ∀ k, k ≤ L.length → EntriesAt (extractorInput c π L).toArray (posL + 1 + entryOff L k)
      (L.drop k) := by
  intro k hk
  induction h : L.length - k generalizing k with
  | zero =>
    rw [List.drop_eq_nil_of_le (by omega)]; trivial
  | succ n ih =>
    have hkL : k < L.length := by omega
    rw [List.drop_eq_getElem_cons hkL]
    have hend := tape_entries_end c π L hs
    have hle : entryOff L (k + 1) ≤ entryOff L L.length := by
      rw [entryOff_length]; exact entryOff_le_sum L (k + 1)
    rw [entryOff_succ L hkL] at hle
    refine ⟨⟨?_, hq _ (List.getElem_mem hkL), fun j hj => ?_, fun m hm => ?_, ?_⟩, ?_⟩
    · rw [getD_toArray, tape_entry c π L hs hkL]
    · rw [getD_toArray]; exact tape_query c π L hs hkL hj
    · rw [getD_toArray]; exact tape_answer c π L hs hkL hm
    · omega
    · have := ih (k + 1) (by omega) (by omega)
      rwa [entryOff_succ L hkL, ← Nat.add_assoc] at this

end FR.X
