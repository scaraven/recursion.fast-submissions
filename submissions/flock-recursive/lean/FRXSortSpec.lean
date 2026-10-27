-- New for `flock-recursive` (BLUEPRINT §6.5 `index_spec`; stage S-H2, track L-ext).
import FRXLogSpec

/-!
# The sort's key comparison

`cmpIR` compares the entries at `src[i]` and `src[j]` by the key `keyW I x = [a₀, a₁, a₂, a₃, x]`
(the four answer words of the entry at tape position `x`, then `x` itself), lexicographically
and unsigned (`lexW`). **`cmpIR_sem`**: it leaves `1` in `rF` exactly when `keyLt I x y`.

This is the first brick of the sort's correctness (S-H2-RESULT, Part 3).
-/

namespace FR.X

open RecursionFast

/-- The answer position of the entry at tape position `x`, as the program computes it. -/
def aposW (I : Array Word) (x : Word) : Word := ceil8 (I.getD x.toNat 0) + x + 1

/-- The sort key of the entry at `x`: its four answer words, then `x`. -/
def keyW (I : Array Word) (x : Word) : List Word :=
  [I.getD (aposW I x + 0).toNat 0, I.getD (aposW I x + 1).toNat 0,
   I.getD (aposW I x + 2).toNat 0, I.getD (aposW I x + 3).toNat 0, x]

/-- Lexicographic `<` on word lists, unsigned. -/
def lexW : List Word → List Word → Bool
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && lexW as bs)
  | _, _ => false

/-- The sort order. -/
def keyLt (I : Array Word) (x y : Word) : Bool := lexW (keyW I x) (keyW I y)

/-- A 0/1 word. -/
def bW (p : Bool) : Word := if p then 1 else 0

/-- One step of the machine's lexicographic fold. -/
theorem fold_bW (a b : Word) (p : Bool) :
    XOp.or.eval (XOp.ltu.eval a b) (XOp.and.eval (XOp.eq.eval a b) (bW p)) =
      bW (decide (a < b) || (decide (a = b) && p)) := by
  by_cases h1 : a < b <;> by_cases h2 : a = b <;> cases p <;>
    simp [XOp.eval, bW, h1, h2]

theorem cmpWord_sem (I : Array Word) (s : St) (hM : Inv s.M) (w : ℕ) (hw : w < 2 ^ 64) :
    rd (semXIR I (cmpWord w) s).M rF =
      XOp.or.eval (XOp.ltu.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0)
          (I.getD (rd s.M rPb + BitVec.ofNat 64 w).toNat 0))
        (XOp.and.eval (XOp.eq.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0)
          (I.getD (rd s.M rPb + BitVec.ofNat 64 w).toNat 0)) (rd s.M rF)) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [cmpWord, semXIR, runPrims, List.foldl, Prim.run, rKc, rAd, rPa, rPb, rKa, rKb, rG,
    rH, rF]
  simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
    rd_set_ne]
  rfl

theorem wf_cmpWord (w : ℕ) : WF (cmpWord w) := by
  simp [cmpWord, WF, Prim.dst, rKc, rAd, rKa, rKb, rG, rH, rF]

theorem cmpWord_frame (I : Array Word) (s : St) (hM : Inv s.M) (w : ℕ) {r : ℕ}
    (hr : r = rPa ∨ r = rPb) : rd (semXIR I (cmpWord w) s).M r = rd s.M r :=
  frame I _ s (wf_cmpWord w) hM r (by rcases hr with rfl | rfl <;> decide) (by
    rcases hr with rfl | rfl <;>
      simp [cmpWord, Writes, Prim.dst, rKc, rAd, rKa, rKb, rG, rH, rF, rPa, rPb, cTmp])

theorem aposIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {d q : ℕ}
    (hdq : (d = rPa ∧ q = rX) ∨ (d = rPb ∧ q = rY)) :
    rd (semXIR I (aposIR d q) s).M d = aposW I (rd s.M q) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  rcases hdq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [aposIR, ceil8Ps, semXIR, runPrims, List.foldl, List.cons_append, List.nil_append,
      Prim.run, rKc, rT2, rQL, rPa, rPb, rX, rY, cOne] at h1 ⊢
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
      rd_set_ne, h1]
    simp only [aposW, ceil8, XOp.eval]
    rfl

theorem wf_aposIR {d q : ℕ} (hd : d = rPa ∨ d = rPb) : WF (aposIR d q) := by
  rcases hd with rfl | rfl <;> simp [aposIR, ceil8Ps, WF, Prim.dst, rQL, rKc, rT2, rPa, rPb]

theorem aposIR_frame (I : Array Word) (s : St) (hM : Inv s.M) {d q r : ℕ}
    (hd : d = rPa ∨ d = rPb) (hr : r ∈ [rX, rY, rPa, rPb, rSrc, rI, rJ]) (hrd : r ≠ d) :
    rd (semXIR I (aposIR d q) s).M r = rd s.M r := by
  refine frame I _ s (wf_aposIR hd) hM r ?_ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hd with rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [aposIR, ceil8Ps, Writes, Prim.dst, rQL, rKc, rT2, rPa, rPb, rX, rY, rSrc, rI, rJ]

/-- **The comparison**: `rF := keyLt I x y` for `x = src[i]`, `y = src[j]`. -/
theorem cmpIR_sem (I : Array Word) (s : St) (hM : Inv s.M)
    (hi : regs ≤ (rd s.M rSrc + rd s.M rI).toNat) (hj : regs ≤ (rd s.M rSrc + rd s.M rJ).toNat) :
    rd (semXIR I cmpIR s).M rF = bW (keyLt I (rd s.M (rd s.M rSrc + rd s.M rI).toNat)
      (rd s.M (rd s.M rSrc + rd s.M rJ).toNat)) := by
  set x := rd s.M (rd s.M rSrc + rd s.M rI).toNat
  set y := rd s.M (rd s.M rSrc + rd s.M rJ).toNat
  have hs := hM.1
  simp only [regs] at hs hi hj
  -- the two loads
  have h4 : rd (semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s)))).M rX = x ∧
      rd (semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s)))).M rY = y := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, XOp.eval, rAd, rX, rY, rSrc, rI, rJ, x,
      y] at hi hj ⊢
    constructor <;>
      simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
        rd_set_ne]
  have hM4 : Inv (semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s)))).M :=
    inv_sem I (P := .load rY rAd) (by simp [WF, rY]) (inv_sem I (by simp [WF, Prim.dst, rAd])
      (inv_sem I (P := .load rX rAd) (by simp [WF, rX]) (inv_sem I (by simp [WF, Prim.dst, rAd])
        hM)))
  rw [cmpIR, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq]
  generalize semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s))) = s4 at h4 hM4
  obtain ⟨hx4, hy4⟩ := h4
  -- the answer positions
  rw [semXIR_seq]
  have hM5 := inv_sem I (wf_aposIR (q := rX) (.inl rfl)) hM4
  have ha5 := aposIR_sem I s4 hM4 (.inl ⟨rfl, rfl⟩)
  have hx5 := aposIR_frame I s4 hM4 (q := rX) (.inl rfl) (r := rX) (by simp) (by decide)
  have hy5 := aposIR_frame I s4 hM4 (q := rX) (.inl rfl) (r := rY) (by simp) (by decide)
  generalize semXIR I (aposIR rPa rX) s4 = s5 at hM5 ha5 hx5 hy5
  rw [semXIR_seq]
  have hM6 := inv_sem I (wf_aposIR (q := rY) (.inr rfl)) hM5
  have hb6 := aposIR_sem I s5 hM5 (.inr ⟨rfl, rfl⟩)
  have ha6 := aposIR_frame I s5 hM5 (q := rY) (.inr rfl) (r := rPa) (by simp) (by decide)
  have hx6 := aposIR_frame I s5 hM5 (q := rY) (.inr rfl) (r := rX) (by simp) (by decide)
  have hy6 := aposIR_frame I s5 hM5 (q := rY) (.inr rfl) (r := rY) (by simp) (by decide)
  generalize semXIR I (aposIR rPb rY) s5 = s6 at hM6 hb6 ha6 hx6 hy6
  -- the position comparison
  rw [semXIR_seq]
  have hs6 := hM6.1
  simp only [regs] at hs6
  have hf7 : rd (semXIR I (.blk [.op .ltu rF rX rY]) s6).M rF = bW (lexW [x] [y]) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, rF, rX, rY] at hx6 hy6 hx5 hy5 hx4 hy4 ⊢
    rw [rd_set_self (by omega), hx6, hy6, hx5, hy5, hx4, hy4]
    by_cases h : x < y <;> simp [XOp.eval, bW, lexW, h]
  have hwf7 : WF (.blk [.op .ltu rF rX rY]) := by simp [WF, Prim.dst, rF]
  have hM7 := inv_sem I hwf7 hM6
  have hfr7 : ∀ r, r = rPa ∨ r = rPb → rd (semXIR I (.blk [.op .ltu rF rX rY]) s6).M r =
      rd s6.M r := fun r hr => frame I _ s6 hwf7 hM6 r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;> simp [Writes, Prim.dst, rF, rPa, rPb])
  have ha7 := hfr7 rPa (.inl rfl)
  have hb7 := hfr7 rPb (.inr rfl)
  generalize semXIR I (.blk [.op .ltu rF rX rY]) s6 = s7 at hf7 hM7 ha7 hb7
  -- the four answer words
  have step : ∀ (s' : St), Inv s'.M → rd s'.M rPa = aposW I x → rd s'.M rPb = aposW I y →
      ∀ (w : ℕ) (p : Bool), w < 4 → rd s'.M rF = bW p →
      rd (semXIR I (cmpWord w) s').M rF = bW (decide (I.getD (aposW I x + BitVec.ofNat 64 w).toNat 0 <
          I.getD (aposW I y + BitVec.ofNat 64 w).toNat 0) ||
        (decide (I.getD (aposW I x + BitVec.ofNat 64 w).toNat 0 =
          I.getD (aposW I y + BitVec.ofNat 64 w).toNat 0) && p)) ∧
      Inv (semXIR I (cmpWord w) s').M ∧ rd (semXIR I (cmpWord w) s').M rPa = aposW I x ∧
      rd (semXIR I (cmpWord w) s').M rPb = aposW I y := fun s' hM' ha hb w p hw hf =>
    ⟨by rw [cmpWord_sem I s' hM' w (by omega), ha, hb, hf, fold_bW],
     inv_sem I (wf_cmpWord w) hM', by rw [cmpWord_frame I s' hM' w (.inl rfl), ha],
     by rw [cmpWord_frame I s' hM' w (.inr rfl), hb]⟩
  rw [ha6, ha5, hx4] at ha7
  rw [hb6, hy5, hy4] at hb7
  rw [semXIR_seq]
  obtain ⟨f3, m3, a3, b3⟩ := step s7 hM7 ha7 hb7 3 _ (by decide) hf7
  generalize semXIR I (cmpWord 3) s7 = s8 at f3 m3 a3 b3
  rw [semXIR_seq]
  obtain ⟨f2, m2, a2, b2⟩ := step s8 m3 a3 b3 2 _ (by decide) f3
  generalize semXIR I (cmpWord 2) s8 = s9 at f2 m2 a2 b2
  rw [semXIR_seq]
  obtain ⟨f1, m1, a1, b1⟩ := step s9 m2 a2 b2 1 _ (by decide) f2
  generalize semXIR I (cmpWord 1) s9 = s10 at f1 m1 a1 b1
  obtain ⟨f0, -, -, -⟩ := step s10 m1 a1 b1 0 _ (by decide) f1
  rw [f0]
  rfl

end FR.X
