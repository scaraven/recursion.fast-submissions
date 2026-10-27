-- New for `flock-recursive` (BLUEPRINT §6.5 `index_spec`; stage S-H2, track L-ext).
import FRXMerge

/-!
# Simulating the merge sort: `stepIR` by `mstep`, `passIR` by `passF`, `sortIR` by `passes_ok`

* Word-level facts: the branch-free `min` (`minW_toWord`), the `eq`/`ltu` flags.
* `Rel S D n w src M σ`: the registers hold the pass state `σ : MS` (`Regs`), the heap holds the
  source at `S + ·` and `σ.dst` at `D + ·` on `[0, n)`; `Lay` is the pass layout.
* `blockIR_sem`, `choose_sem`, `tail_sem`, **`stepIR_sem`**: one step is `mstep (keyLt I)`.
* **`passIR_sem`**: a pass writes `passF` of the source into the destination, swaps the bases and
  sets `w := min(2w, n)`.
* **`sortIR_sem`**: 64 passes leave `X[0..n)` strictly sorted by `keyLt` and holding exactly the
  initial (distinct) values (`passes_ok`).
* **`idxIR_sorted`**: on a domain tape of a SNARK proof, after `idxIR` `X[0..|L|)` holds exactly
  the log entries' tape positions, sorted by (answer, position).

(S-H2-RESULT, Parts 5 and 6.)
-/

namespace FR.X

open RecursionFast

/-- The branch-free `min` of `minPs`: `b ^^^ ((a ^^^ b) &&& (0 - [a < b]))`. -/
theorem minW (a b : Word) :
    b ^^^ ((a ^^^ b) &&& (0 - XOp.ltu.eval a b)) = if a < b then a else b := by
  by_cases h : a < b
  · have h1 : (0 : Word) - 1 = BitVec.allOnes 64 := by decide
    simp only [XOp.eval, h, ↓reduceIte, h1, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm b a, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  · simp only [XOp.eval, h, ↓reduceIte, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]

/-- `min` of two small numbers as words. -/
theorem minW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    toWord b ^^^ ((toWord a ^^^ toWord b) &&& (0 - XOp.ltu.eval (toWord a) (toWord b))) =
      toWord (min a b) := by
  rw [minW]
  by_cases h : a < b
  · rw [if_pos ((toWord_lt_toWord ha hb).2 h), Nat.min_eq_left h.le]
  · rw [if_neg (fun h' => h ((toWord_lt_toWord ha hb).1 h')), Nat.min_eq_right (by omega)]

/-- The `eq` flag on small numbers. -/
theorem eqW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.eq.eval (toWord a) (toWord b) = bW (decide (a = b)) := by
  simp only [XOp.eval, bW]
  by_cases h : a = b
  · simp [h]
  · rw [if_neg (fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_toWord ha, toNat_toWord hb] at this))]
    simp [h]

/-- The `ltu` flag on small numbers. -/
theorem ltW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.ltu.eval (toWord a) (toWord b) = bW (decide (a < b)) := by
  simp only [XOp.eval, bW, toWord_lt_toWord ha hb]
  by_cases h : a < b <;> simp [h]


/-! ## Word helpers -/

theorem add_toWord (a b : ℕ) : XOp.add.eval (toWord a) (toWord b) = toWord (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem or_self_eval (x : Word) : XOp.or.eval x x = x := BitVec.or_self

/-- `minPs` as the machine evaluates it. -/
theorem minP_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.xor.eval (toWord b) (XOp.and.eval (XOp.xor.eval (toWord a) (toWord b))
      (XOp.sub.eval 0 (XOp.ltu.eval (toWord a) (toWord b)))) = toWord (min a b) :=
  minW_toWord ha hb

theorem bW_and (p q : Bool) : XOp.and.eval (bW p) (bW q) = bW (p && q) := by
  cases p <;> cases q <;> decide

theorem bW_ne_zero : bW true ≠ 0 := by decide

theorem bW_false : bW false = 0 := rfl

/-! ## The heap frame of store-free, loop-free code -/

/-- No store, no loop, every destination a register. -/
def Lo : XIR → Prop
  | .blk ps => ∀ p ∈ ps, p.dst < regs
  | .load d _ => d < regs
  | .input d _ => d < regs
  | .out _ => True
  | .seq p q => Lo p ∧ Lo q
  | .ite _ p q => Lo p ∧ Lo q
  | _ => False

/-- **Heap frame**: such code leaves every cell `≥ regs` alone. -/
theorem hframe (I : Array Word) : ∀ (P : XIR) (s : St), Lo P → ∀ x, regs ≤ x →
    rd (semXIR I P s).M x = rd s.M x
  | .blk _, _, h, _, hx => rd_runPrims_of_not_writes (fun p hp he => by have := h p hp; omega) _
  | .load _ _, _, h, _, hx => rd_set_ne (by simp only [Lo] at h; omega)
  | .input _ _, _, h, _, hx => rd_set_ne (by simp only [Lo] at h; omega)
  | .out _, _, _, _, _ => rfl
  | .seq p q, s, h, x, hx => (hframe I q _ h.2 x hx).trans (hframe I p s h.1 x hx)
  | .ite _ p q, s, h, x, hx => by
    simp only [semXIR]; split
    · exact hframe I q s h.2 x hx
    · exact hframe I p s h.1 x hx
  | .store .., _, h, _, _ => h.elim
  | .loopK .., _, h, _, _ => h.elim
  | .loopT .., _, h, _, _ => h.elim

/-- Controls for `Lo`: a store, or a block writing a heap cell, is not `Lo`. -/
theorem not_lo_store : ¬ Lo (.store rAd rV) := id

theorem not_lo_heap : ¬ Lo (.blk [.const regs 0]) := by simp [Lo, Prim.dst]

/-! ## The relation between the machine and `MS` -/

/-- The nine registers of a merge pass. -/
def regL : List ℕ := [rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst]

/-- The registers hold `σ`'s indices and the pass parameters `S`, `D` (the bases), `n`, `w`. -/
structure Regs (M : Mem) (S D n w : ℕ) (σ : MS) : Prop where
  i : rd M rI = toWord σ.i
  iE : rd M rIE = toWord σ.iE
  j : rd M rJ = toWord σ.j
  jE : rd M rJE = toWord σ.jE
  k : rd M rKk = toWord σ.k
  w : rd M rW2 = toWord w
  n : rd M rN = toWord n
  S : rd M rSrc = toWord S
  D : rd M rDst = toWord D

theorem Regs.frame {M M' : Mem} {S D n w : ℕ} {σ : MS} (h : Regs M S D n w σ)
    (hf : ∀ r ∈ regL, rd M' r = rd M r) : Regs M' S D n w σ where
  i := (hf rI (by simp [regL])).trans h.i
  iE := (hf rIE (by simp [regL])).trans h.iE
  j := (hf rJ (by simp [regL])).trans h.j
  jE := (hf rJE (by simp [regL])).trans h.jE
  k := (hf rKk (by simp [regL])).trans h.k
  w := (hf rW2 (by simp [regL])).trans h.w
  n := (hf rN (by simp [regL])).trans h.n
  S := (hf rSrc (by simp [regL])).trans h.S
  D := (hf rDst (by simp [regL])).trans h.D

theorem regL_lt : ∀ r ∈ regL, r < regs := by decide

theorem Regs.sem {I : Array Word} {P : XIR} {s : St} {S D n w : ℕ} {σ : MS}
    (h : Regs s.M S D n w σ) (hM : Inv s.M) (hP : WF P) (hw : ∀ r ∈ regL, ¬ Writes P r) :
    Regs (semXIR I P s).M S D n w σ :=
  h.frame fun r hr => FR.X.frame I P s hP hM r (regL_lt r hr) (hw r hr)

/-- The indices stay in range. -/
def Bnd (n : ℕ) (σ : MS) : Prop := σ.i ≤ σ.iE ∧ σ.j ≤ σ.jE ∧ σ.iE ≤ n ∧ σ.jE ≤ n

/-- The layout of a pass: source at `S`, destination at `D`, disjoint heap ranges of `n` cells. -/
structure Lay (S D n w sz : ℕ) : Prop where
  rS : regs ≤ S
  rD : regs ≤ D
  sS : S + n ≤ sz
  sD : D + n ≤ sz
  disj : S + n ≤ D ∨ D + n ≤ S
  bS : S + n < 2 ^ 64
  bD : D + n < 2 ^ 64
  bn : 3 * n + 2 < 2 ^ 64
  bw : w ≤ n + 1
  pw : 0 < n → 0 < w

/-- **The simulation relation**: the machine's memory holds the pass state `σ`. -/
structure Rel (S D n w : ℕ) (src : ℕ → Word) (M : Mem) (σ : MS) : Prop where
  inv : Inv M
  rg : Regs M S D n w σ
  hs : ∀ a < n, rd M (S + a) = src a
  hd : ∀ a < n, rd M (D + a) = σ.dst a
  bnd : Bnd n σ

theorem bstart_props {n w : ℕ} {σ : MS} (hB : Bnd n σ) (hk : σ.k < n) (hw : 0 < w) :
    (bstart n w σ).k = σ.k ∧ (bstart n w σ).dst = σ.dst ∧ Bnd n (bstart n w σ) ∧
      ((bstart n w σ).i < (bstart n w σ).iE ∨ (bstart n w σ).j < (bstart n w σ).jE) := by
  unfold bstart Bnd at *
  split
  · refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only <;> omega
  · exact ⟨rfl, rfl, by omega, by omega⟩

/-! ## `blockIR` -/

theorem lo_blockIR : Lo blockIR := by
  simp [Lo, blockIR, minPs, Prim.dst, regs, rG, rH, rI, rIE, rJ, rJE, rKk, rV, rT1, rT2, rKc]

theorem wf_blockIR : WF blockIR := by
  simp [WF, blockIR, minPs, Prim.dst, rG, rH, rI, rIE, rJ, rJE, rKk, rV, rT1, rT2, rKc]

/-- **`blockIR` computes `bstart`.** -/
theorem blockIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w : ℕ} {σ : MS}
    (hR : Regs s.M S D n w σ) (hB : Bnd n σ) (hk : σ.k < n) (hn : 3 * n + 2 < 2 ^ 64)
    (hw : w ≤ n + 1) : Regs (semXIR I blockIR s).M S D n w (bstart n w σ) := by
  have hs := hM.1
  simp only [regs] at hs
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hwf1 : WF (.blk [.op .eq rG rI rIE, .op .eq rH rJ rJE, .op .and rG rG rH]) := by
    simp [WF, Prim.dst, rG, rH]
  have h1 : rd (semXIR I (.blk [.op .eq rG rI rIE, .op .eq rH rJ rJE, .op .and rG rG rH]) s).M
      rG = bW (decide (σ.i = σ.iE) && decide (σ.j = σ.jE)) := by
    have hi := hR.i; have hiE := hR.iE; have hj := hR.j; have hjE := hR.jE
    simp only [semXIR, runPrims, List.foldl, Prim.run, rG, rH, rI, rIE, rJ, rJE] at hi hiE hj hjE ⊢
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
      rd_set_ne]
    rw [hi, hiE, hj, hjE, eqW_toWord (by omega) (by omega), eqW_toWord (by omega) (by omega),
      bW_and]
  have hR1 := hR.sem (I := I) hM hwf1 (by simp [regL, Writes, Prim.dst, rG, rH, rI, rIE, rJ,
    rJE, rKk, rW2, rN, rSrc, rDst])
  have hM1 := inv_sem I hwf1 hM
  rw [blockIR, semXIR_seq, semXIR_ite]
  generalize semXIR I (.blk [.op .eq rG rI rIE, .op .eq rH rJ rJE, .op .and rG rG rH]) s = s1
    at h1 hR1 hM1
  unfold bstart
  by_cases hc : σ.i = σ.iE ∧ σ.j = σ.jE
  · rw [if_pos hc, h1, decide_eq_true hc.1, decide_eq_true hc.2]
    rw [Bool.and_self, if_neg bW_ne_zero]
    have hs1 := hM1.1
    simp only [regs] at hs1
    obtain ⟨i1, iE1, j1, jE1, k1, w1, n1, S1, D1⟩ := hR1
    simp only [rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst] at i1 iE1 j1 jE1 k1 w1 n1 S1 D1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [semXIR, minPs, runPrims, List.foldl, List.cons_append, List.nil_append,
      Prim.run, rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst, rV, rT1, rT2,
      rKc] <;>
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) only [rd_set_self,
      rd_set_ne] <;>
    simp only [i1, iE1, j1, jE1, k1, w1, n1, S1, D1, or_self_eval, add_toWord] <;>
    simp (disch := omega) only [minP_toWord, add_toWord, or_self_eval]
  · rw [if_neg hc, h1, show (decide (σ.i = σ.iE) && decide (σ.j = σ.jE)) = false by simpa using hc,
      if_pos bW_false]
    exact hR1


/-! ## `stepIR`, piece by piece -/

/-- The run flags. -/
def flagsIR : XIR := .blk [.op .ltu rG rI rIE, .op .ltu rH rJ rJE]
/-- The choice: `rF := takeL`. -/
def chooseIR : XIR := .ite rG (.ite rH cmpIR (.blk [.const rF 1])) (.blk [.const rF 0])
/-- The head that goes next: its address in `rAd`, the head advanced. -/
def advIR : XIR := .ite rF (.blk [.op .add rAd rSrc rI, .op .add rI rI cOne])
  (.blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne])
/-- The write `dst[k] := src[h]`, `k += 1`. -/
def tailIR : XIR :=
  .seq (.load rV rAd) (.seq (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne]) (.store rAd rV))

theorem stepIR_eq : stepIR = .seq blockIR (.seq flagsIR (.seq chooseIR (.seq advIR tailIR))) :=
  rfl

theorem add_one_toWord (a : ℕ) : XOp.add.eval (toWord a) 1 = toWord (a + 1) :=
  (BitVec.ofNat_add a 1).symm

/-- **The choice** leaves `takeL` in `rF`. -/
theorem choose_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w : ℕ} {src : ℕ → Word}
    {τ : MS} (hR : Regs s.M S D n w τ) (hrS : regs ≤ S) (hbS : S + n < 2 ^ 64) (hB : Bnd n τ)
    (hsrc : ∀ a < n, rd s.M (S + a) = src a)
    (hG : rd s.M rG = bW (decide (τ.i < τ.iE))) (hH : rd s.M rH = bW (decide (τ.j < τ.jE))) :
    rd (semXIR I chooseIR s).M rF = bW (takeL (keyLt I) src τ) := by
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hs := hM.1
  simp only [regs] at hs hrS
  rw [chooseIR, semXIR_ite]
  by_cases g : τ.i < τ.iE
  · rw [hG, decide_eq_true g, if_neg bW_ne_zero, semXIR_ite]
    by_cases h : τ.j < τ.jE
    · rw [hH, decide_eq_true h, if_neg bW_ne_zero]
      have ha : ∀ a < n, regs ≤ (rd s.M rSrc + toWord a).toNat ∧
          rd s.M (rd s.M rSrc + toWord a).toNat = src a := fun a ha => by
        rw [hR.S, toWord_add, toNat_toWord (by omega), hsrc a ha]
        exact ⟨by simp only [regs]; omega, rfl⟩
      rw [cmpIR_sem I s hM (by rw [hR.i]; exact (ha _ (by omega)).1)
        (by rw [hR.j]; exact (ha _ (by omega)).1), hR.i, hR.j, (ha _ (by omega)).2,
        (ha _ (by omega)).2]
      simp [takeL, g, h]
    · rw [hH, decide_eq_false h, if_pos bW_false]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [rF]; omega)]
      simp [takeL, g, h, bW]
  · rw [hG, decide_eq_false g, if_pos bW_false]
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rF]; omega)]
    simp [takeL, g, bW]

theorem lo_cmpIR : Lo cmpIR := by
  simp [Lo, cmpIR, cmpWord, aposIR, ceil8Ps, Prim.dst, regs, rAd, rX, rY, rPa, rPb, rKa, rKb, rF,
    rG, rH, rQL, rKc, rT2]

theorem wf_cmpIR : WF cmpIR := by
  simp [WF, cmpIR, cmpWord, aposIR, ceil8Ps, Prim.dst, rAd, rX, rY, rPa, rPb, rKa, rKb, rF,
    rG, rH, rQL, rKc, rT2]

/-- **The write**: `dst[k] := src[h]`, `k += 1`; the source and the other registers stay. -/
theorem tail_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w h : ℕ} {src : ℕ → Word}
    {τ : MS} (hL : Lay S D n w s.M.size) (hR : Regs s.M S D n w τ) (hk : τ.k < n) (hh : h < n)
    (hA : rd s.M rAd = toWord (S + h)) (hsrc : ∀ a < n, rd s.M (S + a) = src a)
    (hdst : ∀ a < n, rd s.M (D + a) = τ.dst a) :
    Inv (semXIR I tailIR s).M ∧
    Regs (semXIR I tailIR s).M S D n w { τ with k := τ.k + 1, dst := upd τ.dst τ.k (src h) } ∧
    (∀ a < n, rd (semXIR I tailIR s).M (S + a) = src a) ∧
    (∀ a < n, rd (semXIR I tailIR s).M (D + a) = upd τ.dst τ.k (src h) a) := by
  have hs := hM.1
  have hc1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  obtain ⟨Lr, Ld, LsS, LsD, Ldj, LbS, LbD, -, -, -⟩ := hL
  simp only [regs] at hs Lr Ld
  have e : semXIR I tailIR s = semXIR I (.store rAd rV) (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s) := rfl
  have hwf2 : WF (.seq (.load rV rAd) (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) := by
    simp [WF, Prim.dst, rV, rAd, rKk]
  have hM2 := inv_sem I hwf2 hM
  have hH2 := hframe I (.seq (.load rV rAd) (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne]))
    s (by simp [Lo, Prim.dst, regs, rV, rAd, rKk])
  have hz2 := size_sem I (.seq (.load rV rAd) (.blk [.op .add rAd rDst rKk,
    .op .add rKk rKk cOne])) s
  have hF2 : ∀ r ∈ [rI, rIE, rJ, rJE, rW2, rN, rSrc, rDst], rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M r = rd s.M r := fun r hr =>
    frame I _ s hwf2 hM r (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr;
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr;
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Writes, Prim.dst, rV, rAd, rKk, rI, rIE, rJ, rJE, rW2, rN, rSrc, rDst])
  have hA2 : rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M rAd = toWord (D + τ.k) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rAd, rKk, rV]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hR.D, hR.k, add_toWord]
  have hK2 : rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M rKk = toWord (τ.k + 1) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rAd, rKk, rV]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hR.k, hc1, add_one_toWord]
  have hV2 : rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M rV = src h := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rAd, rKk, rV]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hA, toNat_toWord (by omega), hsrc h hh]
  rw [e]
  generalize semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s = s2 at hM2 hH2 hz2 hF2 hA2 hK2 hV2
  have hst : ∀ i, i ≠ cTmp → rd (semXIR I (.store rAd rV) s2).M i =
      if i = D + τ.k then src h else rd s2.M i := fun i hi => by
    rw [← hV2]
    exact rd_storeM hM2 hA2 (by simp only [regs]; omega) (by omega) (by omega) (by decide)
      (by decide) hi
  have hreg : ∀ r ∈ [rI, rIE, rJ, rJE, rW2, rN, rSrc, rDst],
      rd (semXIR I (.store rAd rV) s2).M r = rd s.M r := fun r hr => by
    have h1 : r < regs ∧ r ≠ cTmp := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hst r h1.2, if_neg (by simp only [regs] at h1; omega), hF2 r hr]
  refine ⟨inv_sem I (P := .store rAd rV) (by simp [WF, rAd, cTmp]) hM2,
    ⟨(hreg rI (by simp)).trans hR.i, (hreg rIE (by simp)).trans hR.iE,
      (hreg rJ (by simp)).trans hR.j, (hreg rJE (by simp)).trans hR.jE, ?_,
      (hreg rW2 (by simp)).trans hR.w, (hreg rN (by simp)).trans hR.n,
      (hreg rSrc (by simp)).trans hR.S, (hreg rDst (by simp)).trans hR.D⟩,
    fun a ha => ?_, fun a ha => ?_⟩
  · rw [hst rKk (by decide), if_neg (by simp only [rKk]; omega), hK2]
  · rw [hst _ (by simp only [cTmp]; omega), if_neg (by omega), hH2 _ (by simp only [regs]; omega),
      hsrc a ha]
  · rw [hst _ (by simp only [cTmp]; omega)]
    by_cases hak : a = τ.k
    · subst hak; rw [if_pos rfl]; simp [upd]
    · rw [if_neg (by omega), hH2 _ (by simp only [regs]; omega), hdst a ha]
      simp [upd, hak]


/-- **`advIR`** for a head register `r ∈ {rI, rJ}` holding `h`: `rAd := S + h`, `r := h + 1`. -/
theorem adv_blk (I : Array Word) (s : St) (hM : Inv s.M) {S h : ℕ} {r : ℕ} (hr : r = rI ∨ r = rJ)
    (hS : rd s.M rSrc = toWord S) (hh : rd s.M r = toWord h) :
    rd (semXIR I (.blk [.op .add rAd rSrc r, .op .add r r cOne]) s).M rAd = toWord (S + h) ∧
    rd (semXIR I (.blk [.op .add rAd rSrc r, .op .add r r cOne]) s).M r = toWord (h + 1) ∧
    ∀ q ∈ regL, q ≠ r → rd (semXIR I (.blk [.op .add rAd rSrc r, .op .add r r cOne]) s).M q =
      rd s.M q := by
  have hs := hM.1
  have hc1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have hr' : r < 256 ∧ r ≠ rAd ∧ r ≠ cOne := by rcases hr with rfl | rfl <;> decide
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_, fun q hq hqr => ?_⟩
  · rw [rd_set_ne hr'.2.1, rd_set_self (by simp only [rAd]; omega), hS, hh, add_toWord]
  · rw [rd_set_self (by simp only [size_set]; omega), rd_set_ne (Ne.symm hr'.2.1),
      rd_set_ne (by decide : rAd ≠ cOne), hc1, hh, add_one_toWord]
  · have hq' : q ≠ rAd := by
      simp only [regL, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [rd_set_ne (Ne.symm hqr), rd_set_ne (Ne.symm hq')]

theorem lo_flagsIR : Lo flagsIR := by simp [Lo, flagsIR, Prim.dst, regs, rG, rH]
theorem wf_flagsIR : WF flagsIR := by simp [WF, flagsIR, Prim.dst, rG, rH]
theorem lo_chooseIR : Lo chooseIR := by
  simp only [Lo, chooseIR]; exact ⟨⟨lo_cmpIR, by simp [Prim.dst, regs, rF]⟩,
    by simp [Prim.dst, regs, rF]⟩
theorem wf_chooseIR : WF chooseIR := by
  simp only [WF, chooseIR]; exact ⟨⟨wf_cmpIR, by simp [Prim.dst, rF]⟩, by simp [Prim.dst, rF]⟩
theorem lo_advIR : Lo advIR := by simp [Lo, advIR, Prim.dst, regs, rAd, rI, rJ]
theorem wf_advIR : WF advIR := by simp [WF, advIR, Prim.dst, rAd, rI, rJ]

theorem nw_flagsIR : ∀ r ∈ regL, ¬ Writes flagsIR r := by
  simp [regL, Writes, flagsIR, Prim.dst, rG, rH, rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst]

theorem nw_chooseIR : ∀ r ∈ regL, ¬ Writes chooseIR r := by
  simp [regL, Writes, chooseIR, cmpIR, cmpWord, aposIR, ceil8Ps, Prim.dst, rAd, rX, rY, rPa, rPb,
    rKa, rKb, rF, rG, rH, rQL, rKc, rT2, rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst]

/-- **One step**: `stepIR` maps a state holding `σ` to one holding `mstep σ`. -/
theorem stepIR_sem (I : Array Word) (s : St) {S D n w : ℕ} {src : ℕ → Word} {σ : MS}
    (hL : Lay S D n w s.M.size) (hR : Rel S D n w src s.M σ) (hk : σ.k < n) :
    Rel S D n w src (semXIR I stepIR s).M (mstep (keyLt I) src n w σ) ∧
      (mstep (keyLt I) src n w σ).k = σ.k + 1 := by
  obtain ⟨hM, hRg, hsrc, hdst, hB⟩ := hR
  obtain ⟨tk, tdst, tB, tav⟩ := bstart_props hB hk (hL.pw (by omega))
  have hR1 := blockIR_sem I s hM hRg hB hk hL.bn hL.bw
  have hM1 := inv_sem I wf_blockIR hM
  have hH1 := hframe I _ s lo_blockIR
  have hz1 := size_sem I blockIR s
  have Lr := hL.rS
  have Ld := hL.rD
  have LbS := hL.bS
  have Lbn := hL.bn
  simp only [regs] at Lr Ld
  simp only [mstep]
  rw [stepIR_eq, semXIR_seq]
  generalize bstart n w σ = τ at tk tdst tB tav hR1
  generalize semXIR I blockIR s = s1 at hR1 hM1 hH1 hz1
  obtain ⟨b1, b2, b3, b4⟩ := tB
  -- the flags
  have hfl : rd (semXIR I flagsIR s1).M rG = bW (decide (τ.i < τ.iE)) ∧
      rd (semXIR I flagsIR s1).M rH = bW (decide (τ.j < τ.jE)) := by
    have hs1 := hM1.1
    simp only [regs] at hs1
    simp only [flagsIR, semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rG, rH]; omega)) only [rd_set_self,
      rd_set_ne]
    · rw [hR1.i, hR1.iE, ltW_toWord (by omega) (by omega)]
    · rw [hR1.j, hR1.jE, ltW_toWord (by omega) (by omega)]
  have hR2 := hR1.sem (I := I) hM1 wf_flagsIR nw_flagsIR
  have hM2 := inv_sem I wf_flagsIR hM1
  have hH2 := hframe I _ s1 lo_flagsIR
  have hz2 := size_sem I flagsIR s1
  rw [semXIR_seq]
  generalize semXIR I flagsIR s1 = s2 at hfl hR2 hM2 hH2 hz2
  -- the choice
  have hsrc2 : ∀ a < n, rd s2.M (S + a) = src a := fun a ha => by
    rw [hH2 _ (by simp only [regs]; omega), hH1 _ (by simp only [regs]; omega), hsrc a ha]
  have hF := choose_sem I s2 hM2 hR2 hL.rS LbS ⟨b1, b2, b3, b4⟩ hsrc2 hfl.1 hfl.2
  have hR3 := hR2.sem (I := I) hM2 wf_chooseIR nw_chooseIR
  have hM3 := inv_sem I wf_chooseIR hM2
  have hH3 := hframe I _ s2 lo_chooseIR
  have hz3 := size_sem I chooseIR s2
  rw [semXIR_seq]
  generalize semXIR I chooseIR s2 = s3 at hF hR3 hM3 hH3 hz3
  have hsrc3 : ∀ a < n, rd s3.M (S + a) = src a := fun a ha => by
    rw [hH3 _ (by simp only [regs]; omega), hsrc2 a ha]
  have hdst3 : ∀ a < n, rd s3.M (D + a) = τ.dst a := fun a ha => by
    rw [hH3 _ (by simp only [regs]; omega), hH2 _ (by simp only [regs]; omega),
      hH1 _ (by simp only [regs]; omega), hdst a ha, tdst]
  have hL3 : Lay S D n w s3.M.size := by rw [hz3, hz2, hz1]; exact hL
  -- the write
  rw [semXIR_seq, advIR, semXIR_ite, hF]
  by_cases hT : takeL (keyLt I) src τ = true
  · have hi : τ.i < τ.iE := by simp [takeL] at hT; exact hT.1
    rw [hT, if_neg bW_ne_zero, if_pos rfl]
    obtain ⟨a1, a2, a3⟩ := adv_blk I s3 hM3 (.inl rfl) hR3.S hR3.i
    have hR4 : Regs (semXIR I (.blk [.op .add rAd rSrc rI, .op .add rI rI cOne]) s3).M S D n w
        { τ with i := τ.i + 1 } := ⟨a2, (a3 rIE (by simp [regL]) (by decide)).trans hR3.iE,
      (a3 rJ (by simp [regL]) (by decide)).trans hR3.j,
      (a3 rJE (by simp [regL]) (by decide)).trans hR3.jE,
      (a3 rKk (by simp [regL]) (by decide)).trans hR3.k,
      (a3 rW2 (by simp [regL]) (by decide)).trans hR3.w,
      (a3 rN (by simp [regL]) (by decide)).trans hR3.n,
      (a3 rSrc (by simp [regL]) (by decide)).trans hR3.S,
      (a3 rDst (by simp [regL]) (by decide)).trans hR3.D⟩
    have hP : Lo (.blk [.op .add rAd rSrc rI, .op .add rI rI cOne]) := by
      simp [Lo, Prim.dst, regs, rAd, rI]
    have hM4 := inv_sem I (P := .blk [.op .add rAd rSrc rI, .op .add rI rI cOne])
      (by simp [WF, Prim.dst, rAd, rI]) hM3
    obtain ⟨t1, t2, t3, t4⟩ := tail_sem I _ hM4 (by rw [size_sem]; exact hL3) hR4
      (by show τ.k < n; omega)
      (h := τ.i) (by omega) a1 (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; omega),
        hsrc3 a ha]) (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; omega),
        hdst3 a ha])
    exact ⟨⟨t1, t2, t3, t4, ⟨by show τ.i + 1 ≤ τ.iE; omega, b2, b3, b4⟩⟩, by simp only; omega⟩
  · have hj : τ.j < τ.jE := by
      by_contra hj
      apply hT
      simp only [takeL, hj, decide_false, Bool.not_false, Bool.true_or, Bool.and_true,
        decide_eq_true_eq]
      omega
    rw [Bool.not_eq_true] at hT
    rw [hT, if_pos bW_false, if_neg (by simp)]
    obtain ⟨a1, a2, a3⟩ := adv_blk I s3 hM3 (.inr rfl) hR3.S hR3.j
    have hR4 : Regs (semXIR I (.blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne]) s3).M S D n w
        { τ with j := τ.j + 1 } := ⟨(a3 rI (by simp [regL]) (by decide)).trans hR3.i,
      (a3 rIE (by simp [regL]) (by decide)).trans hR3.iE, a2,
      (a3 rJE (by simp [regL]) (by decide)).trans hR3.jE,
      (a3 rKk (by simp [regL]) (by decide)).trans hR3.k,
      (a3 rW2 (by simp [regL]) (by decide)).trans hR3.w,
      (a3 rN (by simp [regL]) (by decide)).trans hR3.n,
      (a3 rSrc (by simp [regL]) (by decide)).trans hR3.S,
      (a3 rDst (by simp [regL]) (by decide)).trans hR3.D⟩
    have hP : Lo (.blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne]) := by
      simp [Lo, Prim.dst, regs, rAd, rJ]
    have hM4 := inv_sem I (P := .blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne])
      (by simp [WF, Prim.dst, rAd, rJ]) hM3
    obtain ⟨t1, t2, t3, t4⟩ := tail_sem I _ hM4 (by rw [size_sem]; exact hL3) hR4
      (by show τ.k < n; omega)
      (h := τ.j) (by omega) a1 (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; omega),
        hsrc3 a ha]) (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; omega),
        hdst3 a ha])
    exact ⟨⟨t1, t2, t3, t4, ⟨b1, by show τ.j + 1 ≤ τ.jE; omega, b3, b4⟩⟩, by simp only; omega⟩


/-! ## The pass -/

theorem regL_ne {c : ℕ} (hc : c ∉ regL) : ∀ r ∈ regL, c ≠ r := fun _ hr he => hc (he ▸ hr)

/-- A write to a counter outside `regL` and below `regs` keeps the relation. -/
theorem Rel.set {S D n w : ℕ} {src : ℕ → Word} {M : Mem} {σ : MS} (h : Rel S D n w src M σ)
    {c : ℕ} (hc : c ∉ regL) (hc4 : 4 ≤ c) (hcr : c < regs) (hS : regs ≤ S) (hD : regs ≤ D)
    (v : Word) : Rel S D n w src (M.setIfInBounds c v) σ where
  inv := inv_of_frame h.inv (size_set ..) fun i hi => rd_set_ne (by omega)
  rg := h.rg.frame fun r hr => rd_set_ne (regL_ne hc r hr)
  hs := fun a ha => (rd_set_ne (by omega)).trans (h.hs a ha)
  hd := fun a ha => (rd_set_ne (by omega)).trans (h.hd a ha)
  bnd := h.bnd

theorem Rel.decS {S D n w : ℕ} {src : ℕ → Word} {s : St} {σ : MS}
    (h : Rel S D n w src s.M σ) (hS : regs ≤ S) (hD : regs ≤ D) :
    Rel S D n w src (decS rCS s).M σ :=
  h.set (by decide) (by decide) (by decide) hS hD _

/-- **`n − k` steps** of the pass's loop run `mrun`. -/
theorem stepLoop (I : Array Word) {S D n w : ℕ} {src : ℕ → Word} :
    ∀ (m : ℕ) (s : St) (σ : MS), Lay S D n w s.M.size → Rel S D n w src s.M σ → σ.k + m = n →
      Rel S D n w src (iterL (semXIR I stepIR) rCS m s).M (mrun (keyLt I) src n w m σ)
  | 0, _, _, _, hR, _ => hR
  | m + 1, s, σ, hL, hR, hm => by
    obtain ⟨h1, h2⟩ := stepIR_sem I s hL hR (by omega)
    simp only [iterL, mrun]
    exact stepLoop I m _ _ (by rw [size_decS, size_sem]; exact hL) (h1.decS hL.rS hL.rD)
      (by rw [h2]; omega)

/-- **One pass**: the destination holds `passF` of the source; the bases swap and
`w := min(2w, n)`. -/
theorem passIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w : ℕ}
    (hL : Lay S D n w s.M.size) (hn : I.getD posL 0 = toWord n)
    (hS : rd s.M rSrc = toWord S) (hD : rd s.M rDst = toWord D) (hW : rd s.M rW2 = toWord w)
    (hN : rd s.M rN = toWord n) :
    Inv (semXIR I passIR s).M ∧ rd (semXIR I passIR s).M rSrc = toWord D ∧
    rd (semXIR I passIR s).M rDst = toWord S ∧
    rd (semXIR I passIR s).M rW2 = toWord (min (2 * w) n) ∧ rd (semXIR I passIR s).M rN = toWord n ∧
    ∀ a < n, rd (semXIR I passIR s).M (D + a) =
      passF (keyLt I) (fun a => rd s.M (S + a)) n w (fun a => rd s.M (D + a)) a := by
  have hs := hM.1
  have Lbn := hL.bn
  have Lbw := hL.bw
  simp only [regs] at hs
  have hP0 : WF passPre := by simp [passPre, readAt, WF, Prim.dst, rI, rIE, rJ, rJE, rKk, rNS, rA]
  have hlo0 : Lo passPre := by
    simp [Lo, passPre, readAt, Prim.dst, regs, rI, rIE, rJ, rJE, rKk, rNS, rA]
  have hcnt : rd (semXIR I passPre s).M rNS = toWord n := by
    rw [passPre, rd_seq_readAt I _ s (by simp [WF, Prim.dst, rI, rIE, rJ, rJE, rKk]) hM
      (by decide) (by simp only [posL]; omega), hn]
  have hR0 : Regs (semXIR I passPre s).M S D n w ⟨0, 0, 0, 0, 0, 0, fun a => rd s.M (D + a)⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [passPre, readAt, semXIR, runPrims, List.foldl, Prim.run] <;>
    simp (disch := first | decide | (simp only [size_set, rI, rIE, rJ, rJE, rKk, rNS, rA]; omega))
      only [rd_set_self, rd_set_ne] <;>
    first | exact hW | exact hN | exact hS | exact hD | rfl
  have hM0 := inv_sem I hP0 hM
  have hH0 := hframe I _ s hlo0
  have hz0 := size_sem I passPre s
  rw [passIR, semXIR_seq, semXIR_seq]
  generalize semXIR I passPre s = s0 at hcnt hR0 hM0 hH0 hz0
  have hs0 := hM0.1
  simp only [regs] at hs0
  have e : semXIR I (.loopT rCS rNS ⟨0, 1, 5⟩ stepIR) s0 =
      iterL (semXIR I stepIR) rCS n ⟨entryT rCS rNS s0.M, s0.o⟩ := by
    simp only [semXIR, rd_entryT (show rCS < s0.M.size by simp only [rCS]; omega), hcnt,
      toNat_toWord (show n < 2 ^ 64 by omega)]
  rw [e]
  have hRel : Rel S D n w (fun a => rd s.M (S + a)) (entryT rCS rNS s0.M)
      ⟨0, 0, 0, 0, 0, 0, fun a => rd s.M (D + a)⟩ :=
    Rel.set (M := s0.M) ⟨hM0, hR0, fun a ha => hH0 _ (le_trans hL.rS (by omega)),
      fun a ha => hH0 _ (le_trans hL.rD (by omega)), by simp [Bnd]⟩ (by decide) (by decide)
      (by decide) hL.rS hL.rD _
  have h1 := stepLoop I n ⟨entryT rCS rNS s0.M, s0.o⟩ _ (by rw [size_entryT, hz0]; exact hL) hRel
    (by simp)
  generalize iterL (semXIR I stepIR) rCS n ⟨entryT rCS rNS s0.M, s0.o⟩ = s1 at h1
  obtain ⟨hM1, hR1, -, hd1, -⟩ := h1
  have hs1 := hM1.1
  simp only [regs] at hs1
  have hlo : Lo (.blk swapPs) := by
    simp [Lo, swapPs, minPs, Prim.dst, regs, rV, rSrc, rDst, rW2, rT1, rT2, rKc]
  refine ⟨inv_sem I (by simp [WF, swapPs, minPs, Prim.dst, rV, rSrc, rDst, rW2, rT1, rT2, rKc])
    hM1, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  rotate_left 4
  · rw [hframe I _ s1 hlo _ (le_trans hL.rD (by omega)), hd1 a ha]; rfl
  all_goals
    simp only [swapPs, minPs, semXIR, runPrims, List.foldl, List.cons_append, List.nil_append,
      Prim.run]
    simp (disch := first | decide | (simp only [size_set, rV, rSrc, rDst, rW2, rT1, rT2, rKc]; omega))
      only [rd_set_self, rd_set_ne]
    simp only [hR1.S, hR1.D, hR1.w, hR1.n, or_self_eval, add_toWord]
  rw [minP_toWord (by omega) (by omega), two_mul]


/-! ## The sort: 64 passes -/

theorem iterL_succ' (f : St → St) (c : ℕ) :
    ∀ (k : ℕ) (s : St), iterL f c (k + 1) s = decS c (f (iterL f c k s))
  | 0, _ => rfl
  | k + 1, s => iterL_succ' f c k (decS c (f s))

theorem wseq_le (n : ℕ) : ∀ p, wseq n p ≤ n + 1
  | 0 => by simp [wseq]
  | p + 1 => by simp only [wseq]; omega

theorem wseq_pos {n : ℕ} (hn : 0 < n) (p : ℕ) : 0 < wseq n p := by
  rw [wseq_eq hn]; exact lt_min (Nat.two_pow_pos p) hn

/-- The source base of pass `p`: `X` on even passes, `Y = X + n` on odd ones. -/
def baseX (n p : ℕ) : ℕ := if p % 2 = 0 then memX else memX + n

theorem baseX_ctl (n : ℕ) : baseX n 0 = memX ∧ baseX n 1 = memX + n := ⟨rfl, rfl⟩

theorem baseX_two (n p : ℕ) : baseX n (p + 1 + 1) = baseX n p := by
  unfold baseX
  by_cases h : p % 2 = 0
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- The count of the sort's loop. -/
theorem entryK64 {M : Mem} (hM : Inv M) (hN : rd M rNP = 64) :
    rd (entryK rCP rNP 64 M) rCP = 64 := by
  have hs := hM.1
  simp only [regs] at hs
  unfold entryK
  dsimp only
  have h1 : rd (M.setIfInBounds rCP 64) rNP = 64 := by rw [rd_set_ne (by decide), hN]
  have h2 : rd (M.setIfInBounds rCP 64) rCP = 64 := rd_set_self (by simp only [rCP]; omega)
  rw [h1, h2, rd_set_self (by simp only [size_set, cTmp]; omega)]
  rw [if_pos (by decide), rd_set_ne (by decide), h2]

/-- **The sort's semantics**: on a heap whose `X[0..n)` holds distinct words, `sortIR` leaves in
`X[0..n)` exactly those words, strictly sorted by `keyLt`. -/
theorem sortIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n : ℕ}
    (hn : I.getD posL 0 = toWord n) (hn2 : n < 2 ^ 62) (hsz : memX + n + n ≤ s.M.size)
    (hinj : ∀ a b, a < n → b < n → rd s.M (memX + a) = rd s.M (memX + b) → a = b) :
    (∀ a b, a < b → b < n →
      keyLt I (rd (semXIR I sortIR s).M (memX + a)) (rd (semXIR I sortIR s).M (memX + b)) = true) ∧
    (∀ a < n, ∃ c < n, rd (semXIR I sortIR s).M (memX + a) = rd s.M (memX + c)) ∧
    (∀ c < n, ∃ a < n, rd (semXIR I sortIR s).M (memX + a) = rd s.M (memX + c)) := by
  have hs := hM.1
  have hm : memX = 2 ^ 26 := rfl
  simp only [regs] at hs
  have hP0 : WF sortPre := by simp [sortPre, readAt, WF, Prim.dst, rN, rA, rW2, rSrc, rDst, rNP]
  have hlo0 : Lo sortPre := by
    simp [Lo, sortPre, readAt, Prim.dst, regs, rN, rA, rW2, rSrc, rDst, rNP]
  -- the registers after `sortPre`
  have h0 : rd (semXIR I sortPre s).M rN = toWord n ∧ rd (semXIR I sortPre s).M rW2 = toWord 1 ∧
      rd (semXIR I sortPre s).M rSrc = toWord memX ∧
      rd (semXIR I sortPre s).M rDst = toWord (memX + n) ∧ rd (semXIR I sortPre s).M rNP = 64 := by
    have hN := rd_readAt I s hM (d := rN) (pos := posL) (by decide) (by simp only [posL]; omega)
    have hM' := inv_sem I (P := readAt rN posL) (by simp [readAt, WF, Prim.dst, rN, rA]) hM
    rw [hn] at hN
    rw [sortPre, semXIR_seq]
    generalize semXIR I (readAt rN posL) s = s' at hN hM'
    have hs' := hM'.1
    simp only [regs] at hs'
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rN, rW2, rSrc, rDst, rNP]; omega)) only
      [rd_set_self, rd_set_ne]
    · exact hN
    · rfl
    · rfl
    · rw [hN]; exact add_toWord _ _
  have hM0 := inv_sem I hP0 hM
  have hH0 := hframe I _ s hlo0
  have hz0 := size_sem I sortPre s
  rw [sortIR, semXIR_seq]
  generalize semXIR I sortPre s = s0 at h0 hM0 hH0 hz0
  obtain ⟨n0, w0, S0, D0, P0⟩ := h0
  have e : semXIR I (.loopK rCP rNP 64 passIR) s0 =
      iterL (semXIR I passIR) rCP 64 ⟨entryK rCP rNP 64 s0.M, s0.o⟩ := by
    simp only [semXIR, entryK64 hM0 P0]
    rfl
  rw [e]
  have hE : ∀ i, i ≠ rCP → i ≠ cTmp → rd (entryK rCP rNP 64 s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME : Inv (entryK rCP rNP 64 s0.M) := inv_of_frame hM0 (size_entryK ..)
    fun i hi => hE i (by simp only [rCP]; omega) (by simp only [cTmp]; omega)
  generalize hS0 : (⟨entryK rCP rNP 64 s0.M, s0.o⟩ : St) = T at hE hME
  -- the pass invariant
  have hLay : ∀ p, Lay (baseX n p) (baseX n (p + 1)) n (wseq n p) s.M.size := fun p => by
    have := wseq_le n p
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, this, wseq_pos (p := p)⟩ <;>
      unfold baseX <;> simp only [hm, regs] <;> split_ifs <;> omega
  have hPI : ∀ p, Inv (iterL (semXIR I passIR) rCP p T).M ∧
      (iterL (semXIR I passIR) rCP p T).M.size = s.M.size ∧
      rd (iterL (semXIR I passIR) rCP p T).M rSrc = toWord (baseX n p) ∧
      rd (iterL (semXIR I passIR) rCP p T).M rDst = toWord (baseX n (p + 1)) ∧
      rd (iterL (semXIR I passIR) rCP p T).M rW2 = toWord (wseq n p) ∧
      rd (iterL (semXIR I passIR) rCP p T).M rN = toWord n := by
    intro p
    induction p with
    | zero =>
      simp only [iterL]
      rw [← hS0]
      refine ⟨hME, by rw [size_entryK, hz0], ?_, ?_, ?_, ?_⟩
      · rw [hE _ (by decide) (by decide), S0]; simp only [baseX, Nat.zero_mod, if_true]
      · rw [hE _ (by decide) (by decide), D0]; simp only [baseX]; rfl
      · rw [hE _ (by decide) (by decide), w0]; rfl
      · rw [hE _ (by decide) (by decide), n0]
    | succ p ih =>
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih
      obtain ⟨j1, j2, j3, j4, j5, -⟩ := passIR_sem I _ i1 (by rw [i2]; exact hLay p) hn i3 i4 i5 i6
      rw [iterL_succ']
      refine ⟨inv_of_frame j1 (size_decS ..) fun i hi => rd_decS (by simp only [rCP]; omega) _,
        by rw [size_decS, size_sem, i2], ?_, ?_, ?_, ?_⟩
      · rw [rd_decS (by decide), j2]
      · exact (rd_decS (by decide) _).trans (j3.trans (congrArg toWord (baseX_two n p).symm))
      · exact (rd_decS (by decide) _).trans (j4.trans (by simp only [wseq]))
      · rw [rd_decS (by decide), j5]
  have hX : ∀ p, ∀ a < n, rd (iterL (semXIR I passIR) rCP (p + 1) T).M (baseX n (p + 1) + a) =
      passF (keyLt I) (fun a => rd (iterL (semXIR I passIR) rCP p T).M (baseX n p + a)) n (wseq n p)
        (fun a => rd (iterL (semXIR I passIR) rCP p T).M (baseX n (p + 1) + a)) a := fun p a ha => by
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hPI p
    have hL := hLay p
    rw [← i2] at hL
    rw [iterL_succ', rd_decS (by have := hL.rD; simp only [regs, rCP] at *; omega)]
    exact (passIR_sem I _ i1 hL hn i3 i4 i5 i6).2.2.2.2.2 a ha
  have hX0 : ∀ a < n, rd (iterL (semXIR I passIR) rCP 0 T).M (baseX n 0 + a) = rd s.M (memX + a) :=
    fun a ha => by
      simp only [iterL, baseX, Nat.zero_mod, if_true]
      rw [← hS0, hE _ (by simp only [rCP, hm]; omega) (by simp only [cTmp, hm]; omega),
        hH0 _ (by simp only [regs, hm]; omega)]
  obtain ⟨r1, r2, r3⟩ := passes_ok (keyLt_order I) (by omega)
    (fun p a => rd (iterL (semXIR I passIR) rCP p T).M (baseX n p + a))
    (fun p a => rd (iterL (semXIR I passIR) rCP p T).M (baseX n (p + 1) + a)) hX
    (fun a b ha hb h => hinj a b ha hb (by rwa [hX0 a ha, hX0 b hb] at h))
  have hB64 : baseX n 64 = memX := if_pos (by decide)
  simp only [hB64] at r1 r2 r3
  refine ⟨r1, fun a ha => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc, e⟩ := r2 a ha
    exact ⟨c, hc, by rw [e, hX0 c hc]⟩
  · obtain ⟨a, ha, e⟩ := r3 c hc
    exact ⟨a, ha, by rw [e, hX0 c hc]⟩


/-! ## The log index after walk and sort -/

theorem entryOff_lt (L : Log) {a b : ℕ} (h : a < b) (hb : b ≤ L.length) :
    entryOff L a < entryOff L b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rw [entryOff_succ L (by omega)]
    have : 5 ≤ qWords L[b] := Nat.le_add_right _ _
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · have := ih h' (by omega); omega
    · subst h'; omega

/-- **The log index** (`index_spec`, sort half): after `idxIR` (walk and sort) on a domain tape of a SNARK proof,
`X[0..|L|)` holds exactly the tape positions of the log's entries, strictly sorted by the key
(answer, position). -/
theorem idxIR_sorted (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : memX + L.length + L.length ≤ s.M.size) :
    (∀ a b, a < b → b < L.length →
      keyLt (extractorInput c π L).toArray
        (rd (semXIR (extractorInput c π L).toArray idxIR s).M (memX + a))
        (rd (semXIR (extractorInput c π L).toArray idxIR s).M (memX + b)) = true) ∧
    (∀ a < L.length, ∃ k < L.length, rd (semXIR (extractorInput c π L).toArray idxIR s).M
      (memX + a) = toWord (posL + 1 + entryOff L k)) ∧
    (∀ k < L.length, ∃ a < L.length, rd (semXIR (extractorInput c π L).toArray idxIR s).M
      (memX + a) = toWord (posL + 1 + entryOff L k)) := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end c π L hs
  have h5 : 5 * L.length ≤ entryOff L L.length := by
    have := length_logEntries L
    rwa [entries_length, ← entryOff_length] at this
  have hW := fun {k : ℕ} (hk : k < L.length) => walk_spec c π L hs hq ht s hM (by omega) hk
  have hwf : WF walkIR := wf_logIR.1.1
  rw [idxIR, semXIR_seq]
  obtain ⟨r1, r2, r3⟩ := sortIR_sem I (semXIR I walkIR s) (inv_sem I hwf hM) (n := L.length)
    (by rw [hI, getD_toArray, tape_getD_posL c π L hs]) (by omega) (by rw [size_sem]; exact hsz)
    (fun a b ha hb h => by
      rw [hW ha, hW hb] at h
      have hab := congrArg BitVec.toNat h
      have ea : entryOff L a < entryOff L L.length := entryOff_lt L ha le_rfl
      have eb : entryOff L b < entryOff L L.length := entryOff_lt L hb le_rfl
      rw [toNat_toWord (by omega), toNat_toWord (by omega)] at hab
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · have := entryOff_lt L h' hb.le; omega
      · have := entryOff_lt L h' ha.le; omega)
  refine ⟨r1, fun a ha => ?_, fun k hk => ?_⟩
  · obtain ⟨k, hk, e⟩ := r2 a ha
    exact ⟨k, hk, e.trans (hW hk)⟩
  · obtain ⟨a, ha, e⟩ := r3 k hk
    exact ⟨a, ha, e.trans (hW hk)⟩

end FR.X
