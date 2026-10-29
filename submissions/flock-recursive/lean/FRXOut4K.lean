-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.7; stage S-H4, pass 11, item 2: the
-- aggregate's segment count on the machine). 3.x has no aggregate.
import FRXOut4E

/-!
# The aggregate's segment count on the machine (`kSelIR`)

Aggregate `a`'s segment count is `kSel κ a w` (`FRXOut4`): the first sub-slot `i < maxK` whose three
activity selectors do not sum to `1`, else `maxK`. The selectors are decoded cells (rows 1–3), so
after the decode each is two heap words at `wAddr`. `F` addition is coefficientwise XOR, so the
sum is `1` iff the XOR of the low words is `1` and that of the high words `0` (**`sum3_one`**).

**`kSelIR κ a maxK`** keeps a flag `alive` (all sub-slots so far selected) and adds it to the count
`qK` per sub-slot (**`kSelIR_sem`**: `qK = kSel κ a w`; **`kc_find`**: the running count is the
first failing index).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Specification -/

/-- Selector `ι` of aggregate `a`'s sub-slot `i`: its cell's heap address. -/
def selA (κ : NodeKind) (a i : ℕ) (ι : Kind) : ℕ := wAddr κ (κ.oneCell + selR (N4c.sub κ a i) ι)

/-- The flag and the count: `qS0 := (Σ low = 1) ∧ (Σ high = 0)`, `alive &&= qS0`, `qK += alive`. -/
def kPs : List Prim :=
  [.op .xor qS0 qS0 qS2, .op .xor qS0 qS0 qS4, .op .xor qS1 qS1 qS3, .op .xor qS1 qS1 qS5,
   .op .eq qS0 qS0 cOne, .const oK 0, .op .eq qS1 qS1 oK, .op .and qS0 qS0 qS1, .op .and qAl qAl qS0,
   .op .add qK qK qAl]

/-- **Sub-slot `i`'s step**: the three selectors' six words, then `kPs`. -/
def kStep (κ : NodeKind) (a i : ℕ) : XIR :=
  .seq (ldA qS0 (selA κ a i .L32)) (.seq (ldA qS1 (selA κ a i .L32 + 1))
  (.seq (ldA qS2 (selA κ a i .P30)) (.seq (ldA qS3 (selA κ a i .P30 + 1))
  (.seq (ldA qS4 (selA κ a i .N30)) (.seq (ldA qS5 (selA κ a i .N30 + 1)) (.blk kPs))))))

/-- **The segment count over the first `n` sub-slots** (`alive := 1`, `qK := 0`, then the steps). -/
def kSelIR (κ : NodeKind) (a : ℕ) : ℕ → XIR
  | 0 => .blk [.const qAl 1, .const qK 0]
  | i + 1 => .seq (kSelIR κ a i) (kStep κ a i)

/-- The running count: per index, `1` while every flag so far holds. -/
def kc (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => kc p i + if (List.range (i + 1)).all p then 1 else 0

/-! ## The count, purely -/

theorem kc_find (p : ℕ → Bool) : ∀ n, kc p n = ((List.range n).find? fun i => !p i).getD n
  | 0 => rfl
  | n + 1 => by
    rw [kc, kc_find p n, List.range_succ, List.find?_append, List.all_append]
    cases h : (List.range n).find? fun i => !p i with
    | some j =>
      have hj := List.find?_some h
      have hjm := List.mem_range.1 (List.mem_of_find?_eq_some h)
      have ha : (List.range n).all p = false := by
        rw [List.all_eq_false]; exact ⟨j, List.mem_range.2 hjm, by simpa using hj⟩
      simp [ha]
    | none =>
      have ha : (List.range n).all p = true := by
        rw [List.all_eq_true]; intro x hx
        have := List.find?_eq_none.1 h x hx
        simpa using this
      cases hp : p n <;> simp [ha, hp]

/-! ## Proof helpers: words -/

theorem F_one_iff (u v : Word) : (⟨wB u, wB v⟩ : F) = 1 ↔ u = 1 ∧ v = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun x : F => x.c₀.val.toBitVec) h
    have h2 := congrArg (fun x : F => x.c₁.val.toBitVec) h
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- **Three selectors sum to `1`** iff the low words XOR to `1` and the high words to `0`. -/
theorem sum3_one (M : Mem) (a b c : ℕ) :
    rdF M a + rdF M b + rdF M c = 1 ↔
      (rd M a ^^^ rd M b ^^^ rd M c = 1 ∧ rd M (a + 1) ^^^ rd M (b + 1) ^^^ rd M (c + 1) = 0) :=
  F_one_iff _ _

theorem ite_and_w (A B : Prop) [Decidable A] [Decidable B] :
    XOp.and.eval (if A then (1 : Word) else 0) (if B then 1 else 0) = if A ∧ B then 1 else 0 := by
  by_cases a : A <;> by_cases b : B <;> simp [a, b, XOp.eval]

theorem eq_w (x y : Word) : XOp.eq.eval x y = if x = y then 1 else 0 := rfl

/-! ## The step -/

/-- The step's invariant after `i` sub-slots. -/
structure KInv (M₀ : Mem) (p : ℕ → Bool) (i : ℕ) (t : St) : Prop where
  of : OF M₀ t
  al : rd t.M qAl = if (List.range i).all p then 1 else 0
  k : rd t.M qK = toWord (kc p i)

/-- **One sub-slot**: its flag is `p i` when the heap's selector words are the cells'. -/
theorem kStep_sem (I : Array Word) (κ : NodeKind) (a i : ℕ) {M₀ : Mem} {p : ℕ → Bool}
    (hA : ∀ ι, regs ≤ selA κ a i ι ∧ selA κ a i ι + 1 < bufB)
    (hp : p i = decide (rdF M₀ (selA κ a i .L32) + rdF M₀ (selA κ a i .P30) + rdF M₀ (selA κ a i .N30) = 1))
    (hi : kc p i < 2 ^ 32) {t : St} (h : KInv M₀ p i t) :
    (semXIR I (kStep κ a i) t).o = t.o ∧ KInv M₀ p (i + 1) (semXIR I (kStep κ a i) t) := by
  have hs := h.of.inv.1
  simp only [regs] at hs
  have hA' : ∀ ι, regs ≤ selA κ a i ι + 1 ∧ selA κ a i ι + 1 < 2 ^ 64 ∧ selA κ a i ι < 2 ^ 64 :=
    fun ι => ⟨by have := (hA ι).1; omega, by have := (hA ι).2; simp only [bufB] at this; omega,
      by have := (hA ι).2; simp only [bufB] at this; omega⟩
  have L := fun (d : ℕ) (adr : ℕ) (t : St) (h1 : 4 ≤ d) (h2 : d < regs) (h3 : d ≠ oAd) (h4 : regs ≤ adr)
    (h5 : adr < 2 ^ 64) (hO : OF M₀ t) => ldA_sem I (a := adr) h1 h2 h3 h4 h5 hO
  rw [kStep, semXIR_seq]
  obtain ⟨x0, o0, O0, k0⟩ := L qS0 _ t (by decide) (by decide) (by decide) (hA .L32).1 (hA' .L32).2.2 h.of
  generalize semXIR I (ldA qS0 (selA κ a i .L32)) t = t0 at x0 o0 O0 k0
  rw [semXIR_seq]
  obtain ⟨x1, o1, O1, k1⟩ := L qS1 _ t0 (by decide) (by decide) (by decide) (hA' .L32).1 (hA' .L32).2.1 O0
  generalize semXIR I (ldA qS1 (selA κ a i .L32 + 1)) t0 = t1 at x1 o1 O1 k1
  rw [semXIR_seq]
  obtain ⟨x2, o2, O2, k2⟩ := L qS2 _ t1 (by decide) (by decide) (by decide) (hA .P30).1 (hA' .P30).2.2 O1
  generalize semXIR I (ldA qS2 (selA κ a i .P30)) t1 = t2 at x2 o2 O2 k2
  rw [semXIR_seq]
  obtain ⟨x3, o3, O3, k3⟩ := L qS3 _ t2 (by decide) (by decide) (by decide) (hA' .P30).1 (hA' .P30).2.1 O2
  generalize semXIR I (ldA qS3 (selA κ a i .P30 + 1)) t2 = t3 at x3 o3 O3 k3
  rw [semXIR_seq]
  obtain ⟨x4, o4, O4, k4⟩ := L qS4 _ t3 (by decide) (by decide) (by decide) (hA .N30).1 (hA' .N30).2.2 O3
  generalize semXIR I (ldA qS4 (selA κ a i .N30)) t3 = t4 at x4 o4 O4 k4
  rw [semXIR_seq]
  obtain ⟨x5, o5, O5, k5⟩ := L qS5 _ t4 (by decide) (by decide) (by decide) (hA' .N30).1 (hA' .N30).2.1 O4
  generalize semXIR I (ldA qS5 (selA κ a i .N30 + 1)) t4 = t5 at x5 o5 O5 k5
  -- the six words
  have w0 : rd t5.M qS0 = rd M₀ (selA κ a i .L32) := by
    rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide), k3 _ (by decide) (by decide),
      k2 _ (by decide) (by decide), k1 _ (by decide) (by decide), x0,
      h.of.low _ (hA .L32).1 (by have := (hA .L32).2; omega)]
  have w1 : rd t5.M qS1 = rd M₀ (selA κ a i .L32 + 1) := by
    rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide), k3 _ (by decide) (by decide),
      k2 _ (by decide) (by decide), x1, O0.low _ (hA' .L32).1 (hA .L32).2]
  have w2 : rd t5.M qS2 = rd M₀ (selA κ a i .P30) := by
    rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), x2,
      O1.low _ (hA .P30).1 (by have := (hA .P30).2; omega)]
  have w3 : rd t5.M qS3 = rd M₀ (selA κ a i .P30 + 1) := by
    rw [k5 _ (by decide) (by decide), k4 _ (by decide) (by decide), x3, O2.low _ (hA' .P30).1 (hA .P30).2]
  have w4 : rd t5.M qS4 = rd M₀ (selA κ a i .N30) := by
    rw [k5 _ (by decide) (by decide), x4, O3.low _ (hA .N30).1 (by have := (hA .N30).2; omega)]
  have w5 : rd t5.M qS5 = rd M₀ (selA κ a i .N30 + 1) := by
    rw [x5, O4.low _ (hA' .N30).1 (hA .N30).2]
  have kt : ∀ r, r ∉ [qS0, qS1, qS2, qS3, qS4, qS5, oAd] → rd t5.M r = rd t.M r := fun r hr => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    rw [k5 _ hr.2.2.2.2.2.1 hr.2.2.2.2.2.2, k4 _ hr.2.2.2.2.1 hr.2.2.2.2.2.2, k3 _ hr.2.2.2.1 hr.2.2.2.2.2.2,
      k2 _ hr.2.2.1 hr.2.2.2.2.2.2, k1 _ hr.2.1 hr.2.2.2.2.2.2, k0 _ hr.1 hr.2.2.2.2.2.2]
  have al5 : rd t5.M qAl = if (List.range i).all p then 1 else 0 := by rw [kt _ (by decide)]; exact h.al
  have kk5 : rd t5.M qK = toWord (kc p i) := by rw [kt _ (by decide)]; exact h.k
  have hs5 := O5.inv.1
  simp only [regs] at hs5
  rw [semXIR_blk]
  have hall : (List.range (i + 1)).all p = ((List.range i).all p && p i) := by
    rw [List.range_succ, List.all_append]; simp
  have hpi : (p i = true) ↔ (rd M₀ (selA κ a i .L32) ^^^ rd M₀ (selA κ a i .P30) ^^^ rd M₀ (selA κ a i .N30) = 1 ∧
      rd M₀ (selA κ a i .L32 + 1) ^^^ rd M₀ (selA κ a i .P30 + 1) ^^^ rd M₀ (selA κ a i .N30 + 1) = 0) := by
    rw [hp, decide_eq_true_iff]; exact sum3_one M₀ _ _ _
  have av : rd (runPrims kPs t5.M) qAl = if (List.range (i + 1)).all p then 1 else 0 := by
    simp only [kPs, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qS0, qS1, qS2, qS3, qS4, qS5, qAl, qK, oK, cOne]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [w0, w1, w2, w3, w4, w5, al5, one_cOne O5.inv, eq_w, eq_w]
    simp only [XOp.eval]
    rw [hall]
    by_cases ha : (List.range i).all p = true <;> by_cases hq : p i = true
    · have := hpi.1 hq; simp [ha, hq, this.1, this.2]
    · have : ¬ (_ ∧ _) := fun h' => hq (hpi.2 h'); simp only [ha, hq] at *
      by_cases e1 : rd M₀ (selA κ a i .L32) ^^^ rd M₀ (selA κ a i .P30) ^^^ rd M₀ (selA κ a i .N30) = 1 <;>
        by_cases e2 : rd M₀ (selA κ a i .L32 + 1) ^^^ rd M₀ (selA κ a i .P30 + 1) ^^^ rd M₀ (selA κ a i .N30 + 1) = 0 <;>
        simp_all
    · simp [ha]
    · simp [ha]
  refine ⟨by simp only [o5, o4, o3, o2, o1, o0], of_loK I (P := .blk kPs)
    (by simp [kPs, LoK, Prim.dst, regs, qS0, qS1, qAl, qK, oK]) (by simp [kPs, WF, Prim.dst, qS0, qS1, qAl, qK, oK]) O5,
    av, ?_⟩
  have e : rd (runPrims kPs t5.M) qK = XOp.add.eval (rd t5.M qK) (rd (runPrims kPs t5.M) qAl) := by
    simp only [kPs, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qS0, qS1, qS2, qS3, qS4, qS5, qAl, qK, oK, cOne]; omega)) only
      [rd_set_self, rd_set_ne]
  rw [e, av, kk5, kc]
  split_ifs
  · rw [add_one_toWord]
  · simp [XOp.eval]

/-- **The count after `n` sub-slots** is `kc` of the flags (`alive` its running conjunction). -/
theorem kSelIR_run (I : Array Word) (κ : NodeKind) (a : ℕ) {M₀ : Mem} {p : ℕ → Bool} {N : ℕ} (hN : N < 2 ^ 32)
    (hA : ∀ i < N, ∀ ι, regs ≤ selA κ a i ι ∧ selA κ a i ι + 1 < bufB)
    (hp : ∀ i < N, p i = decide (rdF M₀ (selA κ a i .L32) + rdF M₀ (selA κ a i .P30) + rdF M₀ (selA κ a i .N30) = 1)) :
    ∀ n, n ≤ N → ∀ {t : St}, OF M₀ t →
      (semXIR I (kSelIR κ a n) t).o = t.o ∧ KInv M₀ p n (semXIR I (kSelIR κ a n) t)
  | 0, _, t, hO => by
    have hs := hO.inv.1
    simp only [regs] at hs
    refine ⟨rfl, of_loK I (P := .blk [.const qAl 1, .const qK 0]) (by simp [LoK, Prim.dst, regs, qAl, qK])
      (by simp [WF, Prim.dst, qAl, qK]) hO, ?_, ?_⟩
    all_goals simp only [kSelIR, semXIR_blk, runPrims, List.foldl, Prim.run]
    all_goals simp (disch := (simp only [size_set, qAl, qK]; omega)) only [rd_set_self, rd_set_ne]
    all_goals first | rfl | (simp [kc]; done) | (simp [kc]; rfl)
  | n + 1, hn, t, hO => by
    obtain ⟨o1, h1⟩ := kSelIR_run I κ a hN hA hp n (by omega) hO
    have hkc : kc p n ≤ n := by
      clear o1 h1 hO
      induction n with
      | zero => simp [kc]
      | succ m ih => rw [kc]; split_ifs <;> omega
    rw [kSelIR, semXIR_seq]
    obtain ⟨o2, h2⟩ := kStep_sem I κ a n (hA n (by omega)) (hp n (by omega)) (by omega) h1
    exact ⟨o2.trans o1, h2⟩

/-- **`kSelIR` computes `kSel`**: on a heap whose selector words are the witness's cells, after
`kSelIR κ a maxK` register `qK` holds aggregate `a`'s segment count. -/
theorem kSelIR_sem (I : Array Word) (κ : NodeKind) (a : ℕ) {M₀ : Mem} {w : Circ.Asg}
    (hA : ∀ i < κ.maxK, ∀ ι, regs ≤ selA κ a i ι ∧ selA κ a i ι + 1 < bufB)
    (hw : ∀ i < κ.maxK, ∀ ι, rdF M₀ (selA κ a i ι) = w (κ.oneCell + selR (N4c.sub κ a i) ι)) {t : St}
    (hO : OF M₀ t) :
    (semXIR I (kSelIR κ a κ.maxK) t).o = t.o ∧ OF M₀ (semXIR I (kSelIR κ a κ.maxK) t) ∧
      rd (semXIR I (kSelIR κ a κ.maxK) t).M qK = toWord (kSel κ a w) := by
  have hm : κ.maxK < 2 ^ 32 := by cases κ <;> decide
  obtain ⟨o, h⟩ := kSelIR_run I κ a (p := fun i => decide ((selSum κ (N4c.sub κ a i)).ev w = 1)) hm hA
    (fun i hi => by rw [selSum_ev, ← hw i hi, ← hw i hi, ← hw i hi]) κ.maxK le_rfl hO
  refine ⟨o, h.of, ?_⟩
  rw [h.k, kc_find, kSel]
  simp only [decide_not]

end FR.X
