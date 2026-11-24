-- New for lvm2 E2F (slice S1, E2F-Q; E2AC-DES §6 statement 14): the `E2` gadget rows of the builder and the
-- proof-of-work range row. Frozen on day 0; proofs E2F-Q's.
import LvmQBuildSem
import LvmTypedLHolds
import LvmDecideBase

/-!
# `E2` gadgets and the proof-of-work range row

* **`C2`**: an `E2` value in the circuit, two `K` cells `(re, im)` (`C2.val`). **`gE2`**: the twin pair
  `e2 f false`, `e2 f true` on the operands' cells (`e2Args`), its value the cells at the pointer `(k, k + 1)`.
  **`gE2mul a b d = a·b + d`**, **`gE2lin k k' a b = a + k·b + k'`**; **`gE2mul_sem`**, **`gE2lin_sem`**: on a
  memory where the segments hold, the output is the `E2` value (statement 14).
* **`powRangeRows g bit v`**: the `BITS`-class auxiliary rows of one ground answer (E2AC-DES §1.4, ARCH-7 §2):
  `64 − g` Boolean rows `b_i·b_i + b_i = 0` and one recomposition row `Σ_i ⟨2^i⟩·b_i + v = 0` (`⟨2^i⟩ = x^i`,
  the word with bit `i`: the bits of `v`'s word in `K`'s polynomial basis). **`powRange_sem`**: if the rows hold
  at an iteration and the bits are free words, `v`'s word is below `2^(64 − g)`, so an answer whose lane 2 is `v` passes `powOK g` (`powOK_of_range`).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

/-- **An `E2` value in the circuit**: two `K` cells, the coordinates on `1` and on `X`. -/
structure C2 where
  /-- The coordinate on `1`. -/
  re : Cell
  /-- The coordinate on `X`. -/
  im : Cell
  deriving DecidableEq, Repr, Inhabited

/-- The `E2` value of a pair of cells in a memory (each cell's constant coefficient). -/
def C2.val (M : Mem) (a : C2) : FE2 := ⟨(a.re.val M).c₀, (a.im.val M).c₀⟩

/-- The `K` operands of `E2` values, `re` then `im` each. -/
def e2Args (xs : List C2) : List Addr := xs.flatMap fun a => [a.re.addr, a.im.addr]

/-- **An `E2` twin pair**: rows `e2 f false`, `e2 f true` on `xs`; the result is the `K` cells `(k, k + 1)` at the
pointer. -/
def gE2 (f : E2Fn) (xs : List C2) : BM C2 := fun p =>
  (⟨kc p.k, kc (p.k + 1)⟩, [.row ⟨.e2 f false, .K, e2Args xs⟩, .row ⟨.e2 f true, .K, e2Args xs⟩])

/-- **`a·b + d` in `E2`.** -/
def gE2mul (a b d : C2) : BM C2 := gE2 .mul [a, b, d]

/-- **`a + k·b + k'` in `E2`** (`k ∈ K`, `k' ∈ E2` constants). -/
def gE2lin (k : FK) (k' : FE2) (a b : C2) : BM C2 := gE2 (.lin k k'.re k'.im) [a, b]

/-- **A twin pair's output** is the `E2` value of its function at its operands. -/
theorem gE2_sem (c : Ctx) (M : Mem) (p : Ptr) (f : E2Fn) (xs : List C2) (h : SegsHold c M p (gE2 f xs p).2) :
    (gE2 f xs p).1.val M = f.val fun o => (M.arg (rowInst p ⟨.e2 f false, .K, e2Args xs⟩) o).c₀ := by
  obtain ⟨h0, h1, -⟩ := h
  have e0 : M.k p.k = (f.val fun o => (M.arg (rowInst p ⟨.e2 f false, .K, e2Args xs⟩) o).c₀).coord false :=
    congrArg FE.c₀ (show M.res (rowInst p ⟨.e2 f false, .K, e2Args xs⟩) = _ from h0)
  have e1 : M.k (p.k + 1) = (f.val fun o => (M.arg (rowInst p ⟨.e2 f false, .K, e2Args xs⟩) o).c₀).coord true :=
    congrArg FE.c₀ (show M.res (rowInst (p.adv [.row ⟨.e2 f false, .K, e2Args xs⟩]) ⟨.e2 f true, .K, e2Args xs⟩) = _
      from h1)
  exact FE2.ext_coord e0 e1

/-- **Statement 14a: the `E2` product row.** On a memory where the gadget's segments hold, its output is `a·b + d`
in `E2`. Owner **E2F-Q**. -/
theorem gE2mul_sem (c : Ctx) (M : Mem) (p : Ptr) (a b d : C2) (h : SegsHold c M p (gE2mul a b d p).2) :
    (gE2mul a b d p).1.val M = a.val M * b.val M + d.val M :=
  gE2_sem c M p .mul [a, b, d] h

/-- **Statement 14b: the `E2` linear row.** On a memory where the gadget's segments hold, its output is
`a + k·b + k'` in `E2`. Owner **E2F-Q**. -/
theorem gE2lin_sem (c : Ctx) (M : Mem) (p : Ptr) (k : FK) (k' : FE2) (a b : C2)
    (h : SegsHold c M p (gE2lin k k' a b p).2) :
    (gE2lin k k' a b p).1.val M = a.val M + FE2.ofK k * b.val M + k' :=
  gE2_sem c M p (.lin k k'.re k'.im) [a, b] h

end Lvm.Loop.Build

namespace Lvm.Typed

open Lvm.Loop

/-- **The proof-of-work range rows** of one ground answer: for each `i < 64 − g` the Boolean row
`bit_i·bit_i + bit_i = 0`, then the recomposition row `Σ_i ⟨2^i⟩·bit_i + v = 0` (`⟨2^i⟩ = x^i`; characteristic 2). -/
def powRangeRows (g : ℕ) (bit : ℕ → AOp) (v : AOp) : List ARow :=
  (List.range (64 - g)).map (fun i ↦ ⟨[(0, bit i, 1), (1, bit i, 1), (2, bit i, 1)]⟩) ++
    [⟨((List.range (64 - g)).map fun i ↦ (2, bit i, FE.ofK ⟨UInt64.ofNat (2 ^ i)⟩)) ++ [(3, v, 1)]⟩]

/-- A Boolean word: `b·b + b = 0` in `K` makes `b` a bit. -/
theorem pr_bit {b : FK} (h : b * b + b = 0) : b = 0 ∨ b = 1 := by
  have h' : b * (b + 1) = 0 := by rw [mul_add, mul_one]; exact h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · right; have := eq_neg_of_add_eq_zero_left h1; rw [this]; rfl

/-- The word with only bit `i` (`i < 64`). -/
theorem pr_pow_val {i : ℕ} (hi : i < 64) : kToNat (⟨UInt64.ofNat (2 ^ i)⟩ : FK) = 2 ^ i := by
  simp only [kToNat, UInt64.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi)

/-- **A sum of distinct powers of `x` times bits is a word below `2^n`.** -/
theorem pr_sum_lt (b : ℕ → FK) (hb : ∀ i, b i = 0 ∨ b i = 1) :
    ∀ n ≤ 64, kToNat (((List.range n).map fun i ↦ (⟨UInt64.ofNat (2 ^ i)⟩ : FK) * b i).sum) < 2 ^ n
  | 0, _ => by simp [kToNat]; rfl
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have ih := pr_sum_lt b hb n (by (clear * - n hn; omega))
    have hpow : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by (clear * - n b; omega))
    rcases hb n with h | h
    · rw [h, mul_zero, add_zero]; exact ih.trans hpow
    · rw [h, mul_one]
      change ((_ : UInt64) ^^^ _).toNat < _
      rw [UInt64.toNat_xor]
      refine Nat.xor_lt_two_pow (ih.trans hpow) ?_
      have := pr_pow_val (i := n) (by (clear * - n b hn; omega))
      simp only [kToNat] at this
      rw [this]; exact hpow

/-- **Statement 14c: the range row.** If the range rows hold at iteration `j`, the bits are free words and `v` is
a `K` value, then `v`'s word is below `2^(64 − g)`. Owner **E2F-Q**. -/
theorem powRange_sem (lay : Lay) (z : ℕ → FK) (j g : ℕ) (hg : g ≤ 64) (bit : ℕ → AOp) (v : AOp)
    (hbit : ∀ i, ∃ b s, bit i = .word b s) (hv : FE.ofK (aopVal lay z j v).c₀ = aopVal lay z j v)
    (h : ∀ r ∈ powRangeRows g bit v, ARowHolds lay z j r) :
    kToNat (aopVal lay z j v).c₀ < 2 ^ (64 - g) := by
  set n := 64 - g with hn
  -- the bits
  have hb : ∀ i < n, ∃ w : FK, aopVal lay z j (bit i) = FE.ofK w ∧ (w = 0 ∨ w = 1) := by
    intro i hi
    obtain ⟨bb, ss, hbi⟩ := hbit i
    have hr := h _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    simp only [ARowHolds, aRowMat, List.filter_cons, List.filter_nil] at hr
    simp only [beq_self_eq_true, if_true, Nat.reduceBEq, Bool.false_eq_true, if_false, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul] at hr
    rw [hbi] at hr ⊢
    refine ⟨z (bb + ss * j), rfl, pr_bit ?_⟩
    have h2 : FE.ofKRingHom (z (bb + ss * j) * z (bb + ss * j) + z (bb + ss * j)) = FE.ofKRingHom 0 := by
      rw [map_add, map_mul, map_zero]; exact hr
    exact congrArg FE.c₀ h2
  choose! w hw hw01 using hb
  -- the recomposition
  have hr := h _ (List.mem_append_right _ (List.mem_singleton_self _))
  simp only [ARowHolds, aRowMat, List.filter_append, List.filter_cons, List.filter_nil] at hr
  simp [List.filter_map, Function.comp_def, List.map_map] at hr
  have hV : aopVal lay z j v = ((List.range n).map fun x ↦
      FE.ofK ⟨UInt64.ofNat (2 ^ x)⟩ * aopVal lay z j (bit x)).sum := (lh_c2 hr).trans rfl
  set b : ℕ → FK := fun i ↦ if i < n then w i else 0 with hbdef
  have hsum : ((List.range n).map fun x ↦ FE.ofK ⟨UInt64.ofNat (2 ^ x)⟩ * aopVal lay z j (bit x)).sum =
      FE.ofKRingHom (((List.range n).map fun x ↦ (⟨UInt64.ofNat (2 ^ x)⟩ : FK) * b x).sum) := by
    rw [map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    have hx' := List.mem_range.mp hx
    simp only [Function.comp_apply, map_mul, hbdef, if_pos hx', hw x hx']
    rfl
  rw [hV, hsum]
  exact pr_sum_lt b (fun i ↦ by
    simp only [hbdef]; split
    · exact hw01 i (by assumption)
    · exact Or.inl rfl) n (by (clear * - n g hg; omega))

/-- **A ground answer whose lane 2 passed the range rows passes `powOK g`** (`powOKR`, V's executable check:
`eToNat c < 2^(192 − g)`). -/
theorem powOK_of_range {g : ℕ} (hg : g ≤ 64) {c : FE} (h : kToNat c.c₂ < 2 ^ (64 - g)) :
    DM.powOKR g c = true := by
  unfold DM.powOKR eToNat
  have h0 : kToNat c.c₀ < 2 ^ 64 := c.c₀.val.toNat_lt
  have h1 : kToNat c.c₁ < 2 ^ 64 := c.c₁.val.toNat_lt
  have he : (2 : ℕ) ^ (192 - g) = 2 ^ 128 * 2 ^ (64 - g) := by rw [← pow_add]; congr 1; (clear * - g hg c; omega)
  rw [he, decide_eq_true_eq]
  generalize (2 : ℕ) ^ (64 - g) = A at h ⊢
  (clear * - c A g h0 h1 h; omega)

end Lvm.Typed
