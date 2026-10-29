-- New for `flock-recursive` (BLUEPRINT §2.3 step 3, A.8 `rsWeight`, A.11; revision 3.16, R-V-M1 (a);
-- stage INT-5).
import FRVIREval

/-!
# RS claim 2's kind factor on the node layout (`rsWeight`, revision 3.16)

R-V-M1, ruling (a): the Lc claim's ring-switching weight carries `W_β`'s kind factor. At Frobenius
stage `k` (`q = p^(2^k)` the claim point's block coordinates, `ρ` the final point's, `β_k =
β^(2^k)`), A.8's pattern-interval sum is

`kwS n β_k q ρ = Σ_{i<8} β_k^i Σ_{t < 2^n} Ind_{κ_i}(t) · eq(q, t) · eq(ρ, t)`,

`κ_i` the node kinds in `blockKinds` order after `chain` (`v_i`'s kind in `finLc`), `Ind_κ` the
union of the kind's intervals in `Layout.nodeLayout`, with `free` extended to `[wmBase, 2^n)`
(`ivsQ`; the complement of the hash blocks). `FRRingSwitch.rsWeight_kind_eq` is the statement that
the Φ form of `eq(p, ·)·B_β` has this extension.

* **Specification** `kwS` (above, over `Fin n` points and `FRSpartan.selOf`).
* **Implementation** `kwI`: per-bit weights `e_l(1) = q_l ρ_l`, `e_l(0) = (1 − q_l)(1 − ρ_l)`, the
  prefix products `Π_{l'<l} (e_{l'}(0) + e_{l'}(1))`, and the prefix sums `pfx` (high bit first,
  one product per bit); each kind is a short list of **items** (`plan`): intervals, single blocks
  and the path runs as a **bit pattern** (the `hashB1` / `hashB2` path blocks alternate, so they
  are the even / odd blocks of a 32-block run: bit 0's weight times a 15-bit range sum). 23 items.
* **`kwI_eq`**: `kwI = kwS` for `n ≥ 16`. The items are checked against `Layout.kindIvs` by
  `planFix_ivs` (a kernel `decide` on the concrete interval lists).
* **`kwS_one`**: `β = 1` gives the plain `eq(q, ρ)`: the kinds partition `[0, 2^n)` (`part_one`).
  A leaf passes `β = 1`, so its claim 2 is unchanged.
* Controls: `kwS_cube` (at a Boolean point the factor is `β^i` of the block's kind), `kwS_hashA`
  (+: `β^3` at `hashStmt`'s block A; −: not the plain weight `1`).
-/

namespace FR
namespace KW
open Finset

/-! ## Product weights and prefix sums -/

section Prefix
variable {R : Type*} [CommRing R]

/-- `Π_{l<n} e_l(bit l of t)`. -/
def prodE (e : ℕ → Bool → R) (n t : ℕ) : R := ∏ l ∈ range n, e l (t.testBit l)

/-- The prefix sum `Σ_{t < x, t < 2^n} Π_l e_l(t_l)`. -/
def psum (e : ℕ → Bool → R) (n x : ℕ) : R :=
  ∑ t ∈ range (2 ^ n), if t < x then prodE e n t else 0

theorem prodE_lo {e : ℕ → Bool → R} {n t : ℕ} (ht : t < 2 ^ n) :
    prodE e (n + 1) t = prodE e n t * e n false := by
  rw [prodE, prod_range_succ, Nat.testBit_lt_two_pow ht]; rfl

theorem prodE_hi {e : ℕ → Bool → R} {n t : ℕ} (ht : t < 2 ^ n) :
    prodE e (n + 1) (2 ^ n + t) = prodE e n t * e n true := by
  rw [prodE, prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ht,
    Bool.not_false]
  refine congrArg (· * e n true) ?_
  exact prod_congr rfl fun l hl ↦ by rw [Nat.testBit_two_pow_add_gt (mem_range.1 hl)]

theorem sum_range_pow_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ t ∈ range (2 ^ (n + 1)), f t =
      ∑ t ∈ range (2 ^ n), f t + ∑ t ∈ range (2 ^ n), f (2 ^ n + t) := by
  rw [pow_succ, mul_two, sum_range_add]

theorem sum_prodE (e : ℕ → Bool → R) (n : ℕ) :
    ∑ t ∈ range (2 ^ n), prodE e n t = ∏ l ∈ range n, (e l false + e l true) := by
  induction n with
  | zero => simp [prodE]
  | succ n ih =>
    rw [sum_range_pow_succ, prod_range_succ, ← ih, mul_add, sum_mul, sum_mul]
    refine congrArg₂ (· + ·) ?_ ?_ <;> refine sum_congr rfl fun t ht ↦ ?_
    · rw [prodE_lo (mem_range.1 ht)]
    · rw [prodE_hi (mem_range.1 ht)]

theorem psum_succ (e : ℕ → Bool → R) (n x : ℕ) :
    psum e (n + 1) x = (∑ t ∈ range (2 ^ n), if t < x then prodE e n t * e n false else 0) +
      ∑ t ∈ range (2 ^ n), if 2 ^ n + t < x then prodE e n t * e n true else 0 := by
  rw [psum, sum_range_pow_succ]
  refine congrArg₂ (· + ·) ?_ ?_ <;> refine sum_congr rfl fun t ht ↦ ?_
  · rw [prodE_lo (mem_range.1 ht)]
  · rw [prodE_hi (mem_range.1 ht)]

/-- **The prefix sum, high bit first**, from the tables `e0 l = e_l(0)`, `e1 l = e_l(1)`,
`sp l = Π_{l'<l} (e_{l'}(0) + e_{l'}(1))`, `lw l = sp l · e_l(0)`: one product per bit. -/
def pfx (e0 e1 lw sp : ℕ → R) : ℕ → ℕ → R
  | 0, x => if 0 < x then 1 else 0
  | n + 1, x =>
    if 2 ^ (n + 1) ≤ x then sp (n + 1)
    else if x.testBit n then lw n + e1 n * pfx e0 e1 lw sp n (x - 2 ^ n)
    else e0 n * pfx e0 e1 lw sp n x

theorem pfx_eq (e : ℕ → Bool → R) (e0 e1 lw sp : ℕ → R) (n : ℕ)
    (h0 : ∀ l < n, e0 l = e l false) (h1 : ∀ l < n, e1 l = e l true)
    (hs : ∀ l ≤ n, sp l = ∏ l' ∈ range l, (e l' false + e l' true))
    (hl : ∀ l < n, lw l = sp l * e l false) (x : ℕ) :
    pfx e0 e1 lw sp n x = psum e n x := by
  induction n generalizing x with
  | zero => rw [psum, pow_zero, sum_range_one]; simp [prodE, pfx]
  | succ n ih =>
    have ih' := ih (fun l h ↦ h0 l (by omega)) (fun l h ↦ h1 l (by omega))
      (fun l h ↦ hs l (by omega)) (fun l h ↦ hl l (by omega))
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ, mul_two]
    rw [pfx, psum_succ]
    split_ifs with hx hb
    · rw [hs _ le_rfl, ← sum_prodE, sum_range_pow_succ]
      refine congrArg₂ (· + ·) ?_ ?_ <;> refine sum_congr rfl fun t ht ↦ ?_
      · rw [if_pos (by have := mem_range.1 ht; omega), prodE_lo (mem_range.1 ht)]
      · rw [if_pos (by have := mem_range.1 ht; omega), prodE_hi (mem_range.1 ht)]
    · have hge : 2 ^ n ≤ x := by
        by_contra h
        rw [Nat.testBit_lt_two_pow (by omega)] at hb
        exact absurd hb (by simp)
      rw [hl n (by omega), hs n (by omega), ← sum_prodE, ih', psum, sum_mul, mul_sum,
        h1 n (by omega)]
      refine congrArg₂ (· + ·) ?_ ?_ <;> refine sum_congr rfl fun t ht ↦ ?_
      · rw [if_pos (by have := mem_range.1 ht; omega)]
      · by_cases h : t < x - 2 ^ n
        · rw [if_pos h, if_pos (by omega)]; ring
        · rw [if_neg h, if_neg (by omega), mul_zero]
    · have hlt : x < 2 ^ n := by
        by_contra h
        have e : x = 2 ^ n + (x - 2 ^ n) := by omega
        rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)] at hb
        exact hb rfl
      rw [ih', psum, mul_sum, h0 n (by omega),
        show (∑ t ∈ range (2 ^ n), if 2 ^ n + t < x then prodE e n t * e n true else 0) = 0 from
          sum_eq_zero fun t _ ↦ if_neg (by omega), add_zero]
      refine sum_congr rfl fun t _ ↦ ?_
      split_ifs <;> ring

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ t ∈ range (2 * m), f t = ∑ u ∈ range m, (f (2 * u) + f (2 * u + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

theorem prodE_even (e : ℕ → Bool → R) (n u : ℕ) :
    prodE e (n + 1) (2 * u) = prodE (fun l ↦ e (l + 1)) n u * e 0 false := by
  rw [prodE, prod_range_succ']
  refine congrArg₂ (· * ·) ?_ ?_
  · exact prod_congr rfl fun l _ ↦ by rw [Nat.testBit_add_one, Nat.mul_div_cancel_left _ two_pos]
  · simp [Nat.testBit_zero]

theorem prodE_odd (e : ℕ → Bool → R) (n u : ℕ) :
    prodE e (n + 1) (2 * u + 1) = prodE (fun l ↦ e (l + 1)) n u * e 0 true := by
  rw [prodE, prod_range_succ']
  refine congrArg₂ (· * ·) ?_ ?_
  · refine prod_congr rfl fun l _ ↦ ?_
    rw [Nat.testBit_add_one, show (2 * u + 1) / 2 = u by omega]
  · simp [Nat.testBit_zero, Nat.add_mod]

end Prefix

/-! ## Items: intervals, single blocks, bit patterns -/

/-- A set of blocks: the interval `[lo, hi)`, the block `c`, or the blocks `t` with bit 0 equal to
`c` and `⌊t/2⌋ ∈ [a, b)` (a run of alternating kinds). -/
inductive Item where
  | iv (lo hi : ℕ)
  | one (c : ℕ)
  | pat (c : Bool) (a b : ℕ)
  deriving DecidableEq, Repr

section Items
variable {R : Type*} [CommRing R]

theorem lsum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, sum_range_succ, ih]

/-- The item's indicator. -/
def Item.ind : Item → ℕ → R
  | .iv lo hi, t => if lo ≤ t ∧ t < hi then 1 else 0
  | .one c, t => if t = c then 1 else 0
  | .pat c a b, t => if t.testBit 0 = c ∧ a ≤ t / 2 ∧ t / 2 < b then 1 else 0

/-- The item as intervals (a pattern as its single blocks). -/
def Item.ivs : Item → List (ℕ × ℕ)
  | .iv lo hi => [(lo, hi)]
  | .one c => [(c, c + 1)]
  | .pat c a b => (List.range (b - a)).map fun u =>
      (2 * (a + u) + c.toNat, 2 * (a + u) + c.toNat + 1)

/-- Ordered bounds. -/
def Item.WF : Item → Prop
  | .iv lo hi => lo ≤ hi
  | .one _ => True
  | .pat _ a b => a ≤ b

instance (it : Item) : Decidable it.WF := by cases it <;> unfold Item.WF <;> infer_instance

/-- **The item's sum, fast**: `P` the prefix sum, `P'` the prefix sum over the bits above bit 0,
`pr` the product at a block, `z0`, `z1` bit 0's weights. -/
def Item.val (P P' pr : ℕ → R) (z0 z1 : R) (n : ℕ) : Item → R
  | .iv lo hi => P hi - P lo
  | .one c => if c < 2 ^ n then pr c else 0
  | .pat c a b => (if c then z1 else z0) * (P' b - P' a)

theorem ind_ivs (it : Item) (t : ℕ) :
    (it.ind t : R) = (it.ivs.map fun p ↦ if p.1 ≤ t ∧ t < p.2 then (1 : R) else 0).sum := by
  cases it with
  | iv lo hi => simp [Item.ind, Item.ivs]
  | one c =>
    simp only [Item.ind, Item.ivs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    split_ifs <;> first | rfl | omega
  | pat c a b =>
    simp only [Item.ind, Item.ivs, List.map_map, Function.comp_def, lsum_range]
    have key : ∀ u ∈ range (b - a),
        (if 2 * (a + u) + c.toNat ≤ t ∧ t < 2 * (a + u) + c.toNat + 1 then (1 : R) else 0) =
          if t / 2 - a = u then (if t.testBit 0 = c ∧ a ≤ t / 2 then 1 else 0) else 0 := by
      intro u _
      cases c <;> simp only [Nat.testBit_zero, Bool.toNat_false, Bool.toNat_true,
        decide_eq_false_iff_not, decide_eq_true_eq] <;> split_ifs <;> first | rfl | omega
    rw [sum_congr rfl key, sum_ite_eq]
    by_cases hP : t.testBit 0 = c <;>
      simp only [mem_range, hP, true_and, false_and, if_false, ite_self] <;>
      split_ifs <;> first | rfl | omega

/-- **Each item's fast value is its sum** (`n ≥ 1`; the pattern's `P'` is over `n − 1` bits). -/
theorem item_val (e : ℕ → Bool → R) (n : ℕ) (it : Item) (hw : it.WF) :
    (∑ t ∈ range (2 ^ (n + 1)), it.ind t * prodE e (n + 1) t) =
      it.val (psum e (n + 1)) (psum (fun l ↦ e (l + 1)) n) (prodE e (n + 1)) (e 0 false)
        (e 0 true) (n + 1) := by
  cases it with
  | iv lo hi =>
    simp only [Item.val, psum, ← sum_sub_distrib]
    refine sum_congr rfl fun t _ ↦ ?_
    simp only [Item.ind]
    have : lo ≤ hi := hw
    split_ifs <;> first | (exfalso; omega) | ring
  | one c =>
    simp only [Item.ind, Item.val, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
  | pat c a b =>
    have : a ≤ b := hw
    rw [pow_succ', sum_range_two_mul]
    simp only [Item.val, psum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun u _ ↦ ?_
    have h0 : (2 * u).testBit 0 = false := by simp [Nat.testBit_zero]
    have h1 : (2 * u + 1).testBit 0 = true := by simp [Nat.testBit_zero, Nat.add_mod]
    have d0 : 2 * u / 2 = u := by omega
    have d1 : (2 * u + 1) / 2 = u := by omega
    simp only [Item.ind, h0, h1, d0, d1, prodE_even, prodE_odd]
    cases c <;> simp only [Bool.false_eq_true, true_and, false_and, if_false, if_true,
      Bool.true_eq_false] <;> split_ifs <;> first | (exfalso; omega) | ring

end Items

/-! ## The node kinds' items -/

/-- The node kinds in `finLc`'s order `v_0 … v_7` (`blockKinds` without `chain`). -/
def nodeKinds : List BlockKind := blockKinds.tail

/-- Kind `κ`'s block intervals among `2^n` blocks: `Layout.kindIvs`, `free` extended to `2^n`. -/
def ivsQ (n : ℕ) (κ : BlockKind) : List (ℕ × ℕ) :=
  if κ = .free then [(Layout.wmBase, 2 ^ n)] else Layout.kindIvs κ

/-- WOTS slot `σ`'s first block. -/
def wB (σ : ℕ) : ℕ := Layout.wotsBase + Layout.wotsSlot * σ

/-- Slot `σ`'s path run: blocks `2·pathH σ … 2·pathH σ + 31` (`hashB1` even, `hashB2` odd). -/
def pathH (σ : ℕ) : ℕ := (wB σ + 466) / 2

open Layout in
/-- **The items of node kind `i < 7`** (`nodeKinds` order), in `nodeLayout`'s order. -/
def planFix : ℕ → List Item
  | 0 => [.iv 1 chainN, .iv (chainN + 1) (2 * chainN), .iv (wB 0 + 400) (wB 0 + 465),
      .iv (wB 1 + 400) (wB 1 + 465)]
  | 1 => [.one 0, .one chainN]
  | 2 => [.one (wB 0 + 465), .one (wB 1 + 465)]
  | 3 => [.one stmtBase, .one (stmtBase + 3)]
  | 4 => [.one (stmtBase + 1), .one (stmtBase + 4), .one (wB 0 + 399),
      .pat false (pathH 0) (pathH 0 + 16), .one (wB 1 + 399), .pat false (pathH 1) (pathH 1 + 16)]
  | 5 => [.one (stmtBase + 2), .one (stmtBase + 5), .pat true (pathH 0) (pathH 0 + 16),
      .pat true (pathH 1) (pathH 1 + 16)]
  | 6 => [.iv (wB 0) (wB 0 + 399), .iv (wB 1) (wB 1 + 399)]
  | _ => []

/-- **The items of node kind `i`** over `2^n` blocks (`free`: `[wmBase, 2^n)`). -/
def plan (n i : ℕ) : List Item := if i = 7 then [.iv Layout.wmBase (2 ^ n)] else planFix i

/-- **The items are the layout** (kernel-checked on the concrete lists). -/
theorem planFix_ivs : ∀ i < 7,
    (planFix i).flatMap Item.ivs = Layout.kindIvs (nodeKinds.getD i .free) := by decide +kernel

theorem planFix_wf : ∀ i < 7, ∀ it ∈ planFix i, it.WF := by decide +kernel

theorem nodeKinds_ne_free : ∀ i < 7, nodeKinds.getD i .free ≠ .free := by decide

theorem plan_ivs (n i : ℕ) (hi : i < 8) :
    (plan n i).flatMap Item.ivs = ivsQ n (nodeKinds.getD i .free) := by
  unfold plan ivsQ
  by_cases h7 : i = 7
  · subst h7; rfl
  · rw [if_neg h7, if_neg (nodeKinds_ne_free i (by omega)), planFix_ivs i (by omega)]

theorem wmBase_le {n : ℕ} (hn : 16 ≤ n) : Layout.wmBase ≤ 2 ^ n :=
  le_trans (by decide) (Nat.pow_le_pow_right (by norm_num) hn)

theorem plan_wf {n i : ℕ} (hn : 16 ≤ n) (hi : i < 8) : ∀ it ∈ plan n i, it.WF := by
  unfold plan
  split_ifs with h
  · simp only [List.mem_singleton]; rintro _ rfl; exact wmBase_le hn
  · exact planFix_wf i (by omega)

theorem sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (g : β → M) :
    ((L.flatMap f).map g).sum = (L.map fun x ↦ ((f x).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [List.flatMap_cons, ih]

theorem selOf_flatMap {R : Type*} [CommRing R] {n : ℕ} (L : List Item) (x : Fin (2 ^ n)) :
    (selOf (L.flatMap Item.ivs) x : R) = (L.map fun it ↦ (it.ind x.val : R)).sum := by
  simp only [selOf, sum_flatMap, ← ind_ivs]

theorem sum_lsum {M : Type*} [AddCommMonoid M] {α : Type*} (s : Finset ℕ) (L : List α)
    (f : α → ℕ → M) : ∑ t ∈ s, (L.map fun a ↦ f a t).sum = (L.map fun a ↦ ∑ t ∈ s, f a t).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [sum_add_distrib, ih]

theorem lprod_range {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, prod_range_succ, ih]

/-! ## Specification -/

/-- The per-bit weight of `eq(q, t)·eq(ρ, t)`. -/
def ew (q ρ : ℕ → K) (l : ℕ) (b : Bool) : K :=
  (if b then q l else 1 - q l) * (if b then ρ l else 1 - ρ l)

/-- **The kind-weighted block weight** (A.8 `rsWeight`, claim 2, at one Frobenius stage):
`Σ_{i<8} β^i Σ_t Ind_{κ_i}(t) eq(q, t) eq(ρ, t)` over the `2^n` blocks. -/
def kwS (n : ℕ) (β : K) (q ρ : Fin n → K) : K :=
  ∑ i ∈ range 8, β ^ i * ∑ t : Fin (2 ^ n),
    selOf (ivsQ n (nodeKinds.getD i .free)) t * eq q (cube t) * eq ρ (cube t)

theorem eq_mul_eq (n : ℕ) (qf ρf : ℕ → K) (t : Fin (2 ^ n)) :
    eq (fun l : Fin n ↦ qf l) (cube t) * eq (fun l : Fin n ↦ ρf l) (cube t) =
      prodE (ew qf ρf) n t.val := by
  rw [eq_cube, eq_cube, ← prod_mul_distrib, prodE]
  exact Fin.prod_univ_eq_prod_range (fun l ↦ ew qf ρf l (t.val.testBit l)) n

/-! ## Implementation -/

/-- Prefix products `[1, s 0, s 0 · s 1, …]` (`m + 1` entries). -/
def spArr (s : ℕ → K) : ℕ → Array K
  | 0 => #[1]
  | m + 1 => let a := spArr s m; a.push (a.getD m 0 * s m)

theorem spArr_size (s : ℕ → K) (m : ℕ) : (spArr s m).size = m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [spArr, ih]

theorem spArr_getD (s : ℕ → K) (m : ℕ) : ∀ l ≤ m, (spArr s m).getD l 0 = ∏ l' ∈ range l, s l' := by
  induction m with
  | zero => intro l hl; obtain rfl : l = 0 := by omega
            rfl
  | succ m ih =>
    intro l hl
    simp only [spArr, Array.getD_eq_getD_getElem?, Array.getElem?_push, spArr_size]
    split_ifs with h
    · subst h
      rw [Option.getD_some, prod_range_succ, ← ih m le_rfl, Array.getD_eq_getD_getElem?]
    · rw [← Array.getD_eq_getD_getElem?, ih l (by omega)]

theorem pfx_fun {R : Type*} [CommRing R] (e : ℕ → Bool → R) (e0 e1 lw sp : ℕ → R) (n : ℕ)
    (h0 : ∀ l < n, e0 l = e l false) (h1 : ∀ l < n, e1 l = e l true)
    (hs : ∀ l ≤ n, sp l = ∏ l' ∈ range l, (e l' false + e l' true))
    (hl : ∀ l < n, lw l = sp l * e l false) : pfx e0 e1 lw sp n = psum e n :=
  funext (pfx_eq e e0 e1 lw sp n h0 h1 hs hl)

/-- The items' values from the bit tables `g0 l = e_l(0)`, `g1 l = e_l(1)`. -/
def kwCore (n : ℕ) (β : K) (g0 g1 : ℕ → K) : K :=
  let sp := spArr (fun l ↦ g0 l + g1 l) n
  let lw : Array K := Array.ofFn fun l : Fin n ↦ sp.getD l 0 * g0 l
  let sp' := spArr (fun l ↦ g0 (l + 1) + g1 (l + 1)) (n - 1)
  let lw' : Array K := Array.ofFn fun l : Fin (n - 1) ↦ sp'.getD l 0 * g0 (l + 1)
  let P := pfx g0 g1 (fun l ↦ lw.getD l 0) (fun l ↦ sp.getD l 0) n
  let P' := pfx (fun l ↦ g0 (l + 1)) (fun l ↦ g1 (l + 1)) (fun l ↦ lw'.getD l 0)
    (fun l ↦ sp'.getD l 0) (n - 1)
  let pr : ℕ → K := fun c ↦ ((List.range n).map fun l ↦ if c.testBit l then g1 l else g0 l).prod
  ((List.range 8).map fun i ↦
    β ^ i * ((plan n i).map (Item.val P P' pr (g0 0) (g1 0) n)).sum).sum

/-- **The kind-weighted block weight, computed** (`kwI_eq`): per-bit tables `q_l ρ_l`,
`(1 − q_l)(1 − ρ_l)`, prefix products, then each kind's items by prefix sums (`pfx`), single
products and bit patterns. -/
def kwI (n : ℕ) (β : K) (qf ρf : ℕ → K) : K :=
  let a1 : Array K := Array.ofFn fun l : Fin n ↦ qf l * ρf l
  let a0 : Array K := Array.ofFn fun l : Fin n ↦ 1 - qf l - ρf l + a1.getD l 0
  kwCore n β (fun l ↦ a0.getD l 0) (fun l ↦ a1.getD l 0)

theorem kwCore_eq {n : ℕ} (hn : 16 ≤ n) (β : K) (e : ℕ → Bool → K) (g0 g1 : ℕ → K)
    (h0 : ∀ l < n, g0 l = e l false) (h1 : ∀ l < n, g1 l = e l true) :
    kwCore n β g0 g1 = ∑ i ∈ range 8, β ^ i *
      ((plan n i).map fun it ↦ ∑ t ∈ range (2 ^ n), it.ind t * prodE e n t).sum := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpr : (fun c : ℕ ↦ ((List.range (m + 1)).map fun l ↦
      if c.testBit l then g1 l else g0 l).prod) = prodE e (m + 1) := by
    funext c
    rw [lprod_range, prodE]
    refine prod_congr rfl fun l hl ↦ ?_
    have := mem_range.1 hl
    cases c.testBit l
    · exact h0 l this
    · exact h1 l this
  simp only [kwCore, Nat.add_sub_cancel]
  rw [pfx_fun e _ _ _ _ (m + 1) h0 h1 ?hs ?hl,
    pfx_fun (fun l ↦ e (l + 1)) _ _ _ _ m (fun l hl ↦ h0 (l + 1) (by omega))
      (fun l hl ↦ h1 (l + 1) (by omega)) ?hs' ?hl', lsum_range, hpr, h0 0 (by omega),
    h1 0 (by omega)]
  · refine sum_congr rfl fun i hi ↦ congrArg _ (congrArg List.sum
      (List.map_congr_left fun it hit ↦ ?_))
    exact (item_val e m it (plan_wf hn (mem_range.1 hi) it hit)).symm
  case hs =>
    intro l hl
    rw [spArr_getD _ _ l hl]
    exact prod_congr rfl fun l' hl' ↦ by
      have := mem_range.1 hl'
      rw [h0 l' (by omega), h1 l' (by omega)]
  case hl =>
    intro l hl
    rw [getD_ofFn, dif_pos hl, h0 l hl]
  case hs' =>
    intro l hl
    rw [spArr_getD _ _ l hl]
    exact prod_congr rfl fun l' hl' ↦ by
      have := mem_range.1 hl'
      rw [h0 (l' + 1) (by omega), h1 (l' + 1) (by omega)]
  case hl' =>
    intro l hl
    rw [getD_ofFn, dif_pos (by omega)]
    exact congrArg _ (h0 (l + 1) (by omega))

/-- The kind-weighted block weight as the items' sums (`kwI_eq`'s and `kwS_keys`' first step). -/
theorem kwS_items (n : ℕ) (β : K) (qf ρf : ℕ → K) :
    ∑ i ∈ range 8, β ^ i *
      ((plan n i).map fun it ↦ ∑ t ∈ range (2 ^ n), it.ind t * prodE (ew qf ρf) n t).sum =
    kwS n β (fun l ↦ qf l) (fun l ↦ ρf l) := by
  rw [kwS]
  refine sum_congr rfl fun i hi ↦ congrArg _ ?_
  rw [← plan_ivs n i (mem_range.1 hi)]
  simp only [mul_assoc, eq_mul_eq, selOf_flatMap]
  rw [Fin.sum_univ_eq_sum_range (fun t ↦ ((plan n i).map fun it ↦ (it.ind t : K)).sum *
    prodE (ew qf ρf) n t) (2 ^ n)]
  simp only [← List.sum_map_mul_right]
  rw [sum_lsum]

/-- **`kwI` meets `kwS`** on at least 16 block coordinates. -/
theorem kwI_eq {n : ℕ} (hn : 16 ≤ n) (β : K) (qf ρf : ℕ → K) :
    kwI n β qf ρf = kwS n β (fun l ↦ qf l) (fun l ↦ ρf l) := by
  have g1e : ∀ l < n, (Array.ofFn fun l : Fin n ↦ qf l * ρf l).getD l 0 = ew qf ρf l true :=
    fun l hl ↦ by rw [getD_ofFn, dif_pos hl]; simp [ew]
  have g0e : ∀ l < n, (Array.ofFn fun l : Fin n ↦ 1 - qf l - ρf l +
      (Array.ofFn fun l : Fin n ↦ qf l * ρf l).getD l 0).getD l 0 = ew qf ρf l false :=
    fun l hl ↦ by rw [getD_ofFn, dif_pos hl, g1e l hl]; simp only [ew, if_true, Bool.false_eq_true, if_false]; ring
  rw [kwI, kwCore_eq hn β (ew qf ρf) _ _ g0e g1e, kwS_items]

/-! ## A leaf's factor is trivial: the kinds partition the blocks -/

/-- `[lo, hi)` intervals chained from `a` to `b`, in order and without gaps. -/
def chainFrom : ℕ → List (ℕ × ℕ) → ℕ → Bool
  | a, [], b => a == b
  | a, p :: ps, b => p.1 == a && decide (p.1 ≤ p.2) && chainFrom p.2 ps b

theorem chainFrom_le : ∀ {a b : ℕ} {L : List (ℕ × ℕ)}, chainFrom a L b = true → a ≤ b
  | a, b, [], h => by simp [chainFrom] at h; omega
  | a, b, p :: ps, h => by
    simp only [chainFrom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have := chainFrom_le h.2; omega

theorem chainFrom_sum {R : Type*} [CommRing R] (t : ℕ) :
    ∀ {a b : ℕ} {L : List (ℕ × ℕ)}, chainFrom a L b = true →
      (L.map fun p ↦ if p.1 ≤ t ∧ t < p.2 then (1 : R) else 0).sum =
        if a ≤ t ∧ t < b then 1 else 0
  | a, b, [], h => by
    simp only [chainFrom, beq_iff_eq] at h; subst h; simp
  | a, b, p :: ps, h => by
    simp only [chainFrom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have hb := chainFrom_le h.2
    rw [List.map_cons, List.sum_cons, chainFrom_sum t h.2]
    obtain ⟨⟨h1, h2⟩, -⟩ := h
    split_ifs <;> first | (exfalso; omega) | simp

/-- The layout's intervals below `wmBase` (every kind but `free`), in address order. -/
def fixL : List (ℕ × ℕ) := Layout.nodeLayout.dropLast.map fun iv ↦ (iv.lo, iv.hi)

theorem fixL_chain : chainFrom 0 fixL Layout.wmBase = true := by decide +kernel

/-- The seven non-`free` node kinds' intervals are the layout's below `wmBase`, regrouped. -/
theorem kinds_perm :
    ((List.range 7).flatMap fun i ↦ Layout.kindIvs (nodeKinds.getD i .free)).Perm fixL := by
  decide +kernel

/-- **The kinds partition the blocks** (`Sel ≡ 1`, `free` the complement up to `2^n`). -/
theorem part_one {R : Type*} [CommRing R] {n : ℕ} (hn : 16 ≤ n) (t : Fin (2 ^ n)) :
    ∑ i ∈ range 8, (selOf (ivsQ n (nodeKinds.getD i .free)) t : R) = 1 := by
  rw [sum_range_succ, ← lsum_range]
  have h7 : ∀ i ∈ List.range 7, (selOf (ivsQ n (nodeKinds.getD i .free)) t : R) =
      selOf (Layout.kindIvs (nodeKinds.getD i .free)) t := fun i hi ↦ by
    rw [ivsQ, if_neg (nodeKinds_ne_free i (List.mem_range.1 hi))]
  rw [List.map_congr_left h7]
  simp only [selOf]
  rw [← sum_flatMap, (kinds_perm.map _).sum_eq, chainFrom_sum t.val fixL_chain]
  simp only [ivsQ, show nodeKinds.getD 7 .free = .free from rfl, if_true, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have := t.isLt
  have := wmBase_le hn
  split_ifs <;> first | (exfalso; omega) | simp

/-- **A leaf's claim 2 is the plain `eq`** (`β = 1`): `kwS n 1 q ρ = eq(q, ρ)`. -/
theorem kwS_one {n : ℕ} (hn : 16 ≤ n) (q ρ : Fin n → K) : kwS n 1 q ρ = eq q ρ := by
  rw [kwS, ← eq_mle q ρ]
  simp only [one_pow, one_mul]
  rw [sum_comm]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [← sum_mul, ← sum_mul, part_one hn t, one_mul, eq_swap (cube t) ρ]

/-! ## Controls -/

/-- At a Boolean point the factor is `Σ_i β^i Ind_{κ_i}(t₀)`: `β^i` of the block's kind. -/
theorem kwS_cube (n : ℕ) (β : K) (t₀ : Fin (2 ^ n)) :
    kwS n β (cube t₀) (cube t₀) = ∑ i ∈ range 8, β ^ i * selOf (ivsQ n (nodeKinds.getD i .free)) t₀ := by
  refine sum_congr rfl fun i _ ↦ congrArg _ ?_
  simp only [eq_cube_cube, ← ite_and, and_self, mul_ite, mul_one, mul_zero]
  simp

/-- `hashStmt`'s block A of slot 1. -/
def tA : Fin (2 ^ 16) := ⟨Layout.stmtBase, by decide⟩

theorem selOf_tA : ∀ i < 8, (selOf (ivsQ 16 (nodeKinds.getD i .free)) tA : ℤ) =
    if i = 3 then 1 else 0 := by decide +kernel

theorem selOf_cast {n : ℕ} (ivs : List (ℕ × ℕ)) (x : Fin (2 ^ n)) :
    (selOf ivs x : K) = ((selOf ivs x : ℤ) : K) := by
  simp only [selOf, Int.cast_list_sum, List.map_map, Function.comp_def, Int.cast_ite,
    Int.cast_one, Int.cast_zero]

/-- (+) **The factor at `hashStmt`'s block A is `β^3`** (`hashA` is `v_3`'s kind). -/
theorem kwS_hashA (β : K) : kwS 16 β (cube tA) (cube tA) = β ^ 3 := by
  rw [kwS_cube, sum_eq_single 3]
  · rw [selOf_cast, selOf_tA 3 (by norm_num), if_pos rfl, Int.cast_one, mul_one]
  · intro i hi h3
    rw [selOf_cast, selOf_tA i (mem_range.1 hi), if_neg h3, Int.cast_zero, mul_zero]
  · simp

/-- (−) **… so it is not the plain weight** (R-V-M1's defect): at `β = 0` the kind-weighted value
at block A is `0`, the plain `eq` is `1`. -/
theorem kwS_hashA_ne_plain : kwS 16 0 (cube tA) (cube tA) ≠ eq (cube tA) (cube tA) := by
  rw [kwS_hashA, eq_cube_cube, if_pos rfl]
  simp

/-! ## The fast form (S-T1): dyadic blocks, merged keys, the `F` side

Per stage the value is a sum over **blocks**: `[0, x)` is the union of the dyadic blocks
`{t : t >>> (j+1) = x >>> (j+1), bit j of t = 0}` over the set bits `j` of `x` (`cubesOf`), each
with weight (fixed bits' product) · `Π_{l<j} s_l`, `s_l = e_l(0) + e_l(1)` (`cubeW`). An item is two
signed prefix sums (characteristic two: the signs drop), a pattern two prefix sums over bits
`1…n-1` times bit 0's weight. The blocks of all items, merged by key (`grpM`, `grpP`), are a closed
constant. The fixed bits' product splits as an `F` part (the claim point's side, `q ∈ F`) times a
`K` part (`ρ`'s, the same at every stage), and the `F` part of stage `k` is the `2^k`-th power of
stage 0's: per stage only squarings, one `smulF` per block and two Horner sums over the levels. -/

/-- The dyadic blocks of `[0, x)` over `n` bits: `(j, x >>> (j+1))` for each set bit `j` of `x`;
all of `[0, 2^n)` (the key `(n, 0)`) once `2^n ≤ x`. -/
def cubesOf (n x : ℕ) : List (ℕ × ℕ) :=
  if 2 ^ n ≤ x then [(n, 0)] else
    (List.range n).flatMap fun j => if x.testBit j then [(j, x >>> (j + 1))] else []

/-- Block `(j, u)`'s fixed bits: bit `j` is `0` and bit `j + 1 + l` is `u`'s bit `l`; none for
`j ≥ n` (the whole cube). -/
def fixB (n j u : ℕ) : List (ℕ × Bool) :=
  if j < n then (j, false) :: (List.range (n - j - 1)).map fun l => (j + 1 + l, u.testBit l) else []

/-- A block key: `none` a block of the `n` bits, `some c` a pattern block (bit 0 is `c`, the block
over bits `1 … n-1`); then the level and the high part. -/
abbrev Key := Option Bool × ℕ × ℕ

/-- A key's fixed bits. -/
def fixK (n : ℕ) : Key → List (ℕ × Bool)
  | (none, j, u) => fixB n j u
  | (some c, j, u) => (0, c) :: (fixB (n - 1) j u).map fun p => (p.1 + 1, p.2)

/-- An item's signed prefix-sum endpoints `(exponent, side, x)`. An even pattern is the run
`[2a, 2b)` minus the odd pattern, so every pattern block is on the odd side. -/
def itemTerms (i : ℕ) : Item → List (ℕ × Option Bool × ℕ)
  | .iv lo hi => [(i, none, hi), (i, none, lo)]
  | .one c => [(i, none, c + 1), (i, none, c)]
  | .pat true a b => [(i, some true, b), (i, some true, a)]
  | .pat false a b => [(i, none, 2 * b), (i, none, 2 * a), (i, some true, b), (i, some true, a)]

/-- An endpoint's blocks. -/
def termKeys (n : ℕ) : ℕ × Option Bool × ℕ → List (ℕ × Key)
  | (i, none, x) => (cubesOf n x).map fun c => (i, none, c.1, c.2)
  | (i, some b, x) => (cubesOf (n - 1) x).map fun c => (i, some b, c.1, c.2)

/-- Every item's blocks, with the kind's exponent. -/
def allKeys (n : ℕ) : List (ℕ × Key) :=
  ((List.range 8).flatMap fun i => (plan n i).flatMap (itemTerms i)).flatMap (termKeys n)

/-- Merge neighbours with equal keys (their exponent lists appended). -/
def mergeAdj {α : Type} [DecidableEq α] : List (α × List ℕ) → List (α × List ℕ)
  | [] => []
  | p :: rest =>
    match mergeAdj rest with
    | [] => [p]
    | q :: rest' => if p.1 = q.1 then (p.1, p.2 ++ q.2) :: rest' else p :: q :: rest'

/-- A block of level `j` on side `none`, as `(u, [exponent])`. -/
def selM (j : ℕ) (p : ℕ × Key) : Option (ℕ × List ℕ) :=
  if p.2.1 = none ∧ p.2.2.1 = j then some (p.2.2.2, [p.1]) else none

/-- A pattern block of level `j`, as `((c, u), [exponent])`. -/
def selP (j : ℕ) (p : ℕ × Key) : Option ((Bool × ℕ) × List ℕ) :=
  match p.2 with
  | (some c, j', u) => if j' = j then some ((c, u), [p.1]) else none
  | _ => none

/-- Level `j`'s blocks on side `none`, merged: `(u, exponents)`. -/
def grpM (n j : ℕ) : List (ℕ × List ℕ) :=
  mergeAdj (((allKeys n).filterMap (selM j)).mergeSort fun a b => decide (a.1 ≤ b.1))

/-- Level `j`'s pattern blocks, merged: `((c, u), exponents)`. -/
def grpP (n j : ℕ) : List ((Bool × ℕ) × List ℕ) :=
  mergeAdj (((allKeys n).filterMap (selP j)).mergeSort
    fun a b => decide (2 * a.1.2 + a.1.1.toNat ≤ 2 * b.1.2 + b.1.1.toNat))

/-- **The node layout's merged blocks** (16 block bits), level by level, as fixed-bit lists with
exponents: a closed constant. -/
def skelM : List (List (List (ℕ × Bool) × List ℕ)) :=
  (List.range 17).map fun j => (grpM 16 j).map fun p => (fixK 16 (none, j, p.1), p.2)

/-- The pattern blocks, level by level (levels `0 … 15` of the 15 bits above bit 0). -/
def skelP : List (List (List (ℕ × Bool) × List ℕ)) :=
  (List.range 16).map fun j => (grpP 16 j).map fun p => (fixK 16 (some p.1.1, j, p.1.2), p.2)

/-- A block's two factors at the claim point's side `fF` (`F`) and `ρ`'s side `gK` (`K`), its
coefficient `Σ_{i ∈ E} β^i` from the powers `bp`. -/
def mkEnt (bp : ℕ → F) (fF : ℕ → Bool → F) (gK : ℕ → Bool → K) (g : List (List (ℕ × Bool) × List ℕ)) :
    List (F × K) :=
  (g.map fun p => ((p.2.map bp).sum * (p.1.map fun b => fF b.1 b.2).prod,
    (p.1.map fun b => gK b.1 b.2).prod)).filter fun p => p.1 != 0

/-- A level's sum `Σ a • G`. -/
def gsum (g : List (F × K)) : K := (g.map fun p => K.smulF p.1 p.2).sum

/-- `Σ_j (Π_{l<j} s (o + l)) y_j`, by Horner. -/
def hornerK (s : ℕ → K) : ℕ → List K → K
  | _, [] => 0
  | o, y :: ys => y + s o * hornerK s (o + 1) ys

/-- The next stage's levels: each `F` factor squared. -/
def sqG (g : List (List (F × K))) : List (List (F × K)) := g.map fun l => l.map fun p => (F.sq p.1, p.2)

section P
variable {R : Type*} [CommRing R]

/-- Block `(j, u)`'s weight: its fixed bits' product times `Π_{l < min j n} (e_l(0) + e_l(1))`. -/
def cubeW (e : ℕ → Bool → R) (n j u : ℕ) : R :=
  ((fixB n j u).map fun p => e p.1 p.2).prod * ∏ l ∈ range (min j n), (e l false + e l true)

theorem cubes_sum {M : Type*} [AddCommMonoid M] (W : ℕ × ℕ → M) {n x : ℕ} (hx : x < 2 ^ n) :
    ((cubesOf n x).map W).sum = ∑ j ∈ range n, if x.testBit j then W (j, x >>> (j + 1)) else 0 := by
  rw [cubesOf, if_neg (by omega), sum_flatMap, ← lsum_range]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  split_ifs <;> simp

theorem fixB_succ {n j : ℕ} (hj : j < n) (u : ℕ) :
    fixB (n + 1) j u = fixB n j u ++ [(n, u.testBit (n - j - 1))] := by
  rw [fixB, fixB, if_pos (by omega), if_pos hj, show n + 1 - j - 1 = (n - j - 1) + 1 by omega,
    List.range_succ, List.map_append, List.cons_append]
  simp only [List.map_cons, List.map_nil]
  rw [show j + 1 + (n - j - 1) = n by omega]

theorem cubeW_congr (e : ℕ → Bool → R) (n j : ℕ) {u u' : ℕ}
    (h : ∀ l < n - j - 1, u.testBit l = u'.testBit l) : cubeW e n j u = cubeW e n j u' := by
  unfold cubeW fixB
  split_ifs
  · congr 2
    simp only [List.map_cons, List.map_map]
    congr 1
    exact List.map_congr_left fun l hl => by
      simp only [Function.comp_apply, h l (List.mem_range.1 hl)]
  · rfl

theorem cubeW_succ (e : ℕ → Bool → R) {n j : ℕ} (hj : j < n) (u : ℕ) :
    cubeW e (n + 1) j u = cubeW e n j u * e n (u.testBit (n - j - 1)) := by
  rw [cubeW, cubeW, fixB_succ hj, List.map_append, List.prod_append,
    show min j (n + 1) = min j n by omega]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

/-- **The prefix sum is the sum over its dyadic blocks.** -/
theorem psum_cubes (e : ℕ → Bool → R) (n x : ℕ) :
    psum e n x = ((cubesOf n x).map fun c => cubeW e n c.1 c.2).sum := by
  by_cases hx : 2 ^ n ≤ x
  · rw [cubesOf, if_pos hx]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, cubeW, fixB,
      lt_irrefl, if_false, List.map_nil, List.prod_nil, one_mul, min_self]
    rw [psum, ← sum_prodE]
    exact sum_congr rfl fun t ht => if_pos (by have := mem_range.1 ht; omega)
  rw [cubes_sum _ (by omega)]
  push_neg at hx
  induction n generalizing x with
  | zero =>
    obtain rfl : x = 0 := by simpa using hx
    simp [psum]
  | succ n ih =>
    rw [psum_succ, sum_range_succ]
    by_cases hn : x < 2 ^ n
    · rw [Nat.testBit_lt_two_pow hn, if_neg (by simp), add_zero,
        show (∑ t ∈ range (2 ^ n), if 2 ^ n + t < x then prodE e n t * e n true else 0) = 0 from
          sum_eq_zero fun t _ => if_neg (by omega), add_zero]
      have h1 : (∑ t ∈ range (2 ^ n), if t < x then prodE e n t * e n false else 0) =
          psum e n x * e n false := by
        rw [psum, sum_mul]; exact sum_congr rfl fun t _ => by split_ifs <;> simp
      rw [h1, ih x hn, sum_mul]
      refine sum_congr rfl fun j hj => ?_
      have hj := mem_range.1 hj
      split_ifs
      · rw [cubeW_succ e hj, Nat.testBit_shiftRight, show j + 1 + (n - j - 1) = n by omega,
          Nat.testBit_lt_two_pow hn]
      · simp
    · push_neg at hn
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ n + y := ⟨x - 2 ^ n, by omega⟩
      have hy : y < 2 ^ n := by rw [pow_succ] at hx; omega
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy, Bool.not_false, if_pos rfl]
      have h1 : (∑ t ∈ range (2 ^ n), if t < 2 ^ n + y then prodE e n t * e n false else 0) =
          (∏ l ∈ range n, (e l false + e l true)) * e n false := by
        rw [← sum_prodE, sum_mul]
        exact sum_congr rfl fun t ht => if_pos (by have := mem_range.1 ht; omega)
      have h2 : (∑ t ∈ range (2 ^ n), if 2 ^ n + t < 2 ^ n + y then prodE e n t * e n true else 0) =
          psum e n y * e n true := by
        rw [psum, sum_mul]
        exact sum_congr rfl fun t _ => by split_ifs <;> first | rfl | (exfalso; omega) | simp
      rw [h1, h2, ih y hy, sum_mul, add_comm]
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        have hj := mem_range.1 hj
        rw [Nat.testBit_two_pow_add_gt hj]
        split_ifs
        · rw [cubeW_succ e hj, Nat.testBit_shiftRight, show j + 1 + (n - j - 1) = n by omega,
            Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy, Bool.not_false]
          congr 1
          refine cubeW_congr e n j fun l hl => ?_
          rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_two_pow_add_gt (by omega)]
        · simp
      · rw [cubeW, fixB, if_pos (by omega), show n + 1 - n - 1 = 0 by omega, min_eq_left (by omega)]
        simp only [List.range_zero, List.map_nil, List.map_cons, List.prod_cons, List.prod_nil,
          mul_one]
        ring

theorem psum_succ_one (e : ℕ → Bool → R) (n c : ℕ) :
    psum e n (c + 1) = psum e n c + if c < 2 ^ n then prodE e n c else 0 := by
  have : psum e n (c + 1) = psum e n c +
      ∑ t ∈ range (2 ^ n), if t = c then prodE e n t else 0 := by
    rw [psum, psum, ← sum_add_distrib]
    exact sum_congr rfl fun t _ => by split_ifs <;> first | rfl | (exfalso; omega) | simp
  rw [this, sum_ite_eq' (range (2 ^ n)) c]
  simp only [mem_range]

theorem psum_two_mul (e : ℕ → Bool → R) (m y : ℕ) :
    psum e (m + 1) (2 * y) = (e 0 false + e 0 true) * psum (fun l => e (l + 1)) m y := by
  rw [psum, psum, pow_succ', sum_range_two_mul, mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [prodE_even, prodE_odd]
  by_cases h : u < y
  · rw [if_pos (by omega), if_pos (by omega), if_pos h]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg h]; ring

/-- A block key's weight: a block of the `n` bits, or bit 0's weight times a block of bits `1…`. -/
def keyW (e : ℕ → Bool → R) (n : ℕ) : Key → R
  | (none, j, u) => cubeW e n j u
  | (some c, j, u) => e 0 c * cubeW (fun l => e (l + 1)) (n - 1) j u

/-- An endpoint's value: `β^i` times the prefix sum; a pattern endpoint: times bit 0's weight, the
prefix sum over bits `1 … m`. -/
def termV (e : ℕ → Bool → R) (β : R) (m : ℕ) : ℕ × Option Bool × ℕ → R
  | (i, none, x) => β ^ i * psum e (m + 1) x
  | (i, some c, x) => β ^ i * (e 0 c * psum (fun l => e (l + 1)) m x)

/-- **An endpoint's value is the sum over its blocks.** -/
theorem termV_keys (e : ℕ → Bool → R) (β : R) (m : ℕ) (t : ℕ × Option Bool × ℕ) :
    termV e β m t = ((termKeys (m + 1) t).map fun p => β ^ p.1 * keyW e (m + 1) p.2).sum := by
  obtain ⟨i, s, x⟩ := t
  cases s with
  | none =>
    simp only [termV, termKeys, List.map_map, Function.comp_def, keyW, psum_cubes,
      List.sum_map_mul_left]
  | some c =>
    simp only [termV, termKeys, List.map_map, Function.comp_def, keyW, psum_cubes,
      Nat.add_sub_cancel, List.sum_map_mul_left]

end P

section C2
variable {R : Type*} [CommRing R] [CharP R 2]

/-- **An item's fast value is the sum of its endpoints' values** (characteristic two). -/
theorem item_terms (e : ℕ → Bool → R) (β : R) (m i : ℕ) (it : Item) :
    β ^ i * it.val (psum e (m + 1)) (psum (fun l => e (l + 1)) m) (prodE e (m + 1)) (e 0 false)
      (e 0 true) (m + 1) = ((itemTerms i it).map (termV e β m)).sum := by
  have h2 := CharTwo.two_eq_zero (R := R)
  cases it with
  | iv lo hi =>
    simp only [Item.val, itemTerms, termV, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, CharTwo.sub_eq_add, mul_add]
  | one c =>
    simp only [Item.val, itemTerms, termV, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, psum_succ_one]
    linear_combination (-(β ^ i * psum e (m + 1) c)) * h2
  | pat c a b =>
    cases c with
    | true =>
      simp only [Item.val, itemTerms, termV, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, CharTwo.sub_eq_add, if_true]
      ring
    | false =>
      simp only [Item.val, itemTerms, termV, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, CharTwo.sub_eq_add, Bool.false_eq_true, if_false, psum_two_mul]
      linear_combination (-(β ^ i * e 0 true * (psum (fun l => e (l + 1)) m b +
        psum (fun l => e (l + 1)) m a))) * h2

/-- **The kind-weighted block weight is the sum over all items' blocks** (`n = m + 1 ≥ 16`). -/
theorem kwS_keys {m : ℕ} (hn : 16 ≤ m + 1) (β : K) (qf ρf : ℕ → K) :
    kwS (m + 1) β (fun l ↦ qf l) (fun l ↦ ρf l) =
      ((allKeys (m + 1)).map fun p => β ^ p.1 * keyW (ew qf ρf) (m + 1) p.2).sum := by
  rw [← kwS_items, allKeys, sum_flatMap]
  simp only [← termV_keys, sum_flatMap, ← item_terms, ← lsum_range, ← List.sum_map_mul_left]
  refine congrArg List.sum ?_
  refine List.map_congr_left fun i hi => congrArg _ (List.map_congr_left fun it hit => ?_)
  rw [List.sum_map_mul_left, lsum_range, item_val _ m it (plan_wf hn (List.mem_range.1 hi) it hit)]

end C2
section Grp
variable {R : Type*} [CommRing R]

theorem sum_filterMap {α β : Type*} (L : List α) (φ : α → Option β) (F : β → R) :
    ((L.filterMap φ).map F).sum = (L.map fun a => (φ a).elim 0 F).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons]
    cases φ a <;> simp [ih]

theorem mergeAdj_sum {α : Type} [DecidableEq α] (w : ℕ → R) (V : α → R) :
    ∀ L : List (α × List ℕ), ((mergeAdj L).map fun p => (p.2.map w).sum * V p.1).sum =
      (L.map fun p => (p.2.map w).sum * V p.1).sum
  | [] => rfl
  | p :: rest => by
    have ih := mergeAdj_sum w V rest
    rw [List.map_cons, List.sum_cons, ← ih, mergeAdj]
    split
    · next h => simp [h]
    · next q rest' h =>
      rw [h] at ih ⊢
      split_ifs with hk
      · simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append, hk]
        ring
      · rfl

theorem cubesOf_le {n x : ℕ} {c : ℕ × ℕ} (h : c ∈ cubesOf n x) : c.1 ≤ n := by
  unfold cubesOf at h
  split_ifs at h
  · simp at h; simp [h]
  · simp only [List.mem_flatMap, List.mem_range] at h
    obtain ⟨j, hj, hc⟩ := h
    split_ifs at hc <;> simp at hc
    rw [hc]; exact hj.le

theorem allKeys_lvl {m : ℕ} {p : ℕ × Key} (h : p ∈ allKeys (m + 1)) :
    (p.2.1 = none → p.2.2.1 < m + 2) ∧ (p.2.1 ≠ none → p.2.2.1 < m + 1) := by
  simp only [allKeys, List.mem_flatMap] at h
  obtain ⟨⟨i, s, x⟩, -, hp⟩ := h
  cases s with
  | none =>
    simp only [termKeys, List.mem_map] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    have := cubesOf_le hc
    exact ⟨fun _ => by simp; omega, fun h => absurd rfl h⟩
  | some b =>
    simp only [termKeys, List.mem_map] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    have := cubesOf_le hc
    exact ⟨fun h => by simp at h, fun _ => by simp; omega⟩

/-- **The blocks regrouped by level and merged by key.** -/
theorem keys_grp (m : ℕ) (w : ℕ → R) (V : Key → R) :
    ((allKeys (m + 1)).map fun p => w p.1 * V p.2).sum =
      ∑ j ∈ range (m + 2), ((grpM (m + 1) j).map fun p => (p.2.map w).sum * V (none, j, p.1)).sum +
      ∑ j ∈ range (m + 1),
        ((grpP (m + 1) j).map fun p => (p.2.map w).sum * V (some p.1.1, j, p.1.2)).sum := by
  have hM : ∀ j, ((grpM (m + 1) j).map fun p => (p.2.map w).sum * V (none, j, p.1)).sum =
      ((allKeys (m + 1)).map fun p =>
        (selM j p).elim 0 fun q => (q.2.map w).sum * V (none, j, q.1)).sum := fun j => by
    rw [grpM, mergeAdj_sum w (fun u => V (none, j, u)),
      ((List.mergeSort_perm _ _).map _).sum_eq, sum_filterMap]
  have hP : ∀ j, ((grpP (m + 1) j).map fun p => (p.2.map w).sum * V (some p.1.1, j, p.1.2)).sum =
      ((allKeys (m + 1)).map fun p =>
        (selP j p).elim 0 fun q => (q.2.map w).sum * V (some q.1.1, j, q.1.2)).sum := fun j => by
    rw [grpP]
    refine (mergeAdj_sum w (fun cu : Bool × ℕ => V (some cu.1, j, cu.2)) _).trans ?_
    rw [((List.mergeSort_perm _ _).map _).sum_eq, sum_filterMap]
  simp only [hM, hP, sum_lsum, ← List.sum_map_add]
  refine congrArg _ (List.map_congr_left fun p hp => ?_)
  obtain ⟨h1, h2⟩ := allKeys_lvl hp
  obtain ⟨i, s, j0, u⟩ := p
  cases s with
  | none =>
    have := h1 rfl
    have hz : ∀ t, (selP t (i, none, j0, u)).elim (0 : R)
        (fun p => (List.map w p.2).sum * V (some p.1.1, t, p.1.2)) = 0 := fun t => by simp [selP]
    simp only [hz, sum_const_zero, add_zero]
    rw [sum_eq_single j0]
    · simp [selM, selP]
    · intro j _ hj; simp [selM, selP, Ne.symm hj]
    · intro h; exact absurd (mem_range.2 this) h
  | some c =>
    simp only at h2
    have := h2 (by simp)
    have hz : ∀ t, (selM t (i, some c, j0, u)).elim (0 : R)
        (fun q => (List.map w q.2).sum * V (none, t, q.1)) = 0 := fun t => by simp [selM]
    simp only [hz, sum_const_zero, zero_add]
    rw [sum_eq_single j0]
    · simp [selM, selP]
    · intro j _ hj; simp [selM, selP, Ne.symm hj]
    · intro h; exact absurd (mem_range.2 this) h

end Grp

section Stage

/-- The free bits' product of a key (`s_l = e_l(0) + e_l(1)`). -/
def freeP (e : ℕ → Bool → K) (n : ℕ) : Key → K
  | (none, j, _) => ∏ l ∈ range (min j n), (e l false + e l true)
  | (some _, j, _) => ∏ l ∈ range (min j (n - 1)), (e (l + 1) false + e (l + 1) true)

theorem keyW_split (e : ℕ → Bool → K) (n : ℕ) (k : Key) :
    keyW e n k = ((fixK n k).map fun p => e p.1 p.2).prod * freeP e n k := by
  obtain ⟨s, j, u⟩ := k
  cases s with
  | none => rfl
  | some c =>
    simp only [keyW, cubeW, fixK, freeP, List.map_cons, List.prod_cons, List.map_map,
      Function.comp_def]
    ring

theorem prod_fix_ofF (qF : ℕ → F) (ρf : ℕ → K) (L : List (ℕ × Bool)) :
    (L.map fun p => ew (fun l => K.ofF (qF l)) ρf p.1 p.2).prod =
      K.ofF ((L.map fun p => if p.2 then qF p.1 else 1 - qF p.1).prod) *
        (L.map fun p => if p.2 then ρf p.1 else 1 - ρf p.1).prod := by
  induction L with
  | nil => simp; rfl
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    have hm : ∀ a b : F, K.ofF (a * b) = K.ofF a * K.ofF b := map_mul K.ofFRingHom
    rw [hm]
    have h1 : K.ofF (if p.2 then qF p.1 else 1 - qF p.1) =
        if p.2 then K.ofF (qF p.1) else 1 - K.ofF (qF p.1) := by
      split_ifs
      · rfl
      · exact (map_sub K.ofFRingHom 1 (qF p.1)).trans (by rw [map_one]; rfl)
    rw [h1, ew]
    ring

theorem gsum_mkEnt (bp : ℕ → F) (fF : ℕ → Bool → F) (gK : ℕ → Bool → K)
    (g : List (List (ℕ × Bool) × List ℕ)) :
    gsum (mkEnt bp fF gK g) = (g.map fun p => K.ofF ((p.2.map bp).sum) *
      (K.ofF ((p.1.map fun b => fF b.1 b.2).prod) * (p.1.map fun b => gK b.1 b.2).prod)).sum := by
  have hm : ∀ a b : F, K.ofF (a * b) = K.ofF a * K.ofF b := map_mul K.ofFRingHom
  rw [gsum, mkEnt]
  induction g with
  | nil => rfl
  | cons p g ih =>
    simp only [List.map_cons, List.filter_cons, List.sum_cons]
    split_ifs with h
    · rw [List.map_cons, List.sum_cons, ih, K.smulF_eq_mul, hm, mul_assoc]
    · rw [ih]
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
      rw [← mul_assoc, ← hm, h, show K.ofF 0 = 0 from rfl, zero_mul, zero_add]

theorem hornerK_eq (s : ℕ → K) : ∀ (o : ℕ) (Y : List K),
    hornerK s o Y = ∑ j ∈ range Y.length, (∏ l ∈ range j, s (o + l)) * Y.getD j 0
  | _, [] => by simp [hornerK]
  | o, y :: ys => by
    rw [hornerK, hornerK_eq s (o + 1) ys, List.length_cons, sum_range_succ', mul_sum, add_comm]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine sum_congr rfl fun j _ => ?_
      rw [prod_range_succ', List.getD_cons_succ, add_zero,
        prod_congr rfl fun l _ => congrArg s (show o + (l + 1) = o + 1 + l by omega)]
      ring
    · simp

theorem getD_range_map {α : Type*} {n j : ℕ} (g : ℕ → α) (d : α) (hj : j < n) :
    ((List.range n).map g).getD j d = g j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem ofF_lsum (L : List F) : K.ofF L.sum = (L.map K.ofF).sum := map_list_sum K.ofFRingHom L

theorem ofF_pow (a : F) (i : ℕ) : K.ofF (a ^ i) = K.ofF a ^ i := map_pow K.ofFRingHom a i

/-- **One stage, fast** (16 block bits; the claim point's block coordinates in `F`). -/
theorem kwS_fast (β : F) (qF : ℕ → F) (ρf : ℕ → K) (s : ℕ → K)
    (hs : ∀ l < 16, s l = K.ofF (qF l) + (1 + ρf l)) :
    kwS 16 (K.ofF β) (fun l => K.ofF (qF l)) (fun l => ρf l) =
      hornerK s 0 (skelM.map fun g => gsum (mkEnt (β ^ ·) (fun l b => if b then qF l else 1 - qF l)
        (fun l b => if b then ρf l else 1 - ρf l) g)) +
      hornerK s 1 (skelP.map fun g => gsum (mkEnt (β ^ ·) (fun l b => if b then qF l else 1 - qF l)
        (fun l b => if b then ρf l else 1 - ρf l) g)) := by
  set e := ew (fun l => K.ofF (qF l)) ρf
  have h2 := CharTwo.two_eq_zero (R := K)
  have hse : ∀ l < 16, e l false + e l true = s l := fun l hl => by
    rw [hs l hl]
    simp only [e, ew, if_true, Bool.false_eq_true, if_false]
    linear_combination (K.ofF (qF l) * ρf l - K.ofF (qF l) - ρf l) * h2
  refine (kwS_keys (m := 15) (by norm_num) (K.ofF β) (fun l => K.ofF (qF l)) ρf).trans ?_
  rw [keys_grp 15 (K.ofF β ^ ·) (keyW e (15 + 1)), hornerK_eq,
    hornerK_eq, skelM, skelP, List.map_map, List.map_map, List.length_map, List.length_map,
    List.length_range, List.length_range, show (15 : ℕ) + 1 = 16 from rfl]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine sum_congr rfl fun j hj => ?_
    have hj := mem_range.1 hj
    rw [getD_range_map _ _ hj, Function.comp_apply, gsum_mkEnt, List.map_map,
      ← List.sum_map_mul_left]
    refine congrArg _ (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply]
    rw [keyW_split, ← prod_fix_ofF, ofF_lsum, List.map_map]
    simp only [Function.comp_def, ofF_pow, freeP, min_eq_left (show j ≤ 16 by omega)]
    rw [prod_congr rfl fun l hl => hse l (by have := mem_range.1 hl; omega)]
    simp only [zero_add]
    ring
  · refine sum_congr rfl fun j hj => ?_
    have hj := mem_range.1 hj
    rw [getD_range_map _ _ hj, Function.comp_apply, gsum_mkEnt, List.map_map,
      ← List.sum_map_mul_left]
    refine congrArg _ (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply]
    rw [keyW_split, ← prod_fix_ofF, ofF_lsum, List.map_map]
    simp only [Function.comp_def, ofF_pow, freeP, show 16 - 1 = 15 from rfl,
      min_eq_left (show j ≤ 15 by omega)]
    rw [prod_congr rfl fun l hl => hse (l + 1) (by have := mem_range.1 hl; omega)]
    simp only [show ∀ l, 1 + l = l + 1 from fun l => by omega]
    ring

end Stage


/-! ### Controls of the fast form -/

/-- (+) The blocks of `[0, 11)` over 4 bits: `{10}`, `{8, 9}`, `[0, 8)`; `[0, 16)` is one block. -/
theorem cubesOf_pos : cubesOf 4 11 = [(0, 5), (1, 2), (3, 0)] ∧ cubesOf 4 16 = [(4, 0)] := by
  decide

/-- (−) The key is the part above bit `j` (`x >>> (j+1)`): keyed by `x >>> j`, the blocks differ. -/
theorem cubesOf_neg : cubesOf 4 11 ≠ [(0, 11), (1, 5), (3, 1)] := by decide

/-- (+) The node layout's items give 417 blocks (`skelM`, `skelP` merge them to 58 + 23 keys:
`logs/S-T1`, the probe's `kf` run), and **no pattern block is on the even side** (an even pattern is
a run minus the odd one, `itemTerms`). -/
theorem allKeys_counts : (allKeys 16).length = 417 ∧
    (allKeys 16).all (fun p => p.2.1 != some false) = true := by decide +kernel

/-- (−) … while the plan itself has even patterns (`hashB1`'s path blocks). -/
theorem plan_even : (plan 16 4).any (fun it => it == .pat false (pathH 0) (pathH 0 + 16)) = true := by
  decide +kernel

end KW
end FR
