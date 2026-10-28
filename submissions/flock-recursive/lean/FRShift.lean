-- New for `flock-recursive` (BLUEPRINT §2.3 step 4, §5.2 rows S1–S3, §7 `FRShift`).
import FRSumcheck
import FRField128

/-!
# The shift argument (BLUEPRINT rev. 3.1 §2.3 step 4, §4.1, §5.2 rows S1–S2; P1-D5)

The chain checks of the leaf and the node: the input slot of block `y + 1` equals the output slot
of block `y`, the first input is the public start `s` (or `h0`), the last output the public end `h`.
Tables live on `s + n` variables, `join σ y`: the slot `σ` low, the block `y` high. The block count
`n` (`m − 14`) and the slot width `s` are parameters.

* The successor `succT u v = [v = u + 1]` (no wrap) and its bilinear extension `shiftMle`
  (**`shift_mle`**: `Σ_{u,v} eq(τ,u) [v = u+1] eq(v,ρ) = S_n(τ, ρ)` by the low-bit recursion
  `S_{n+1} = (1 − τ₀) ρ₀ eq(τ', ρ') + τ₀ (1 − ρ₀) S_n(τ', ρ')`); `shiftPair` computes
  `(eq, S)` in one pass (`shiftPair_eq`).
* The argument: `ChainLinks Out In sV hV`, the residual tables `chainD`, `chainD0`
  (**`chainLinks_iff`**: the links hold iff both vanish), **`shift_sound`** (broken links leave a
  nonzero residual: the doom of S1's start).
  - S1: `θ` (slot) and `τ` (block) coordinates, at most one bad value each (`shift_coord_le`; the
    block coordinates bind `chainD` only, `zerocheck_bad_le`), and `κ_s` at most one
    (`shift_kappa_le`).
  - S2, block rounds: the summand `eq(τ, ·) · Out_θ + (Sh_τ + κ [· = 0]) · In_θ` on the
    slot-collapsed tables (`T_θ = fixLow T θ`), degree 2 (`shift_round_le`: at most 2 per round);
    **`shift_trueSum`**: its true sum is `shiftTarget + D̃(θ, τ) + κ D̃₀(θ)`, so the target claim
    `eq(τ, last) h̃V(θ) + κ s̃V(θ)` is false exactly when the residual combination is nonzero;
    `shift_final` and `shW_mle` (`S_n(τ, ρ) + κ eq(0, ρ)`): what the verifier computes.
  - S2, collapse rounds: a slot read from `z` at the positions `pos` (`hT`) has
    `T̃(θ, ρ) = Σ_p w_θ(p) Z̃(p, ρ)` (`collapse_mle`), a degree-2 sumcheck (`innerExpr`, at most 2
    per round) ending in one claim on `z` (`collapse_final`); `slotW_mle_aligned` is the slot
    weight's closed form for a slot at an aligned base.
  - The node's two chains batched by `1, y` (`chainLinks_batch`, on bit-valued tables).

Revision 3's univariate S3 round and the range-restricted form are withdrawn by revision 3.1.
-/

namespace FR

open Finset

variable {R : Type*} [CommRing R]

/-! ## Successor -/

/-- `[v = u + 1]` on the blocks: the successor relation, with no wrap. -/
def succT {n : ℕ} (u v : Fin (2 ^ n)) : R := if v.val = u.val + 1 then 1 else 0

/-- The bilinear extension of `succT`, by the low bit: `y = x + 1` iff `x₀ = 0, y₀ = 1, y' = x'`
or `x₀ = 1, y₀ = 0, y' = x' + 1`. -/
def shiftMle : (n : ℕ) → (Fin n → R) → (Fin n → R) → R
  | 0, _, _ => 0
  | n + 1, x, y => (1 - x 0) * y 0 * eq (Fin.tail x) (Fin.tail y) +
      x 0 * (1 - y 0) * shiftMle n (Fin.tail x) (Fin.tail y)

private theorem succT_dbl {n : ℕ} (u v : Fin (2 ^ n)) (b c : Bool) :
    (succT (dbl u b) (dbl v c) : R) =
      if b then (if c then 0 else succT u v) else (if c then (if v = u then 1 else 0) else 0) := by
  unfold succT
  cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ite_eq_right (by simp only [dbl, Bool.toNat_false]; omega)
  · exact if_congr (by rw [Fin.ext_iff]; simp only [dbl, Bool.toNat_false, Bool.toNat_true]; omega)
      rfl rfl
  · exact if_congr (by simp only [dbl, Bool.toNat_false, Bool.toNat_true]; omega) rfl rfl
  · exact ite_eq_right (by simp only [dbl, Bool.toNat_true]; omega)

/-- **The successor's extension.** `Σ_{u,v} eq(τ, u) · [v = u + 1] · eq(v, ρ) = S_n(τ, ρ)`. -/
theorem shift_mle {n : ℕ} (τ ρ : Fin n → R) :
    ∑ u : Fin (2 ^ n), ∑ v : Fin (2 ^ n), eq τ (cube u) * succT u v * eq (cube v) ρ =
      shiftMle n τ ρ := by
  induction n with
  | zero =>
    rw [sum_cube_zero, sum_cube_zero]
    simp [succT, shiftMle]
  | succ n ih =>
    rw [shiftMle, ← ih (Fin.tail τ) (Fin.tail ρ), ← eq_mle (Fin.tail τ) (Fin.tail ρ),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [sum_cube_succ, eq_dbl, eq_swap (cube (dbl _ _)) ρ, succT_dbl, Bool.false_eq_true,
      ↓reduceIte, mul_zero, zero_mul, add_zero, zero_add, mul_ite, mul_one, ite_mul]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
    congr 1
    · rw [eq_swap (Fin.tail ρ) (cube u)]; ring
    · exact Finset.sum_congr rfl fun v _ ↦ by rw [eq_swap (Fin.tail ρ) (cube v)]; ring

/-! ## Computable successor extension -/

/-- `(eq(x, y), S(x, y))` in one pass over two lists. -/
@[specialize]
def shiftPair : List R → List R → R × R
  | x :: xs, y :: ys =>
    let p := shiftPair xs ys
    ((x * y + (1 - x) * (1 - y)) * p.1, (1 - x) * y * p.1 + x * (1 - y) * p.2)
  | _, _ => (1, 0)

theorem ptOf_cons (n : ℕ) (x : R) (xs : List R) :
    ptOf (n + 1) (x :: xs) = Fin.cons x (ptOf n xs) := by
  funext l
  refine Fin.cases ?_ (fun i ↦ ?_) l <;> rfl

/-- **`shiftPair` is `(eq, shiftMle)`** on points of length `n`. -/
theorem shiftPair_eq (n : ℕ) (xs ys : List R) (hx : xs.length = n) (hy : ys.length = n) :
    shiftPair xs ys = (eq (ptOf n xs) (ptOf n ys), shiftMle n (ptOf n xs) (ptOf n ys)) := by
  induction n generalizing xs ys with
  | zero =>
    rw [List.length_eq_zero_iff.mp hx, List.length_eq_zero_iff.mp hy]
    simp [shiftPair, eq, shiftMle]
  | succ n ih =>
    obtain _ | ⟨x, xs⟩ := xs
    · simp at hx
    obtain _ | ⟨y, ys⟩ := ys
    · simp at hy
    simp only [List.length_cons, add_left_inj] at hx hy
    rw [shiftPair, ih xs ys hx hy, ptOf_cons, ptOf_cons, shiftMle, eq_succ]
    simp

/-- **`shiftEq_eq`** (A.8 `shiftEq`, rev. 3.7): the computed shift is the successor's extension. -/
theorem shiftEq_eq (n : ℕ) (xs ys : List R) (hx : xs.length = n) (hy : ys.length = n) :
    (shiftPair xs ys).2 = ∑ u : Fin (2 ^ n), ∑ v : Fin (2 ^ n),
      eq (ptOf n xs) (cube u) * succT u v * eq (cube v) (ptOf n ys) := by
  rw [shiftPair_eq n xs ys hx hy, shift_mle]

/-! ## The argument (BLUEPRINT rev. 3.1 §2.3 step 4, P1-D5)

Tables on `s + n` variables (`join σ y`: slot `σ` low, block `y` high): `Out`, `In` are the slots
`h_out` and `h_in` (or `d`) of every block; `sV`, `hV` the public endpoints. The S1 coordinates
`θ` (slot) and `τ` (block) and the batching `κ` reduce the links to one claim
`Σ_y eq(τ, y) Out_θ(y) + Σ_y (Sh_τ(y) + κ [y = 0]) In_θ(y) = eq(τ, last) h̃V(θ) + κ s̃V(θ)` with
`T_θ = fixLow T θ` the slot-collapsed table; S2's block rounds run on it (degree 2), and the
collapse rounds (`collapse_*`) turn `Õut(θ, ρ)`, `Ĩn(θ, ρ)` into one claim on `z` over the
in-block positions. -/

section Argument

variable [CharP R 2] {s n : ℕ}

/-- The first block. -/
def firstBlk (n : ℕ) : Fin (2 ^ n) := ⟨0, Nat.two_pow_pos n⟩

/-- The last block. -/
def lastBlk (n : ℕ) : Fin (2 ^ n) := ⟨2 ^ n - 1, Nat.sub_lt (Nat.two_pow_pos n) one_pos⟩

omit [CharP R 2] in
/-- `Σ_{y'} [y' = y + 1] f(y')` is `f(y + 1)`, or `0` past the last block. -/
theorem sum_succT (y : Fin (2 ^ n)) (f : Fin (2 ^ n) → R) :
    ∑ y', succT y y' * f y' = if h : y.val + 1 < 2 ^ n then f ⟨y.val + 1, h⟩ else 0 := by
  simp only [succT, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨y.val + 1, h⟩ (fun y' _ hy ↦ ite_eq_right fun e ↦ hy (Fin.ext e))
      (by simp), ite_eq_left rfl]
  · exact Finset.sum_eq_zero fun y' _ ↦ ite_eq_right fun (e : y'.val = y.val + 1) ↦ h (e ▸ y'.isLt)

/-- **The chain links** (BLUEPRINT §4.1's `ChainLinks z s h`, slot by slot): the input of block
`y + 1` is the output of block `y`, the first input is `sV`, the last output is `hV`. -/
def ChainLinks (Out In : Fin (2 ^ (s + n)) → R) (sV hV : Fin (2 ^ s) → R) : Prop :=
  (∀ σ (y : Fin (2 ^ n)) (h : y.val + 1 < 2 ^ n), In (join σ ⟨y.val + 1, h⟩) = Out (join σ y)) ∧
    (∀ σ, Out (join σ (lastBlk n)) = hV σ) ∧ ∀ σ, In (join σ (firstBlk n)) = sV σ

/-- The link residual `Out(σ, y) + In(σ, y + 1)`, with `hV(σ)` in place of the missing successor
of the last block (characteristic two). -/
def chainD (Out In : Fin (2 ^ (s + n)) → R) (hV : Fin (2 ^ s) → R) (w : Fin (2 ^ (s + n))) : R :=
  let p := (joinEquiv s n).symm w
  Out w + (∑ y', succT p.2 y' * In (join p.1 y')) + if p.2 = lastBlk n then hV p.1 else 0

/-- The start residual `In(σ, 0) + sV(σ)`. -/
def chainD0 (In : Fin (2 ^ (s + n)) → R) (sV : Fin (2 ^ s) → R) (σ : Fin (2 ^ s)) : R :=
  In (join σ (firstBlk n)) + sV σ

omit [CharP R 2] in
theorem chainD_join (Out In : Fin (2 ^ (s + n)) → R) (hV : Fin (2 ^ s) → R) (σ : Fin (2 ^ s))
    (y : Fin (2 ^ n)) :
    chainD Out In hV (join σ y) =
      Out (join σ y) + (∑ y', succT y y' * In (join σ y')) + if y = lastBlk n then hV σ else 0 := by
  simp only [chainD]
  rw [show join σ y = joinEquiv s n (σ, y) from rfl, Equiv.symm_apply_apply]

/-- **The links hold iff both residual tables vanish.** -/
theorem chainLinks_iff (Out In : Fin (2 ^ (s + n)) → R) (sV hV : Fin (2 ^ s) → R) :
    ChainLinks Out In sV hV ↔ chainD Out In hV = 0 ∧ chainD0 In sV = 0 := by
  have hlast : ∀ y : Fin (2 ^ n), y = lastBlk n ↔ ¬ y.val + 1 < 2 ^ n := fun y ↦ by
    rw [Fin.ext_iff]; simp only [lastBlk]; omega
  constructor
  · rintro ⟨hl, hh, hs⟩
    refine ⟨funext fun w ↦ ?_, funext fun σ ↦ ?_⟩
    · obtain ⟨⟨σ, y⟩, rfl⟩ := (joinEquiv s n).surjective w
      change chainD Out In hV (join σ y) = 0
      rw [chainD_join, sum_succT]
      by_cases h : y.val + 1 < 2 ^ n
      · rw [dite_eq_left h, ite_eq_right ((not_congr (hlast y)).mpr (not_not.mpr h)), hl σ y h, add_zero,
          CharTwo.add_self_eq_zero]
      · have hy : y = lastBlk n := (hlast y).mpr h
        rw [dite_eq_right h, ite_eq_left hy, add_zero, hy, hh, CharTwo.add_self_eq_zero]
    · simp only [chainD0, Pi.zero_apply, hs, CharTwo.add_self_eq_zero]
  · rintro ⟨hD, hD0⟩
    refine ⟨fun σ y h ↦ ?_, fun σ ↦ ?_, fun σ ↦ ?_⟩
    · have := congrFun hD (join σ y)
      rw [chainD_join, sum_succT, dite_eq_left h, ite_eq_right ((not_congr (hlast y)).mpr (not_not.mpr h)),
        add_zero, Pi.zero_apply] at this
      exact (CharTwo.add_eq_zero.mp this).symm
    · have := congrFun hD (join σ (lastBlk n))
      rw [chainD_join, sum_succT, dite_eq_right ((hlast _).mp rfl), ite_eq_left rfl, add_zero,
        Pi.zero_apply] at this
      exact CharTwo.add_eq_zero.mp this
    · exact CharTwo.add_eq_zero.mp (congrFun hD0 σ)

/-- **`shift_sound`, start of rows S1–S2.** Broken links leave a nonzero residual table. -/
theorem shift_sound {Out In : Fin (2 ^ (s + n)) → R} {sV hV : Fin (2 ^ s) → R}
    (h : ¬ChainLinks Out In sV hV) : chainD Out In hV ≠ 0 ∨ chainD0 In sV ≠ 0 := by
  rw [chainLinks_iff, not_and_or] at h
  exact h

omit [CharP R 2] in
/-- **S1, the batching `κ_s`.** With `X ≠ 0` or `Y ≠ 0` (here `D̃(θ, τ)` and `D̃₀(θ)`), at most
one `κ` makes `X + κ Y = 0`. -/
theorem shift_kappa_le [IsDomain R] [Fintype R] [DecidableEq R] {X Y : R} (h : X ≠ 0 ∨ Y ≠ 0) :
    (univ.filter fun κ ↦ X + κ * Y = 0).card ≤ 1 := by
  have := batch2_bad_le (v₀ := X) (v₁ := Y) (t₀ := 0) (t₁ := 0) (by
    rintro ⟨⟩; simp at h)
  simpa using this

omit [CharP R 2] in
/-- **S1, one coordinate of `θ` or `τ`, two residual tables bound together** (the slot
coordinates bind both): from `t₁ ≠ 0 ∨ t₂ ≠ 0`, at most one value makes both bound tables zero.
(The block coordinates bind `t₁` only; then `zerocheck_bad_le` applies when `t₂ = 0`, and nothing
escapes when `t₂ ≠ 0`.) -/
theorem shift_coord_le [IsDomain R] [Fintype R] [DecidableEq R] {a b : ℕ}
    (t₁ : Fin (2 ^ (a + 1)) → R) (t₂ : Fin (2 ^ (b + 1)) → R) (h : t₁ ≠ 0 ∨ t₂ ≠ 0) :
    (univ.filter fun c ↦ fix0 t₁ c = 0 ∧ fix0 t₂ c = 0).card ≤ 1 := by
  rcases h with h | h
  · exact (Finset.card_le_card fun c hc ↦ by
      simp only [Finset.mem_filter] at hc ⊢; exact ⟨hc.1, hc.2.1⟩).trans (zerocheck_bad_le _ h)
  · exact (Finset.card_le_card fun c hc ↦ by
      simp only [Finset.mem_filter] at hc ⊢; exact ⟨hc.1, hc.2.2⟩).trans (zerocheck_bad_le _ h)

/-! ### S2: the block rounds -/

/-- The block weight `Sh_τ(y') + κ [y' = 0]` with `Sh_τ(y') = Σ_y eq(τ, y) [y' = y + 1]`. -/
def shW (τ : Fin n → R) (κ : R) (y' : Fin (2 ^ n)) : R :=
  (∑ y, eq τ (cube y) * succT y y') + κ * if y' = firstBlk n then 1 else 0

omit [CharP R 2] in
theorem cube_firstBlk : (cube (firstBlk n) : Fin n → R) = fun _ ↦ 0 := by
  funext l; simp [cube, firstBlk]

omit [CharP R 2] in
/-- **The block weight's extension**: `S_n(τ, ρ) + κ · eq(0, ρ)` (the verifier's `shiftTarget`). -/
theorem shW_mle (τ ρ : Fin n → R) (κ : R) :
    mle (shW τ κ) ρ = shiftMle n τ ρ + κ * eq (fun _ ↦ 0) ρ := by
  rw [← shift_mle, ← cube_firstBlk, eq_swap _ ρ]
  simp only [mle, shW, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      rw [eq_swap ρ]; ring
  · ring

/-- The S2 block summand `eq(τ, ·) · Out_θ + W · In_θ`, degree 2. -/
def shift2Expr : Expr := .add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))

theorem shift2Expr_deg : shift2Expr.deg = 2 := rfl

/-- The S2 tables on the blocks: `eq(τ, ·)`, `Out_θ`, `W`, `In_θ`. -/
def shiftTables (θ : Fin s → R) (τs : List R) (κ : R) (Out In : Fin (2 ^ (s + n)) → R) :
    Array (Array R) :=
  #[eqTable τs, Array.ofFn (fixLow Out θ), Array.ofFn (shW (ptOf n τs) κ), Array.ofFn (fixLow In θ)]

omit [CharP R 2] in
theorem shift_sizes (θ : Fin s → R) (τs : List R) (hτ : τs.length = n) (κ : R)
    (Out In : Fin (2 ^ (s + n)) → R) : ∀ t ∈ shiftTables θ τs κ Out In, t.size = 2 ^ n := by
  simp [shiftTables, eqTable_size, hτ]

/-- The verifier's target: `eq(τ, last) · h̃V(θ) + κ · s̃V(θ)`. -/
def shiftTarget (θ : Fin s → R) (τ : Fin n → R) (κ : R) (sV hV : Fin (2 ^ s) → R) : R :=
  eq τ (cube (lastBlk n)) * mle hV θ + κ * mle sV θ

omit [CharP R 2] in
private theorem shift_tbl (θ : Fin s → R) (τs : List R) (hτ : τs.length = n) (κ : R)
    (Out In : Fin (2 ^ (s + n)) → R) :
    trueSum shift2Expr (shiftTables θ τs κ Out In) n =
      ∑ y, eq (ptOf n τs) (cube y) * fixLow Out θ y + ∑ y, shW (ptOf n τs) κ y * fixLow In θ y := by
  simp only [trueSum, shift2Expr, Expr.eval, shiftTables]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  rw [tbl_eqTable' τs hτ, tbl_ofFn, tbl_ofFn, tbl_ofFn, Finset.sum_add_distrib]

/-- **The S2 true sum** is the target plus the residuals' extensions:
`trueSum = target + D̃(θ, τ) + κ D̃₀(θ)`. With links broken and S1 not bad the claim `target` is
false. -/
theorem shift_trueSum (θ : Fin s → R) (τs : List R) (hτ : τs.length = n) (κ : R)
    (Out In : Fin (2 ^ (s + n)) → R) (sV hV : Fin (2 ^ s) → R) :
    trueSum shift2Expr (shiftTables θ τs κ Out In) n =
      shiftTarget θ (ptOf n τs) κ sV hV + mle (chainD Out In hV) (Fin.append θ (ptOf n τs)) +
        κ * mle (chainD0 In sV) θ := by
  set τ := ptOf n τs
  have hD : ∀ y, fixLow (chainD Out In hV) θ y = fixLow Out θ y +
      (∑ y', succT y y' * fixLow In θ y') + if y = lastBlk n then mle hV θ else 0 := fun y ↦ by
    simp only [fixLow, chainD_join, mul_add, Finset.sum_add_distrib, mle]
    congr 1
    · congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    · split_ifs <;> simp
  have hD0 : mle (chainD0 In sV) θ = fixLow In θ (firstBlk n) + mle sV θ := by
    simp only [mle, chainD0, fixLow, mul_add, Finset.sum_add_distrib]
  have hW : ∑ y, shW τ κ y * fixLow In θ y =
      (∑ y, ∑ y', eq τ (cube y) * succT y y' * fixLow In θ y') + κ * fixLow In θ (firstBlk n) := by
    simp only [shW, add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc, ite_mul, one_mul,
      zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_comm]
  have hDτ : mle (fixLow (chainD Out In hV) θ) τ = (∑ y, eq τ (cube y) * fixLow Out θ y) +
      (∑ y, ∑ y', eq τ (cube y) * succT y y' * fixLow In θ y') +
        eq τ (cube (lastBlk n)) * mle hV θ := by
    simp only [mle, hD, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_assoc]
  rw [shift_tbl θ τs hτ, mle_fixLow, hDτ, hD0, hW, shiftTarget]
  linear_combination (-(eq τ (cube (lastBlk n)) * mle hV θ + κ * mle sV θ)) *
    CharTwo.two_eq_zero (R := R)

omit [CharP R 2] in
/-- **Row S2, one block round**: from a false claim at most 2 challenges escape. -/
theorem shift_round_le [IsDomain R] [Fintype R] [DecidableEq R] (ts : Array (Array R)) {m : ℕ}
    (hts : ∀ t ∈ ts, t.size = 2 ^ (m + 1)) {claim : R}
    (hfalse : claim ≠ trueSum shift2Expr ts (m + 1)) (g : Array R) :
    (univ.filter fun r ↦ (g.size = shift2Expr.deg + 1 ∧ peval g 0 + peval g 1 = claim) ∧
      peval g r = trueSum shift2Expr (ts.map (bind0 · r)) m).card ≤ 2 :=
  round_escape_le _ ts hts hfalse g

omit [CharP R 2] in
/-- **End of the block rounds** at `ρs`: `eq(τ, ρ) · Õut(θ, ρ) + (S(τ, ρ) + κ eq(0, ρ)) · Ĩn(θ, ρ)`. -/
theorem shift_final (θ : Fin s → R) (τs ρs : List R) (hτ : τs.length = n) (hρ : ρs.length = n)
    (κ : R) (Out In : Fin (2 ^ (s + n)) → R) :
    trueSum shift2Expr (bindAll (shiftTables θ τs κ Out In) ρs) 0 =
      eq (ptOf n τs) (ptOf n ρs) * mle Out (Fin.append θ (ptOf n ρs)) +
        (shiftMle n (ptOf n τs) (ptOf n ρs) + κ * eq (fun _ ↦ 0) (ptOf n ρs)) *
          mle In (Fin.append θ (ptOf n ρs)) := by
  rw [trueSum_bindAll' _ _ _ hρ (shift_sizes θ τs hτ κ Out In)]
  simp only [shift2Expr, Expr.eval, shiftTables]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  rw [tbl_eqTable' τs hτ, tbl_ofFn, tbl_ofFn, tbl_ofFn, mle_eqPt, shW_mle, mle_fixLow, mle_fixLow]

/-! ### S2: the collapse rounds over the in-block positions -/

/-- The slot weight of a slot placed at the positions `pos σ` (`q` position bits):
`w_θ(p) = Σ_σ eq(θ, σ) [pos σ = p]`. -/
def slotW {q : ℕ} (pos : Fin (2 ^ s) → Fin (2 ^ q)) (θ : Fin s → R) (p : Fin (2 ^ q)) : R :=
  ∑ σ, eq θ (cube σ) * if pos σ = p then 1 else 0

omit [CharP R 2] in
/-- **The collapse identity.** A slot table read from `Z` at the positions `pos` has
`T̃(θ, ρ) = Σ_p w_θ(p) · Z̃(p, ρ)`: the collapse sumcheck's true sum. -/
theorem collapse_mle {q : ℕ} (Z : Fin (2 ^ (q + n)) → R) (pos : Fin (2 ^ s) → Fin (2 ^ q))
    (T : Fin (2 ^ (s + n)) → R) (hT : ∀ σ y, T (join σ y) = Z (join (pos σ) y)) (θ : Fin s → R)
    (ρ : Fin n → R) :
    mle T (Fin.append θ ρ) = ∑ p, slotW pos θ p * mle (fun y ↦ Z (join p y)) ρ := by
  rw [mle_split]
  simp only [hT, slotW, Finset.sum_mul, ite_mul, one_mul, zero_mul, mul_assoc, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun σ _ ↦ by rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

omit [CharP R 2] in
/-- **The slot weight's extension, any slot map** (A.8 `slotW`; the chain block's `d` at 520…775 is
not aligned): `w̃_θ(r) = Σ_σ eq(θ, σ) eq(r, pos σ)`, `2^s` terms over the `q = 10` collapse
coordinates. -/
theorem slotW_mle {q : ℕ} (pos : Fin (2 ^ s) → Fin (2 ^ q)) (θ : Fin s → R) (r : Fin q → R) :
    mle (slotW pos θ) r = ∑ σ, eq θ (cube σ) * eq r (cube (pos σ)) := by
  simp only [mle, slotW, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

omit [CharP R 2] in
/-- **The slot weight's extension** for a slot at an aligned base (`pos σ = join σ c`, the low
`s` position bits free): `eq(θ, r₁) · eq(c, r₂)`. -/
theorem slotW_mle_aligned {t : ℕ} (c : Fin (2 ^ t)) (θ r₁ : Fin s → R) (r₂ : Fin t → R) :
    mle (slotW (q := s + t) (fun σ ↦ join σ c) θ) (Fin.append r₁ r₂) =
      eq θ r₁ * eq (cube c) r₂ := by
  rw [mle]
  simp only [slotW, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [eq_append_join]
  rw [← eq_mle θ r₁, Finset.sum_mul]
  exact Finset.sum_congr rfl fun σ _ ↦ by rw [eq_swap r₁, eq_swap r₂]; ring

omit [CharP R 2] in
/-- **End of the collapse rounds** at `rs`: the weight's extension times one claim on `z` at
`(r, ρ)`. -/
theorem collapse_final {q : ℕ} (W : Fin (2 ^ q) → R) (Z : Fin (2 ^ (q + n)) → R) (ρ : Fin n → R)
    (rs : List R) (hr : rs.length = q) :
    trueSum innerExpr (bindAll #[Array.ofFn W, Array.ofFn fun p ↦ mle (fun y ↦ Z (join p y)) ρ]
        rs) 0 = mle W (ptOf q rs) * mle Z (Fin.append (ptOf q rs) ρ) := by
  rw [trueSum_bindAll' _ _ _ hr (prod_sizes _ _)]
  simp only [innerExpr, Expr.eval, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, tbl_ofFn]
  rw [mle_split]
  rfl

/-! ### The chain-masked form (revision 3.14: the node's Sh, the `WM` ruling)

The node's blocks are not one chain: two digest chains `[0, N)`, `[N, 2N)`, then WOTS, `hashStmt`,
`WM`, L and M blocks, which are not linked. The masked identity links block `y` to `y + 1` only
where `lk y` holds (`y + 1` in `y`'s chain), has no end term, and its start term is
`κ Σ_{c ∈ st} [y' = c]` (the node: `st = {0, N}`). -/

section Masked
variable (lk : Fin (2 ^ n) → Prop) [DecidablePred lk] (st : Finset (Fin (2 ^ n)))

/-- **The masked chain links**: `In(σ, y + 1) = Out(σ, y)` where `lk y`; the starts' residual
`Σ_{c ∈ st} (In(σ, c) + sV(σ))` vanishes (the node: `In(σ, 0) = In(σ, N)`, characteristic two). -/
def ChainLinksM (Out In : Fin (2 ^ (s + n)) → R) (sV : Fin (2 ^ s) → R) : Prop :=
  (∀ σ (y : Fin (2 ^ n)) (h : y.val + 1 < 2 ^ n), lk y → In (join σ ⟨y.val + 1, h⟩) = Out (join σ y)) ∧
    ∀ σ, ∑ c ∈ st, (In (join σ c) + sV σ) = 0

/-- The masked link residual: `Out(σ, y) + In(σ, y + 1)` where `lk y`, else `0`. -/
def chainDM (Out In : Fin (2 ^ (s + n)) → R) (w : Fin (2 ^ (s + n))) : R :=
  let p := (joinEquiv s n).symm w
  if lk p.2 then Out w + ∑ y', succT p.2 y' * In (join p.1 y') else 0

/-- The masked start residual `Σ_{c ∈ st} (In(σ, c) + sV(σ))`. -/
def chainD0M (In : Fin (2 ^ (s + n)) → R) (sV : Fin (2 ^ s) → R) (σ : Fin (2 ^ s)) : R :=
  ∑ c ∈ st, (In (join σ c) + sV σ)

omit [CharP R 2] in
theorem chainDM_join (Out In : Fin (2 ^ (s + n)) → R) (σ : Fin (2 ^ s)) (y : Fin (2 ^ n)) :
    chainDM lk Out In (join σ y) =
      if lk y then Out (join σ y) + ∑ y', succT y y' * In (join σ y') else 0 := by
  simp only [chainDM]
  rw [show join σ y = joinEquiv s n (σ, y) from rfl, Equiv.symm_apply_apply]

/-- **`shift_sound_masked`**: on blocks whose successor exists (`hlk`), the masked links hold iff
both masked residual tables vanish; so broken masked links leave a nonzero residual. -/
theorem chainLinksM_iff (hlk : ∀ y, lk y → y.val + 1 < 2 ^ n) (Out In : Fin (2 ^ (s + n)) → R)
    (sV : Fin (2 ^ s) → R) :
    ChainLinksM lk st Out In sV ↔ chainDM lk Out In = 0 ∧ chainD0M st In sV = 0 := by
  constructor
  · rintro ⟨hl, hs⟩
    refine ⟨funext fun w ↦ ?_, funext fun σ ↦ hs σ⟩
    obtain ⟨⟨σ, y⟩, rfl⟩ := (joinEquiv s n).surjective w
    change chainDM lk Out In (join σ y) = 0
    rw [chainDM_join, sum_succT]
    split_ifs with h1 h2
    · rw [hl σ y h2 h1, CharTwo.add_self_eq_zero]
    · exact absurd (hlk y h1) h2
    · rfl
  · rintro ⟨hD, hD0⟩
    refine ⟨fun σ y h hy ↦ ?_, fun σ ↦ congrFun hD0 σ⟩
    have := congrFun hD (join σ y)
    rw [chainDM_join, sum_succT, if_pos hy, dif_pos h, Pi.zero_apply] at this
    exact (CharTwo.add_eq_zero.mp this).symm

theorem shift_sound_masked (hlk : ∀ y, lk y → y.val + 1 < 2 ^ n) {Out In : Fin (2 ^ (s + n)) → R}
    {sV : Fin (2 ^ s) → R} (h : ¬ChainLinksM lk st Out In sV) :
    chainDM lk Out In ≠ 0 ∨ chainD0M st In sV ≠ 0 := by
  rw [chainLinksM_iff lk st hlk, not_and_or] at h
  exact h

/-- **The masked block weight** (the verifier's `shW` with the interval factor):
`Σ_y eq(τ, y) [lk y] [y' = y + 1] + κ [y' ∈ st]`. -/
def shWM (τ : Fin n → R) (κ : R) (y' : Fin (2 ^ n)) : R :=
  (∑ y, eq τ (cube y) * if lk y then succT y y' else 0) + κ * if y' ∈ st then 1 else 0

/-- **The masked S2 block sum** is the target `κ Σ_{c ∈ st} s̃V(θ)` plus the residuals'
extensions: `Σ_y eq(τ,y)[lk y] Out_θ(y) + Σ_{y'} shWM(y') In_θ(y') = κ Σ_c s̃V(θ) +
D̃M(θ, τ) + κ D̃₀M(θ)`. So with links broken and S1 not bad, the masked claim is false. -/
theorem shift_sum_masked (θ : Fin s → R) (τ : Fin n → R) (κ : R) (Out In : Fin (2 ^ (s + n)) → R)
    (sV : Fin (2 ^ s) → R) :
    (∑ y, eq τ (cube y) * (if lk y then fixLow Out θ y else 0)) +
        ∑ y', shWM lk st τ κ y' * fixLow In θ y' =
      κ * ∑ _c ∈ st, mle sV θ + mle (chainDM lk Out In) (Fin.append θ τ) +
        κ * mle (chainD0M st In sV) θ := by
  have hD : ∀ y, fixLow (chainDM lk Out In) θ y =
      if lk y then fixLow Out θ y + ∑ y', succT y y' * fixLow In θ y' else 0 := fun y ↦ by
    simp only [fixLow, chainDM_join]
    split_ifs
    · simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    · simp
  have hD0 : mle (chainD0M st In sV) θ = ∑ c ∈ st, fixLow In θ c + ∑ _c ∈ st, mle sV θ := by
    simp only [mle, chainD0M, fixLow, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := univ) (t := st)]
  have hW : ∑ y', shWM lk st τ κ y' * fixLow In θ y' =
      (∑ y, ∑ y', eq τ (cube y) * (if lk y then succT y y' else 0) * fixLow In θ y') +
        κ * ∑ c ∈ st, fixLow In θ c := by
    simp only [shWM, add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc, ite_mul, one_mul,
      zero_mul, mul_ite, mul_zero, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hDτ : mle (fixLow (chainDM lk Out In) θ) τ = (∑ y, eq τ (cube y) *
      (if lk y then fixLow Out θ y else 0)) +
      ∑ y, ∑ y', eq τ (cube y) * (if lk y then succT y y' else 0) * fixLow In θ y' := by
    simp only [mle, hD, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    split_ifs <;> simp [mul_add, Finset.mul_sum, mul_assoc]
  rw [mle_fixLow, hDτ, hD0, hW]
  linear_combination (-(κ * ∑ _c ∈ st, mle sV θ)) * CharTwo.two_eq_zero (R := R)

end Masked

end Argument

/-! ### The node's two chains, batched by `1, y` -/

/-- `1, y` separate bits: `a + y b = c + y d` with `a, b, c, d ∈ {0, 1}` forces `a = c`, `b = d`. -/
theorem bits_y_inj {a b c d : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hd : d = 0 ∨ d = 1) (h : a + F.y * b = c + F.y * d) : a = c ∧ b = d := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> revert h <;> decide

/-- **The batched chains** (a node's two digest chains, BLUEPRINT §2.3 step 4): on bit-valued
tables, links of `T₁ + y T₂` are links of both. -/
theorem chainLinks_batch {s n : ℕ} {O₁ I₁ O₂ I₂ : Fin (2 ^ (s + n)) → F}
    {s₁ h₁ s₂ h₂ : Fin (2 ^ s) → F}
    (hO₁ : ∀ w, O₁ w = 0 ∨ O₁ w = 1) (hI₁ : ∀ w, I₁ w = 0 ∨ I₁ w = 1)
    (hO₂ : ∀ w, O₂ w = 0 ∨ O₂ w = 1) (hI₂ : ∀ w, I₂ w = 0 ∨ I₂ w = 1)
    (hs₁ : ∀ σ, s₁ σ = 0 ∨ s₁ σ = 1) (hh₁ : ∀ σ, h₁ σ = 0 ∨ h₁ σ = 1)
    (hs₂ : ∀ σ, s₂ σ = 0 ∨ s₂ σ = 1) (hh₂ : ∀ σ, h₂ σ = 0 ∨ h₂ σ = 1)
    (h : ChainLinks (fun w ↦ O₁ w + F.y * O₂ w) (fun w ↦ I₁ w + F.y * I₂ w)
      (fun σ ↦ s₁ σ + F.y * s₂ σ) (fun σ ↦ h₁ σ + F.y * h₂ σ)) :
    ChainLinks O₁ I₁ s₁ h₁ ∧ ChainLinks O₂ I₂ s₂ h₂ := by
  obtain ⟨hl, hh, hs⟩ := h
  have L := fun σ y hy ↦ bits_y_inj (hI₁ _) (hI₂ _) (hO₁ _) (hO₂ _) (hl σ y hy)
  have H := fun σ ↦ bits_y_inj (hO₁ _) (hO₂ _) (hh₁ σ) (hh₂ σ) (hh σ)
  have S := fun σ ↦ bits_y_inj (hI₁ _) (hI₂ _) (hs₁ σ) (hs₂ σ) (hs σ)
  exact ⟨⟨fun σ y hy ↦ (L σ y hy).1, fun σ ↦ (H σ).1, fun σ ↦ (S σ).1⟩,
    ⟨fun σ y hy ↦ (L σ y hy).2, fun σ ↦ (H σ).2, fun σ ↦ (S σ).2⟩⟩

end FR
