-- New for `flock-recursive` (revision 4.4.2, the reserve in RSV2's stacked form, §2.5–§2.6; track
-- RSV-S): the extension lemmas the E-phase's child term needs.
import FRVIREval

/-!
# Points continued above their coordinates, and the constant extension

The reserve's child claim is one point `p ∈ F^23 × F^25` and each node kind's matrices read it at
their own coordinates (`e2R κ` rows, `ncR κ` cells). A parent sums over its own `n` coordinates
with the claim's higher ones fixed (**the mixed point**): `x ↦ M̃(x ‖ p[n, …))`. Two facts make the
sumcheck and the spec agree (RSV2 §2.5):

* **`mle_eq_hiPt`**: for a cube index `u` on `a` bits, the extension in `x ∈ {0,1}^n` of
  `eq((x ‖ hi)[<a], u)` is `eq((r ‖ hi)[<a], u)` at `r`, whether `a ≤ n` (the table is constant in
  the coordinates `a … n − 1`: **the constant extension**) or `a > n` (the coordinates `n … a − 1`
  are fixed: **the fixed evaluation**);
* **`matMLE_hiRow`**, **`matMLE_hiCol`**: the same for a matrix MLE in its row or its column point.

`hiPt u hi` is the point `u` on `n` coordinates continued by `hi` above `n`; `lowA a p` reads the
first `a` coordinates of a point `p : ℕ → R`.
-/

namespace FR.Snd.Rsv
open RecursionFast Finset

section Gen
variable {R : Type*} [CommRing R]

/-- **The point `u` (on `n` coordinates) continued by `hi`** above `n`. -/
def hiPt {n : ℕ} (u : Fin n → R) (hi : ℕ → R) (j : ℕ) : R := if h : j < n then u ⟨j, h⟩ else hi j

/-- A point read at its first `a` coordinates. -/
def lowA (a : ℕ) (p : ℕ → R) : Fin a → R := fun j => p j

theorem hiPt_lt {n : ℕ} (u : Fin n → R) (hi : ℕ → R) {j : ℕ} (h : j < n) : hiPt u hi j = u ⟨j, h⟩ :=
  dif_pos h

theorem hiPt_ge {n : ℕ} (u : Fin n → R) (hi : ℕ → R) {j : ℕ} (h : ¬ j < n) : hiPt u hi j = hi j :=
  dif_neg h

/-- A point continued by itself is itself. -/
theorem hiPt_self {n : ℕ} (p : ℕ → R) : hiPt (lowA n p) p = p := by
  funext j; unfold hiPt lowA; split_ifs <;> rfl

/-- The per-bit factor of `eq(·, u)`. -/
def fb (u : ℕ) (j : ℕ) (c : R) : R := if u.testBit j then c else 1 - c

/-- `eq((v ‖ hi)[<a], u)` split at `n`: the coordinates below `n` and the constant ones above. -/
theorem eq_hiPt_split (a n : ℕ) (u : Fin (2 ^ a)) (hi : ℕ → R) (v : Fin n → R) :
    eq (lowA a (hiPt v hi)) (cube u) =
      (∏ l : Fin n, if (l : ℕ) < a then fb u.val l (v l) else 1) *
        ∏ j ∈ (range a).filter (fun j => ¬ j < n), fb u.val j (hi j) := by
  rw [eq_cube]
  have e1 : (∏ l : Fin a, if u.val.testBit l then lowA a (hiPt v hi) l else 1 - lowA a (hiPt v hi) l) =
      ∏ j ∈ range a, fb u.val j (hiPt v hi j) :=
    Fin.prod_univ_eq_prod_range (fun j => fb u.val j (hiPt v hi j)) a
  rw [e1, ← prod_filter_mul_prod_filter_not (range a) (fun j => j < n)]
  congr 1
  · rw [Fin.prod_univ_eq_prod_range (fun l => if l < a then fb u.val l (hiPt v hi l) else 1) n |>.symm.trans
      (Finset.prod_congr rfl fun l _ => by rw [hiPt_lt v hi l.isLt]) |>.symm]
    rw [prod_ite, prod_const_one, mul_one]
    refine prod_congr ?_ fun _ _ => rfl
    ext j; simp only [mem_filter, mem_range]; omega
  · exact prod_congr rfl fun j hj => by rw [hiPt_ge v hi (mem_filter.1 hj).2]

/-- **The extension of `eq((x ‖ hi)[<a], u)` in `x`** (`n` coordinates) is `eq((r ‖ hi)[<a], u)`:
the constant extension (`a ≤ n`) and the fixed evaluation (`a > n`) at once. -/
theorem mle_eq_hiPt (a n : ℕ) (u : Fin (2 ^ a)) (hi : ℕ → R) (r : Fin n → R) :
    mle (fun x : Fin (2 ^ n) => eq (lowA a (hiPt (cube x) hi)) (cube u)) r =
      eq (lowA a (hiPt r hi)) (cube u) := by
  simp only [mle, eq_hiPt_split, ← mul_assoc, ← sum_mul]
  congr 1
  simp only [eq_cube]
  have h := sum_cube_prod (R := R) (ℓ := n) fun l b =>
    (if b then r l else 1 - r l) * (if (l : ℕ) < a then fb u.val l (if b then 1 else 0) else 1)
  have e : ∀ x : Fin (2 ^ n), (∏ l : Fin n, if x.val.testBit l then r l else 1 - r l) *
      (∏ l : Fin n, if (l : ℕ) < a then fb u.val l (cube x l) else 1) =
      ∏ l : Fin n, (if x.val.testBit l then r l else 1 - r l) *
        (if (l : ℕ) < a then fb u.val l (if x.val.testBit l then 1 else 0) else 1) := fun x => by
    rw [← prod_mul_distrib]; rfl
  rw [sum_congr rfl fun x _ => e x, h]
  refine prod_congr rfl fun l _ => ?_
  by_cases hl : (l : ℕ) < a
  · simp only [hl, ↓reduceIte, fb, Bool.false_eq_true]
    split_ifs <;> ring
  · simp only [hl, ↓reduceIte, Bool.false_eq_true]; ring

end Gen

/-! ## Matrix MLEs -/

/-- `matMLE` as a row extension: `Σ_u eq(τ, u)·(Σ_y eq(σ, y) M[u][y])`. -/
theorem matMLE_row (E : Eval.Entries) {a b : ℕ} (τ : Fin a → F) (σ : Fin b → F) :
    Eval.matMLE E τ σ = ∑ u : Fin (2 ^ a), (∑ y : Fin (2 ^ b), eq σ (cube y) * Eval.entry E u y) *
      eq τ (cube u) := by
  unfold Eval.matMLE
  refine sum_congr rfl fun u _ => ?_
  rw [sum_mul]; exact sum_congr rfl fun y _ => by ring

/-- `matMLE` as a column extension. -/
theorem matMLE_col (E : Eval.Entries) {a b : ℕ} (τ : Fin a → F) (σ : Fin b → F) :
    Eval.matMLE E τ σ = ∑ y : Fin (2 ^ b), (∑ u : Fin (2 ^ a), eq τ (cube u) * Eval.entry E u y) *
      eq σ (cube y) := by
  unfold Eval.matMLE
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_mul]; exact sum_congr rfl fun u _ => by ring

/-- **A matrix MLE's row point continued by `hi`**: its extension in the low `n` row coordinates is
the matrix MLE at `r ‖ hi`. -/
theorem matMLE_hiRow (E : Eval.Entries) (a b n : ℕ) (hi : ℕ → F) (σ : Fin b → F) (r : Fin n → F) :
    mle (fun x : Fin (2 ^ n) => Eval.matMLE E (lowA a (hiPt (cube x) hi)) σ) r =
      Eval.matMLE E (lowA a (hiPt r hi)) σ := by
  simp only [matMLE_row]
  rw [mle_sum]
  exact sum_congr rfl fun u _ => by rw [mle_eq_hiPt]

/-- **… and its column point.** -/
theorem matMLE_hiCol (E : Eval.Entries) (a b n : ℕ) (hi : ℕ → F) (τ : Fin a → F) (r : Fin n → F) :
    mle (fun y : Fin (2 ^ n) => Eval.matMLE E τ (lowA b (hiPt (cube y) hi))) r =
      Eval.matMLE E τ (lowA b (hiPt r hi)) := by
  simp only [matMLE_col]
  rw [mle_sum]
  exact sum_congr rfl fun u _ => by rw [mle_eq_hiPt]


/-! ## Tables on continued points; E1's table -/

theorem mle_add' {n : ℕ} (f g : Fin (2 ^ n) → F) (r : Fin n → F) :
    mle (fun u => f u + g u) r = mle f r + mle g r := mle_add f g r

theorem mle_sub' {n : ℕ} (f g : Fin (2 ^ n) → F) (r : Fin n → F) :
    mle (fun u => f u - g u) r = mle f r - mle g r := mle_sub f g r

theorem mle_const {n : ℕ} (c : F) (r : Fin n → F) : mle (fun _ : Fin (2 ^ n) => c) r = c := by
  simp only [mle, ← sum_mul, eq_sum_one, one_mul]

/-- **A table read at its own `a` coordinates of a continued point** (`mle_eq_hiPt` summed). -/
theorem mle_hiTab {a n : ℕ} (g : Fin (2 ^ a) → F) (hi : ℕ → F) (r : Fin n → F) :
    mle (fun x : Fin (2 ^ n) => mle g (lowA a (hiPt (cube x) hi))) r = mle g (lowA a (hiPt r hi)) := by
  have e : ∀ q : Fin a → F, mle g q = ∑ u ∈ univ, g u * eq q (cube u) := fun q => by
    simp only [mle]; exact sum_congr rfl fun _ _ => mul_comm _ _
  simp only [e]
  rw [mle_sum]
  exact sum_congr rfl fun u _ => by rw [mle_eq_hiPt]

/-- The extension of a coordinate function is the coordinate. -/
theorem mle_coord {n : ℕ} (k : Fin n) (r : Fin n → F) : mle (fun u : Fin (2 ^ n) => cube u k) r = r k := by
  unfold mle
  simp only [eq_cube]
  have e : ∀ u : Fin (2 ^ n), (∏ l : Fin n, if u.val.testBit l then r l else 1 - r l) * cube u k =
      ∏ l : Fin n, (if u.val.testBit l then r l else 1 - r l) *
        (if l = k then (if u.val.testBit l then 1 else 0) else 1) := fun u => by
    rw [prod_mul_distrib, prod_ite_eq' univ k, if_pos (mem_univ _)]; rfl
  rw [sum_congr rfl fun u _ => e u, sum_cube_prod (fun l b =>
    (if b then r l else 1 - r l) * (if l = k then (if b then (1 : F) else 0) else 1))]
  rw [show (fun l : Fin n => (if false = true then r l else 1 - r l) *
      (if l = k then (if false = true then (1 : F) else 0) else 1) +
      (if true = true then r l else 1 - r l) * (if l = k then (if true = true then 1 else 0) else 1)) =
      fun l => if l = k then r l else 1 from funext fun l => by
        by_cases h : l = k <;> simp [h]]
  rw [prod_ite_eq' univ k, if_pos (mem_univ _)]

/-- **E1's table** on `n` coordinates (RSV2 §2.6): the residual `g` on its own `a` coordinates, plus
`D` times coordinate `k` (`η`): `t(x) = g(x[<a]) + D·x_k`. Its extension is `g̃(r[<a]) + D·r_k`. -/
def zcT {a n : ℕ} (k : Fin n) (g : Fin (2 ^ a) → F) (D : F) : Fin (2 ^ n) → F :=
  fun u => mle g (lowA a (hiPt (cube u) 0)) + D * cube u k

theorem mle_zcT {a n : ℕ} (k : Fin n) (g : Fin (2 ^ a) → F) (D : F) (r : Fin n → F) :
    mle (zcT k g D) r = mle g (lowA a (hiPt r 0)) + D * r k := by
  unfold zcT
  rw [mle_add', mle_hiTab, mle_smul, mle_coord]

/-- **E1's table is nonzero** when the residual is, or the child claim's defect is (`a ≤ k`). -/
theorem zcT_ne {a n : ℕ} (k : Fin n) (ha : a ≤ k.val) {g : Fin (2 ^ a) → F} {D : F}
    (h : g ≠ 0 ∨ D ≠ 0) : zcT k g D ≠ 0 := by
  intro h0
  have hm : ∀ r, mle (zcT k g D) r = 0 := fun r => by rw [h0]; simp [mle]
  let rv : Fin (2 ^ a) → F → Fin n → F := fun v c j =>
    if hj : j.val < a then cube v ⟨j, hj⟩ else if j = k then c else 0
  have hlow : ∀ v c, lowA a (hiPt (rv v c) 0) = cube v := fun v c => by
    funext j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.isLt (le_trans ha (le_of_lt k.isLt))
    simp only [lowA, hiPt, hj, dite_true, rv, j.isLt]
  have hk : ∀ v c, rv v c k = c := fun v c => by
    simp only [rv, show ¬ (k : ℕ) < a by omega, dite_false, if_pos]
  have hv : ∀ v c, g v + D * c = 0 := fun v c => by
    have := hm (rv v c); rwa [mle_zcT, hlow, hk, mle_cube] at this
  rcases h with h | h
  · exact h (funext fun v => by have := hv v 0; simpa using this)
  · exact h (by have h1 := hv 0 1; have h2 := hv 0 0; simp at h2; rw [h2] at h1; simpa using h1)

/-! ## Controls -/

/-- (+/−) `hiPt` keeps the point below `n` and reads `hi` above it. -/
theorem hiPt_ctl : hiPt (n := 1) (fun _ => (1 : F)) (fun _ => 0) 0 = 1 ∧
    hiPt (n := 1) (fun _ => (1 : F)) (fun _ => 0) 1 = 0 := ⟨rfl, rfl⟩

end FR.Snd.Rsv
