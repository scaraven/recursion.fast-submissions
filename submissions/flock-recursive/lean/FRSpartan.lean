-- New for `flock-recursive` (BLUEPRINT rev. 3.2 §2.3 steps 2, 3, 5, 7, §4, §5.2 rows Z1–Z3, L1–L2,
-- Lr, E). The sparse-R1CS part ("Spartan") is copied from
-- `submissions/spartan-srom/lean/SpartanSromSoundnessSpartan.lean` (this repository, `783328c`),
-- namespace `SpartanSrom` → `FR`; that file was ported from v3 `spartan-chain` (local `main` at
-- `1f59b38`).
import FRSkip
import FRShift

/-!
# Zerocheck and lincheck soundness (rows Z1–Z3, L1–L2, Lr1–Lr4, E1–E4)

**The block zerocheck** (rev. 3.2 §2.3 step 2, §4). The witness is laid out as 64 skip slices
`i` (the 6 low position bits, ranging over `S`) of tables on the other `ℓ = m − 6` variables `u`.
The tables `a = (I ⊗ A₀) z`, `b = (I ⊗ B₀) z`, `z` and the public target `E` are bit-valued; `Sel`
(the used-block indicator) is a bit-valued table on `u` (constant along positions). The relation
`BHolds`: `a · b = z + E` wherever `Sel = 1` (characteristic two). The residual
`bzRes i u = Sel(u) · (a b + z + E)` is bit-valued.

| step | doom | lemma | count |
|---|---|---|---|
| start | some residual slice nonzero | `bz_start` | — |
| Z1 pinned (7 coordinates) | still nonzero after `fixLow` at `ρ` | `pinned_sound` (`FRSkip`) | 0 |
| Z1 free coordinates | still nonzero | `zerocheck_bad_le` | 1 each |
| Z1 end | `P*(node i) ≠ 0` for some `i ∈ S` | `bz_end`, `bzPoly_node` | — |
| Z2 `λ` | the interpolated claim `≠ P*(λ)` | `zc_skip_bad_le` (`FRSkip`), `bzPoly_natDegree` (≤ 126) | 127 |
| Z3 rounds | `claim ≠ trueSum` (`bzExpr = w(ab + z) + W_E`, degree 3) | `round_escape_le` | 3 each |
| Z3 end | the triple `(â, b̂, ẑ)` is wrong | `bz_final`, `bz_triple_wrong` | — |

`P*(Y) = Σ_u ŵ(u) (Â(Y,u) B̂(Y,u) + Ẑ(Y,u) + Ê(Y,u))` with `ŵ = eq(r,·) Sel` (the weight of
BP-C-R4-m1, never `Sel ⊗ A₀`) and `Â(Y, u)` the quirky (skip-interpolated) extension
`skipExt`. **The weight's final value** is a prefix sum: `prefixP` sums a product weight
`Π_l e_l(x_l)` over `x < c` in `O(n²)` (`prefixP_eq`); `selWeight_eq` gives
`ŵ(r′) = Σ_x eq(r′,x) eq(r,x) Sel(x)` over `Sel`'s intervals (`selOf`) as differences of
`prefixP`, and `selWeight_split` separates the position part (`eq(r_pos, r′_pos)`) from the block
part. It is not `eq(r, r′) · Sẽl(r′)` (`selWeight_ne_control`).

**The lincheck, per kind** (rev. 3.4, S-C-M1): `A = Σ_κ Ind_κ ⊗ A₀^κ`; the sumcheck runs on the
per-kind folded columns (`kindExpr`, `kindTables`, `zfoldK`; degree 2): `lin_trueSum_kinds`
(true sum `â* + α b̂*`, `linAK`), `lin_final_kinds` (`Σ_κ M̃_κ(r_k) v_κ`), `lin_walk_adjust` (one
walk with `rw′ = rw · Σ_κ v_κ free_κ`), `zfoldK_mle` and `lin_beta_claim` (the `v_κ` batched by
`β` are one weighted claim with the public weight `W_β`), `lin_beta_le` (row L3: 6 of `|F|` for 7
kinds). Z3's summand is `w · (ab + z) + W_E` (S-C-M2; `targetMLE_eq` gives `Ŵ_E(λ, ρ)`).

**The single-kind lincheck** (step 3, 14 rounds of degree 2, P1-D4; the leaf). For in-block matrices `A₀, B₀` on
`2^p` positions, row weights `rw` (the quirky row point: Lagrange at `λ` on the skip bits, `eq` on
the rest; computed by the verifier) and the block point `r_blk`, the true values are
`â* = Σ_t eq(r_blk, t) Σ_k rw(k) (A₀ z_t)(k)` (`linA`); `α` batches (`batch2_bad_le`: 1);
`lin_trueSum`: the sum `Σ_j M_α(j) z̄(j)` (`z̄ = z` folded over the blocks at `r_blk`) is
`â* + α b̂*`; rounds `innerExpr` (2 each); `lin_final`: one multilinear claim `ẑ(r_k, r_blk)`.

**Sparse R1CS** (Lr, E; spartan-srom's R1–R4 doom table, unchanged): `Sat`, `residual`,
`matMle`, `zc_start`, `zc_escape_le` (1), `zc_end`, `outerExpr` (3 per round), `outer_final`,
`triple_wrong`, `batch_escape_le` (2), `innerTables`, `inner_final`.
-/

namespace FR

open Finset Polynomial

/-! ## The abstract R1CS -/

section R1CS

variable {E : Type*} [Field E] {a b : ℕ}

/-- `(M z)(x) = Σ_y M(x, y) · z(y)`. -/
def matVec (M : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) : Fin (2 ^ a) → E :=
  fun x ↦ ∑ y, M x y * z y

/-- `M̃(r_x, r_y) = Σ_{x, y} eq(r_x, x) · eq(r_y, y) · M(x, y)`. -/
def matMle (M : Fin (2 ^ a) → Fin (2 ^ b) → E) (rx : Fin a → E) (ry : Fin b → E) : E :=
  ∑ x, ∑ y, eq rx (cube x) * eq ry (cube y) * M x y

/-- The R1CS holds: `(Az)(x) · (Bz)(x) = (Cz)(x)` on the cube. -/
def Sat (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) : Prop :=
  ∀ x, matVec A z x * matVec B z x = matVec C z x

/-- The residual `F(x) = (Az)(x) · (Bz)(x) + (Cz)(x)` (characteristic two: `-` is `+`). -/
def residual (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) : Fin (2 ^ a) → E :=
  fun x ↦ matVec A z x * matVec B z x + matVec C z x

theorem matMle_cube (M : Fin (2 ^ a) → Fin (2 ^ b) → E) (rx : Fin a → E) (y : Fin (2 ^ b)) :
    matMle M rx (cube y) = ∑ x, eq rx (cube x) * M x y := by
  simp [matMle, eq_cube_cube]

/-- `(Mz)~(r_x) = Σ_y M̃(r_x, y) · z(y)`. -/
theorem mle_matVec (M : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) (rx : Fin a → E) :
    mle (matVec M z) rx = ∑ y, matMle M rx (cube y) * z y := by
  simp only [mle, matVec, matMle_cube, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The extension in `y` of `M̃(r_x, y)` on the cube is `M̃(r_x, ·)`. -/
theorem mle_matMle (M : Fin (2 ^ a) → Fin (2 ^ b) → E) (rx : Fin a → E) (ry : Fin b → E) :
    mle (fun y ↦ matMle M rx (cube y)) ry = matMle M rx ry := by
  simp only [mle, matMle_cube, Finset.mul_sum]
  rw [matMle, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

theorem mle_comb {ℓ : ℕ} (p q s : Fin (2 ^ ℓ) → E) (ρ : E) (r : Fin ℓ → E) :
    mle (fun u ↦ p u + ρ * q u + ρ ^ 2 * s u) r = mle p r + ρ * mle q r + ρ ^ 2 * mle s r := by
  simp only [mle, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-! ### R1: the zerocheck coordinates -/

/-- **Start.** An unsatisfied R1CS has a nonzero residual table (`P_0 ≢ 0`). -/
theorem zc_start [CharP E 2] {A B C : Fin (2 ^ a) → Fin (2 ^ b) → E} {z : Fin (2 ^ b) → E}
    (h : ¬Sat A B C z) : tbl a (Array.ofFn (residual A B C z)) ≠ 0 := by
  rw [tbl_ofFn]
  intro hr
  refine h fun x ↦ ?_
  have := congrFun hr x
  simp only [residual, Pi.zero_apply] at this
  exact eq_of_sub_eq_zero (by rwa [CharTwo.sub_eq_add])

/-- **R1, one coordinate.** From a nonzero bound table (doomed), at most one value of the next
coordinate makes the bound table zero (escape). -/
theorem zc_escape_le [Fintype E] [DecidableEq E] (t : Array E) {m : ℕ}
    (ht : t.size = 2 ^ (m + 1)) (hd : tbl (m + 1) t ≠ 0) :
    (univ.filter fun c ↦ tbl m (bind0 t c) = 0).card ≤ 1 := by
  simp only [tbl_bind0 t _ ht]
  exact zerocheck_bad_le _ hd

/-- **End of R1.** With every coordinate drawn and the bound table still nonzero, `F̃(τ) ≠ 0`. -/
theorem zc_end (t : Array E) (τs : List E) (ht : t.size = 2 ^ τs.length)
    (hd : tbl 0 (bindT t τs) ≠ 0) : mle (tbl τs.length t) (pt τs) ≠ 0 := fun h ↦
  hd (funext fun u ↦ by rw [tbl_bindT t τs ht, h]; rfl)

/-! ### R2: the outer sumcheck -/

/-- The outer summand `eq(τ, x) · ((Az)(x) · (Bz)(x) + (Cz)(x))`, degree 3. -/
def outerExpr : Expr := .mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3))

theorem outerExpr_deg : outerExpr.deg = 3 := rfl

/-- The outer tables: `eq(τ, ·)`, `Az`, `Bz`, `Cz`. -/
def outerTables (τs : List E) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) :
    Array (Array E) :=
  #[eqTable τs, Array.ofFn (matVec A z), Array.ofFn (matVec B z), Array.ofFn (matVec C z)]

theorem outer_sizes (τs : List E) (hτ : τs.length = a) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E)
    (z : Fin (2 ^ b) → E) : ∀ t ∈ outerTables τs A B C z, t.size = 2 ^ a := by
  simp [outerTables, eqTable_size, hτ]

/-- The outer true sum is the zerocheck polynomial at `τ`: `Σ_x eq(τ, x) F(x) = F̃(τ)`. -/
theorem outer_trueSum (τs : List E) (hτ : τs.length = a) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E)
    (z : Fin (2 ^ b) → E) :
    trueSum outerExpr (outerTables τs A B C z) a = mle (residual A B C z) (ptOf a τs) := by
  simp only [trueSum, mle, outerTables, outerExpr, Expr.eval]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp [tbl_ofFn, tbl_eqTable' τs hτ, residual]

/-- **Start of R2.** With `F̃(τ) ≠ 0` the outer claim `0` is false. -/
theorem outer_start (τs : List E) (hτ : τs.length = a) {A B C : Fin (2 ^ a) → Fin (2 ^ b) → E}
    {z : Fin (2 ^ b) → E} (h : mle (residual A B C z) (ptOf a τs) ≠ 0) :
    (0 : E) ≠ trueSum outerExpr (outerTables τs A B C z) a := by
  rw [outer_trueSum τs hτ]
  exact h.symm

/-- **End of R2.** All variables bound: the true value is
`eq(τ, r_x) · ((Az)~(r_x) · (Bz)~(r_x) + (Cz)~(r_x))`. -/
theorem outer_final (τs rx : List E) (hτ : τs.length = a) (hx : rx.length = a)
    (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) :
    trueSum outerExpr (bindAll (outerTables τs A B C z) rx) 0 =
      eq (ptOf a τs) (ptOf a rx) * (mle (matVec A z) (ptOf a rx) * mle (matVec B z) (ptOf a rx) +
        mle (matVec C z) (ptOf a rx)) := by
  subst hx
  rw [trueSum_bindAll _ _ _ (outer_sizes τs hτ A B C z)]
  simp only [outerExpr, Expr.eval, outerTables, ← pt_eq_ptOf]
  simp [tbl_ofFn, tbl_eqTable' τs hτ, mle_eqPt]

/-- **After R2.** A false final claim that passes the check has a wrong triple. -/
theorem triple_wrong {claim e vA vB vC tA tB tC : E} (hdoom : claim ≠ e * (tA * tB + tC))
    (hchk : claim = e * (vA * vB + vC)) : (vA, vB, vC) ≠ (tA, tB, tC) := by
  intro h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact hdoom hchk

/-! ### R3, R4: batching and the inner sumcheck -/

/-- The inner tables: `M̃_ρ(r_x, ·) = Ã + ρ B̃ + ρ² C̃` on the cube, and `z`. -/
def innerTables (rx : Fin a → E) (ρ : E) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E)
    (z : Fin (2 ^ b) → E) : Array (Array E) :=
  #[Array.ofFn fun y ↦
      matMle A rx (cube y) + ρ * matMle B rx (cube y) + ρ ^ 2 * matMle C rx (cube y),
    Array.ofFn z]

/-- The inner true sum is the batched true triple. -/
theorem inner_trueSum (rx : Fin a → E) (ρ : E) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E)
    (z : Fin (2 ^ b) → E) :
    trueSum innerExpr (innerTables rx ρ A B C z) b =
      mle (matVec A z) rx + ρ * mle (matVec B z) rx + ρ ^ 2 * mle (matVec C z) rx := by
  rw [innerTables, prod_trueSum, mle_matVec, mle_matVec, mle_matVec, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **R3.** With a wrong triple, at most two `ρ` make the batched claim true. -/
theorem batch_escape_le [Fintype E] [DecidableEq E] (rx : Fin a → E)
    (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E) (z : Fin (2 ^ b) → E) {vA vB vC : E}
    (h : (vA, vB, vC) ≠ (mle (matVec A z) rx, mle (matVec B z) rx, mle (matVec C z) rx)) :
    (univ.filter fun ρ ↦
      vA + ρ * vB + ρ ^ 2 * vC = trueSum innerExpr (innerTables rx ρ A B C z) b).card ≤ 2 := by
  simp only [inner_trueSum]
  exact batch_bad_le h

/-- **End of R4.** All variables bound: the true value is `M̃_ρ(r_x, r_y) · z̃(r_y)`. -/
theorem inner_final (rx : Fin a → E) (ρ : E) (A B C : Fin (2 ^ a) → Fin (2 ^ b) → E)
    (z : Fin (2 ^ b) → E) (ry : List E) (hy : ry.length = b) :
    trueSum innerExpr (bindAll (innerTables rx ρ A B C z) ry) 0 =
      (matMle A rx (ptOf b ry) + ρ * matMle B rx (ptOf b ry) + ρ ^ 2 * matMle C rx (ptOf b ry)) *
        mle z (ptOf b ry) := by
  subst hy
  rw [innerTables, trueSum_bindAll _ _ _ (prod_sizes _ _)]
  simp only [innerExpr, Expr.eval, ← pt_eq_ptOf]
  simp [tbl_ofFn, mle_comb, mle_matMle]

end R1CS

/-! ## Prefix sums of product weights (the zerocheck weight `ŵ(r′)`) -/

section Prefix

variable {R : Type*} [CommRing R]

/-- `Π_l e_l(bit l of c)` for `c < 2^n`, and `0` above. -/
def prodAt {n : ℕ} (e : Fin n → Bool → R) (c : ℕ) : R :=
  if c < 2 ^ n then ∏ l : Fin n, e l (c.testBit l) else 0

/-- `Σ_{x < c} Π_l e_l(x_l)` by the low bit, `O(n²)`. -/
def prefixP : (n : ℕ) → (Fin n → Bool → R) → ℕ → R
  | 0, _, c => if 0 < c then 1 else 0
  | n + 1, e, c => (e 0 false + e 0 true) * prefixP n (fun l ↦ e l.succ) (c / 2) +
      if c % 2 = 1 then e 0 false * prodAt (fun l ↦ e l.succ) (c / 2) else 0

private theorem sum_eq_prodAt {n : ℕ} (e : Fin n → Bool → R) (d : ℕ) :
    ∑ u : Fin (2 ^ n), (if u.val = d then ∏ l : Fin n, e l (u.val.testBit l) else 0) =
      prodAt e d := by
  unfold prodAt
  split_ifs with hd
  · rw [Finset.sum_eq_single ⟨d, hd⟩ (fun u _ hu ↦ ite_eq_right fun h ↦ hu (Fin.ext h)) (by simp),
      ite_eq_left rfl]
  · exact Finset.sum_eq_zero fun u _ ↦ ite_eq_right fun (h : u.val = d) ↦ hd (h ▸ u.isLt)

/-- **`prefixP` is the prefix sum.** -/
theorem prefixP_eq (n : ℕ) (e : Fin n → Bool → R) (c : ℕ) :
    prefixP n e c = ∑ x : Fin (2 ^ n), if x.val < c then ∏ l : Fin n, e l (x.val.testBit l) else 0 := by
  induction n generalizing c with
  | zero =>
    rw [sum_cube_zero]
    simp [prefixP]
  | succ n ih =>
    rw [prefixP, ih, ← sum_eq_prodAt, sum_cube_succ, Finset.mul_sum]
    have key : ∀ u : Fin (2 ^ n), ∀ b : Bool, ∏ l : Fin (n + 1), e l ((dbl u b).val.testBit l) =
        e 0 b * ∏ l : Fin n, e l.succ (u.val.testBit l) := fun u b ↦ by
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, testBit_dbl_zero, Fin.val_succ, testBit_dbl_succ]
    simp only [key]
    rw [show (if c % 2 = 1 then e 0 false * ∑ u : Fin (2 ^ n),
        (if u.val = c / 2 then ∏ l : Fin n, e l.succ (u.val.testBit l) else 0) else 0) =
        ∑ u : Fin (2 ^ n), (if c % 2 = 1 then e 0 false *
          (if u.val = c / 2 then ∏ l : Fin n, e l.succ (u.val.testBit l) else 0) else 0) by
      split_ifs <;> simp [Finset.mul_sum], ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    have e0 : (dbl u false).val = 2 * u.val := by simp [dbl]
    have e1 : (dbl u true).val = 2 * u.val + 1 := by simp [dbl]
    simp only [e0, e1]
    split_ifs <;> first | ring1 | (exfalso; omega)

end Prefix


section SelW

variable {R : Type*} [CommRing R]

/-- The product weight of `eq(r′, x) · eq(r, x)`, bit by bit. -/
def eW {n : ℕ} (r r' : Fin n → R) (l : Fin n) (b : Bool) : R :=
  (if b then r' l else 1 - r' l) * if b then r l else 1 - r l

/-- `Sel` as a sum of interval indicators `[a ≤ x < b]`. -/
def selOf {n : ℕ} (ivs : List (ℕ × ℕ)) (x : Fin (2 ^ n)) : R :=
  (ivs.map fun p ↦ if p.1 ≤ x.val ∧ x.val < p.2 then (1 : R) else 0).sum

/-- **The zerocheck weight's final value** (`selWeight`, BP-C-R4-m1): `ŵ(r′) = Σ_x eq(r′, x)
eq(r, x) Sel(x)` is the sum over `Sel`'s intervals of differences of prefix sums. -/
theorem selWeight_eq {n : ℕ} (r r' : Fin n → R) (ivs : List (ℕ × ℕ))
    (h : ∀ p ∈ ivs, p.1 ≤ p.2) :
    mle (fun x ↦ eq r (cube x) * selOf ivs x) r' =
      (ivs.map fun p ↦ prefixP n (eW r r') p.2 - prefixP n (eW r r') p.1).sum := by
  have hprod : ∀ x : Fin (2 ^ n), eq r' (cube x) * eq r (cube x) =
      ∏ l : Fin n, eW r r' l (x.val.testBit l) := fun x ↦ by
    rw [eq_cube, eq_cube, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun l _ ↦ by unfold eW; split_ifs <;> rfl
  induction ivs with
  | nil => simp [selOf, mle]
  | cons p ps ih =>
    have hp := h p (List.mem_cons_self ..)
    rw [List.map_cons, List.sum_cons, ← ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq),
      prefixP_eq, prefixP_eq, ← Finset.sum_sub_distrib]
    simp only [selOf, List.map_cons, List.sum_cons, mle, mul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← mul_assoc, hprod]
    split_ifs <;> first | ring1 | (exfalso; omega)

/-- `ŵ` splits into the position part and the block part when `Sel` depends on the block only
(positions low, blocks high). -/
theorem selWeight_split {p q : ℕ} (rp r'p : Fin p → R) (rb r'b : Fin q → R)
    (SelB : Fin (2 ^ q) → R) :
    mle (fun x : Fin (2 ^ (p + q)) ↦ eq (Fin.append rp rb) (cube x) * SelB ((joinEquiv p q).symm x).2)
        (Fin.append r'p r'b) =
      eq rp r'p * mle (fun t ↦ eq rb (cube t) * SelB t) r'b := by
  rw [mle_split]
  simp only [mle, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have hj : ∀ a, ((joinEquiv p q).symm (join a t)).2 = t := fun a ↦ by
    rw [show join a t = joinEquiv p q (a, t) from rfl, Equiv.symm_apply_apply]
  simp only [hj, eq_append_join]
  rw [← eq_mle rp r'p, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [eq_swap r'p]; ring

end SelW

/-! ## The block zerocheck (rows Z1–Z3) -/

section BZ

variable {ℓ : ℕ}

/-- **The block R1CS with the public target holds** on the used blocks: `a b = z + E`
(characteristic two) wherever `Sel = 1`. -/
def BHolds (Sel : Fin (2 ^ ℓ) → F) (a b z E : Fin 64 → Fin (2 ^ ℓ) → F) : Prop :=
  ∀ i u, Sel u = 1 → a i u * b i u = z i u + E i u

/-- The residual slice `i`: `Sel(u) · (a b + z + E)`. -/
def bzRes (Sel : Fin (2 ^ ℓ) → F) (a b z E : Fin 64 → Fin (2 ^ ℓ) → F) (i : Fin 64)
    (u : Fin (2 ^ ℓ)) : F :=
  Sel u * (a i u * b i u + z i u + E i u)

/-- **Start of Z1.** A violated relation leaves a nonzero residual slice. -/
theorem bz_start {Sel : Fin (2 ^ ℓ) → F} {a b z E : Fin 64 → Fin (2 ^ ℓ) → F}
    (h : ¬BHolds Sel a b z E) :
    ∃ i, bzRes Sel a b z E i ≠ 0 := by
  by_contra hall
  push Not at hall
  refine h fun i u hu ↦ ?_
  have := congrFun (hall i) u
  simp only [bzRes, hu, one_mul, Pi.zero_apply] at this
  rw [add_assoc] at this
  exact CharTwo.add_eq_zero.mp this

theorem isBit_mul {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) : x * y = 0 ∨ x * y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

theorem isBit_add {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) : x + y = 0 ∨ x + y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [CharTwo.add_self_eq_zero]

/-- The residual is bit-valued (the hypothesis of `pinned_sound`). -/
theorem bzRes_bit {Sel : Fin (2 ^ ℓ) → F} {a b z E : Fin 64 → Fin (2 ^ ℓ) → F}
    (hSel : ∀ u, Sel u = 0 ∨ Sel u = 1) (ha : ∀ i u, a i u = 0 ∨ a i u = 1)
    (hb : ∀ i u, b i u = 0 ∨ b i u = 1) (hz : ∀ i u, z i u = 0 ∨ z i u = 1)
    (hE : ∀ i u, E i u = 0 ∨ E i u = 1) (i : Fin 64) (u : Fin (2 ^ ℓ)) :
    bzRes Sel a b z E i u = 0 ∨ bzRes Sel a b z E i u = 1 :=
  isBit_mul (hSel u) (isBit_add (isBit_add (isBit_mul (ha i u) (hb i u)) (hz i u)) (hE i u))

/-- The castLE of a skip index into the 128 nodes. -/
abbrev sNode (i : Fin 64) : Fin 128 := Fin.castLE (by norm_num) i

/-- The honest Z2 polynomial `P*(Y) = Σ_u eq(r, u) Sel(u) (Â(Y,u) B̂(Y,u) + Ẑ(Y,u) + Ê(Y,u))`. -/
noncomputable def bzPoly (r : Fin ℓ → F) (Sel : Fin (2 ^ ℓ) → F) (a b z E : Fin 64 → Fin (2 ^ ℓ) → F) :
    F[X] :=
  ∑ u, C (eq r (cube u) * Sel u) * (skipExt (fun i ↦ a i u) * skipExt (fun i ↦ b i u) +
    skipExt (fun i ↦ z i u) + skipExt (fun i ↦ E i u))

/-- `P*` has degree at most `126 ≤ 127`. -/
theorem bzPoly_natDegree (r : Fin ℓ → F) (Sel : Fin (2 ^ ℓ) → F)
    (a b z E : Fin 64 → Fin (2 ^ ℓ) → F) : (bzPoly r Sel a b z E).natDegree ≤ 127 := by
  refine natDegree_sum_le_of_forall_le _ _ fun u _ ↦ (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · exact (natDegree_mul_le).trans (by
      have := skipExt_natDegree (fun i ↦ a i u); have := skipExt_natDegree (fun i ↦ b i u); omega)
  · exact (skipExt_natDegree _).trans (by norm_num)
  · exact (skipExt_natDegree _).trans (by norm_num)

/-- At a node of `S`, `P*` is the residual slice's extension at `r`. -/
theorem bzPoly_node (r : Fin ℓ → F) (Sel : Fin (2 ^ ℓ) → F) (a b z E : Fin 64 → Fin (2 ^ ℓ) → F)
    (i : Fin 64) : (bzPoly r Sel a b z E).eval (skipNode (sNode i)) = mle (bzRes Sel a b z E i) r := by
  simp only [bzPoly, eval_finsetSum, eval_mul, eval_add, eval_C, skipExt_node, mle, bzRes]
  exact Finset.sum_congr rfl fun u _ ↦ by ring

/-- **End of Z1.** A nonzero residual extension at `r` makes `P*` nonzero at a node of `S`: the
hypothesis of `zc_skip_bad_le` (row Z2, 127 bad `λ`). -/
theorem bz_end {r : Fin ℓ → F} {Sel : Fin (2 ^ ℓ) → F} {a b z E : Fin 64 → Fin (2 ^ ℓ) → F}
    {i : Fin 64} (h : mle (bzRes Sel a b z E i) r ≠ 0) :
    ∃ b' : Fin 128, b'.val < 64 ∧ (bzPoly r Sel a b z E).eval (skipNode b') ≠ 0 :=
  ⟨sNode i, i.isLt, by rwa [bzPoly_node]⟩

/-- **Row Z2.** From a nonzero residual at `r`, at most 127 values of `λ` make the verifier's
interpolated claim true, whatever the message. -/
theorem bz_skip_le {r : Fin ℓ → F} {Sel : Fin (2 ^ ℓ) → F} {a b z E : Fin 64 → Fin (2 ^ ℓ) → F}
    {i : Fin 64} (h : mle (bzRes Sel a b z E i) r ≠ 0) (msg : Fin 64 → F) :
    (univ.filter fun l ↦ lagrangeS (zcMsg msg) l = (bzPoly r Sel a b z E).eval l).card ≤ 127 :=
  zc_skip_bad_le msg _ (bzPoly_natDegree r Sel a b z E) (bz_end h)

/-- The Z3 summand `w · (A B + Z) + W_E` (rev. 3.4, S-C-M2), degree 3. -/
def bzExpr : Expr := .add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3))) (.var 4)

theorem bzExpr_deg : bzExpr.deg = 3 := rfl

/-- The Z3 tables at `λ`: `w = eq(r, ·) Sel`, `Â(λ, ·)`, `B̂(λ, ·)`, `Ẑ(λ, ·)`, and the target's
weighted table `W_E = eq(r, ·) Sel Ê(λ, ·)`. -/
noncomputable def bzTables (rs : List F) (l : F) (Sel : Fin (2 ^ ℓ) → F)
    (a b z E : Fin 64 → Fin (2 ^ ℓ) → F) : Array (Array F) :=
  #[Array.ofFn fun u ↦ eq (ptOf ℓ rs) (cube u) * Sel u,
    Array.ofFn fun u ↦ (skipExt fun i ↦ a i u).eval l,
    Array.ofFn fun u ↦ (skipExt fun i ↦ b i u).eval l,
    Array.ofFn fun u ↦ (skipExt fun i ↦ z i u).eval l,
    Array.ofFn fun u ↦ eq (ptOf ℓ rs) (cube u) * Sel u * (skipExt fun i ↦ E i u).eval l]

theorem bz_sizes (rs : List F) (l : F) (Sel : Fin (2 ^ ℓ) → F)
    (a b z E : Fin 64 → Fin (2 ^ ℓ) → F) : ∀ t ∈ bzTables rs l Sel a b z E, t.size = 2 ^ ℓ := by
  simp [bzTables]

/-- **The Z3 true sum is `P*(λ)`.** -/
theorem bz_trueSum (rs : List F) (l : F) (Sel : Fin (2 ^ ℓ) → F)
    (a b z E : Fin 64 → Fin (2 ^ ℓ) → F) :
    trueSum bzExpr (bzTables rs l Sel a b z E) ℓ = (bzPoly (ptOf ℓ rs) Sel a b z E).eval l := by
  simp only [trueSum, bzExpr, Expr.eval, bzTables, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    tbl_ofFn, bzPoly, eval_finsetSum, eval_mul, eval_add, eval_C]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **End of Z3.** All variables bound at `ρs`: `ŵ(ρ) · (Ã B̃ + Z̃)(λ, ρ) + Ŵ_E(λ, ρ)`, each factor
the extension of its table. -/
theorem bz_final (rs ρs : List F) (hρ : ρs.length = ℓ) (l : F) (Sel : Fin (2 ^ ℓ) → F)
    (a b z E : Fin 64 → Fin (2 ^ ℓ) → F) :
    trueSum bzExpr (bindAll (bzTables rs l Sel a b z E) ρs) 0 =
      mle (fun u ↦ eq (ptOf ℓ rs) (cube u) * Sel u) (ptOf ℓ ρs) *
          (mle (fun u ↦ (skipExt fun i ↦ a i u).eval l) (ptOf ℓ ρs) *
              mle (fun u ↦ (skipExt fun i ↦ b i u).eval l) (ptOf ℓ ρs) +
            mle (fun u ↦ (skipExt fun i ↦ z i u).eval l) (ptOf ℓ ρs)) +
        mle (fun u ↦ eq (ptOf ℓ rs) (cube u) * Sel u * (skipExt fun i ↦ E i u).eval l)
          (ptOf ℓ ρs) := by
  rw [trueSum_bindAll' _ _ _ hρ (bz_sizes rs l Sel a b z E)]
  simp only [bzExpr, Expr.eval, bzTables, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, tbl_ofFn]

/-- **After Z3.** A false final claim that passes the check (with the verifier's own `ŵ`, `Ŵ_E`)
has a wrong triple `(â, b̂, ẑ)`. -/
theorem bz_triple_wrong {claim w we va vb vz ta tb tz : F}
    (hdoom : claim ≠ w * (ta * tb + tz) + we) (hchk : claim = w * (va * vb + vz) + we) :
    (va, vb, vz) ≠ (ta, tb, tz) := by
  rintro ⟨⟩
  exact hdoom hchk

/-- **`targetMLE`** (A.8): the target's weighted extension at `(λ, ρ)` is the per-position sum
`Σ_i Σ_hi Σ_blk L_i(λ) · eq(r_hi, hi) eq(ρ_hi, hi) · eq(r_blk, blk) eq(ρ_blk, blk) Sel(blk) ·
E(i, hi, blk)` (positions `hi` low, blocks high; only the pinned positions, `E ≠ 0`, contribute). -/
theorem targetMLE_eq {p q : ℕ} (rhi ρhi : Fin p → F) (rb ρb : Fin q → F) (SelB : Fin (2 ^ q) → F)
    (E : Fin 64 → Fin (2 ^ (p + q)) → F) (l : F) :
    mle (fun u ↦ eq (Fin.append rhi rb) (cube u) * SelB ((joinEquiv p q).symm u).2 *
        (skipExt fun i ↦ E i u).eval l) (Fin.append ρhi ρb) =
      ∑ i : Fin 64, ∑ hi : Fin (2 ^ p), ∑ t : Fin (2 ^ q),
        lagrangeWeight (fun b : Fin 64 ↦ skipNode (Fin.castLE (by norm_num) b)) l i *
          (eq rhi (cube hi) * eq ρhi (cube hi)) * (eq rb (cube t) * eq ρb (cube t)) * SelB t *
            E i (join hi t) := by
  rw [mle, ← (joinEquiv p q).sum_comp, Fintype.sum_prod_type]
  simp only [skipExt_eval, Finset.mul_sum, Equiv.symm_apply_apply]
  conv_lhs => enter [2, hi]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun hi _ ↦
    Finset.sum_congr rfl fun t _ ↦ ?_
  rw [show (joinEquiv p q) (hi, t) = join hi t from rfl, eq_append_join, eq_append_join]
  ring

end BZ

/-! ## The lincheck (rows L1–L2) -/

section Lin

variable {R : Type*} [CommRing R] {p q : ℕ}

/-- `â* = Σ_t eq(r_blk, t) Σ_k rw(k) (A₀ z_t)(k)`: `(I ⊗ A₀) z` at the row point `(rw, r_blk)`
(positions low, blocks high). -/
def linA (A₀ : Fin (2 ^ p) → Fin (2 ^ p) → R) (rw : Fin (2 ^ p) → R) (rb : Fin q → R)
    (z : Fin (2 ^ (p + q)) → R) : R :=
  ∑ t : Fin (2 ^ q), eq rb (cube t) * ∑ k, rw k * ∑ j, A₀ k j * z (join j t)

/-- The column weights `M_α(j) = Σ_k rw(k) (A₀(k, j) + α B₀(k, j))`. -/
def linM (A₀ B₀ : Fin (2 ^ p) → Fin (2 ^ p) → R) (rw : Fin (2 ^ p) → R) (α : R)
    (j : Fin (2 ^ p)) : R :=
  ∑ k, rw k * (A₀ k j + α * B₀ k j)

/-- `z` folded over the blocks at `r_blk`: `z̄(j) = Σ_t eq(r_blk, t) z(j, t)`. -/
def zfold (rb : Fin q → R) (z : Fin (2 ^ (p + q)) → R) (j : Fin (2 ^ p)) : R :=
  ∑ t : Fin (2 ^ q), eq rb (cube t) * z (join j t)

/-- **The lincheck's true sum** is `â* + α b̂*`. -/
theorem lin_trueSum (A₀ B₀ : Fin (2 ^ p) → Fin (2 ^ p) → R) (rw : Fin (2 ^ p) → R) (α : R)
    (rb : Fin q → R) (z : Fin (2 ^ (p + q)) → R) :
    trueSum innerExpr #[Array.ofFn (linM A₀ B₀ rw α), Array.ofFn (zfold rb z)] p =
      linA A₀ rw rb z + α * linA B₀ rw rb z := by
  rw [prod_trueSum]
  simp only [linM, zfold, linA, Finset.sum_mul, Finset.mul_sum, mul_add, add_mul,
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Row L1.** A wrong pair `(â, b̂)` survives the batching for at most one `α`. -/
theorem lin_alpha_le [IsDomain R] [Fintype R] [DecidableEq R] (A₀ B₀ : Fin (2 ^ p) → Fin (2 ^ p) → R)
    (rw : Fin (2 ^ p) → R) (rb : Fin q → R) (z : Fin (2 ^ (p + q)) → R) {va vb : R}
    (h : (va, vb) ≠ (linA A₀ rw rb z, linA B₀ rw rb z)) :
    (univ.filter fun α ↦ va + α * vb = linA A₀ rw rb z + α * linA B₀ rw rb z).card ≤ 1 :=
  batch2_bad_le h

/-- **End of L2.** After the `p` rounds at `rs`: `M̃_α(r_k) · ẑ(r_k, r_blk)`, one multilinear claim
on `z`. -/
theorem lin_final (A₀ B₀ : Fin (2 ^ p) → Fin (2 ^ p) → R) (rw : Fin (2 ^ p) → R) (α : R)
    (rb : Fin q → R) (z : Fin (2 ^ (p + q)) → R) (rs : List R) (hr : rs.length = p) :
    trueSum innerExpr (bindAll #[Array.ofFn (linM A₀ B₀ rw α), Array.ofFn (zfold rb z)] rs) 0 =
      mle (linM A₀ B₀ rw α) (ptOf p rs) * mle z (Fin.append (ptOf p rs) rb) := by
  rw [trueSum_bindAll' _ _ _ hr (prod_sizes _ _)]
  simp only [innerExpr, Expr.eval, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, tbl_ofFn]
  congr 1
  rw [mle_split]
  rfl

end Lin

/-! ## The lincheck on per-kind folded columns (rev. 3.4, S-C-M1) -/

section LinKinds

variable {R : Type*} [CommRing R] {p q K : ℕ}

/-- `Σ_{κ ≤ K} t_{2κ} · t_{2κ+1}`: one product per kind, degree 2. -/
def kindExpr : ℕ → Expr
  | 0 => .mul (.var 0) (.var 1)
  | K + 1 => .add (kindExpr K) (.mul (.var (2 * K + 2)) (.var (2 * K + 3)))

theorem kindExpr_deg (K : ℕ) : (kindExpr K).deg = 2 := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [kindExpr, Expr.deg, ih]; rfl

theorem eval_kindExpr (K : ℕ) (v : ℕ → R) :
    (kindExpr K).eval v = ∑ κ ∈ range (K + 1), v (2 * κ) * v (2 * κ + 1) := by
  induction K with
  | zero => simp [kindExpr, Expr.eval]
  | succ K ih => rw [kindExpr, Expr.eval, ih, Finset.sum_range_succ _ (K + 1)]; rfl

/-- The tables `M_κ`, `z̄_κ` interleaved: table `2κ` is `M_κ`, table `2κ + 1` is `z̄_κ`. -/
def kindTables (Ms zs : Fin (K + 1) → Fin (2 ^ p) → R) : Array (Array R) :=
  Array.ofFn (n := 2 * (K + 1)) fun idx ↦ Array.ofFn fun j ↦
    if idx.val % 2 = 0 then Ms ⟨idx.val / 2, by omega⟩ j else zs ⟨idx.val / 2, by omega⟩ j

omit [CommRing R] in
theorem kindTables_size (Ms zs : Fin (K + 1) → Fin (2 ^ p) → R) :
    ∀ t ∈ kindTables Ms zs, t.size = 2 ^ p := by
  intro t ht
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp ht
  simp

theorem tbl_kindTables (Ms zs : Fin (K + 1) → Fin (2 ^ p) → R) (κ : Fin (K + 1)) :
    tbl p ((kindTables Ms zs).getD (2 * κ.val) #[]) = Ms κ ∧
      tbl p ((kindTables Ms zs).getD (2 * κ.val + 1) #[]) = zs κ := by
  have h0 : 2 * κ.val < 2 * (K + 1) := by omega
  have h1 : 2 * κ.val + 1 < 2 * (K + 1) := by omega
  have e0 : 2 * κ.val / 2 = κ.val := by omega
  have e1 : (2 * κ.val + 1) / 2 = κ.val := by omega
  have m1 : (2 * κ.val + 1) % 2 = 1 := by omega
  constructor <;> funext j <;>
    simp [tbl, kindTables, Array.getD_eq_getD_getElem?, h0, h1, Nat.mul_mod_right, e0, e1, m1]

private theorem kind_sum (Ms zs : Fin (K + 1) → Fin (2 ^ p) → R) (G : Array R → Array R → R) :
    ∑ κ ∈ range (K + 1), G ((kindTables Ms zs).getD (2 * κ) #[]) ((kindTables Ms zs).getD (2 * κ + 1) #[]) =
      ∑ κ : Fin (K + 1), G ((kindTables Ms zs).getD (2 * κ.val) #[])
        ((kindTables Ms zs).getD (2 * κ.val + 1) #[]) :=
  (Fin.sum_univ_eq_sum_range (fun κ ↦ G ((kindTables Ms zs).getD (2 * κ) #[])
    ((kindTables Ms zs).getD (2 * κ + 1) #[])) _).symm

/-- The per-kind column fold `z̄_κ(j) = Σ_t eq(r′_blk, t) Ind_κ(t) z(j, t)`. -/
def zfoldK (Ind : Fin (K + 1) → Fin (2 ^ q) → R) (rb : Fin q → R) (z : Fin (2 ^ (p + q)) → R)
    (κ : Fin (K + 1)) (j : Fin (2 ^ p)) : R :=
  ∑ t : Fin (2 ^ q), eq rb (cube t) * Ind κ t * z (join j t)

/-- `â*` for `A = Σ_κ Ind_κ ⊗ A₀^κ`: the indicator inside the block sum. -/
def linAK (Ak : Fin (K + 1) → Fin (2 ^ p) → Fin (2 ^ p) → R) (Ind : Fin (K + 1) → Fin (2 ^ q) → R)
    (rw : Fin (2 ^ p) → R) (rb : Fin q → R) (z : Fin (2 ^ (p + q)) → R) : R :=
  ∑ t : Fin (2 ^ q), eq rb (cube t) * ∑ κ, Ind κ t * ∑ k, rw k * ∑ j, Ak κ k j * z (join j t)

/-- **The per-kind lincheck's true sum** is `â* + α b̂*` (S-C-M1's identity). -/
theorem lin_trueSum_kinds (Ak Bk : Fin (K + 1) → Fin (2 ^ p) → Fin (2 ^ p) → R)
    (Ind : Fin (K + 1) → Fin (2 ^ q) → R) (rw : Fin (2 ^ p) → R) (α : R) (rb : Fin q → R)
    (z : Fin (2 ^ (p + q)) → R) :
    trueSum (kindExpr K) (kindTables (fun κ ↦ linM (Ak κ) (Bk κ) rw α) (zfoldK Ind rb z)) p =
      linAK Ak Ind rw rb z + α * linAK Bk Ind rw rb z := by
  simp only [trueSum, eval_kindExpr]
  refine (Finset.sum_congr rfl fun x _ ↦ kind_sum _ _ (fun a b ↦ tbl p a x * tbl p b x)).trans ?_
  simp only [(tbl_kindTables _ _ _).1, (tbl_kindTables _ _ _).2]
  have aux : ∀ Ck : Fin (K + 1) → Fin (2 ^ p) → Fin (2 ^ p) → R,
      ∑ j : Fin (2 ^ p), ∑ κ, (∑ k, rw k * Ck κ k j) * zfoldK Ind rb z κ j = linAK Ck Ind rw rb z := by
    intro Ck
    simp only [zfoldK, linAK, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => enter [2, κ]; rw [Finset.sum_comm]
    conv_lhs => enter [2, κ, 2, k]; rw [Finset.sum_comm]
    conv_lhs => enter [2, κ]; rw [Finset.sum_comm]
    conv_lhs => enter [2, κ]; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have hM : ∀ κ j, linM (Ak κ) (Bk κ) rw α j =
      (∑ k, rw k * Ak κ k j) + α * ∑ k, rw k * Bk κ k j := fun κ j ↦ by
    simp only [linM, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun _ _ ↦ by ring)
  simp only [hM, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, aux]

/-- **End of L2** (per kind): the true value is `Σ_κ M̃_κ(r_k) · v_κ`, `v_κ = z̄̃_κ(r_k)`. -/
theorem lin_final_kinds (Ak Bk : Fin (K + 1) → Fin (2 ^ p) → Fin (2 ^ p) → R)
    (Ind : Fin (K + 1) → Fin (2 ^ q) → R) (rw : Fin (2 ^ p) → R) (α : R) (rb : Fin q → R)
    (z : Fin (2 ^ (p + q)) → R) (rs : List R) (hr : rs.length = p) :
    trueSum (kindExpr K)
        (bindAll (kindTables (fun κ ↦ linM (Ak κ) (Bk κ) rw α) (zfoldK Ind rb z)) rs) 0 =
      ∑ κ, mle (linM (Ak κ) (Bk κ) rw α) (ptOf p rs) * mle (zfoldK Ind rb z κ) (ptOf p rs) := by
  rw [trueSum_bindAll' _ _ _ hr (kindTables_size _ _), eval_kindExpr,
    kind_sum _ _ (fun a b ↦ mle (tbl p a) (ptOf p rs) * mle (tbl p b) (ptOf p rs))]
  simp only [(tbl_kindTables _ _ _).1, (tbl_kindTables _ _ _).2]

/-- The claim `v_κ` is a weighted claim on `z`: the weight `eq(r_k, j) eq(r′_blk, t) Ind_κ(t)`. -/
theorem zfoldK_mle (Ind : Fin (K + 1) → Fin (2 ^ q) → R) (rb : Fin q → R)
    (z : Fin (2 ^ (p + q)) → R) (κ : Fin (K + 1)) (r : Fin p → R) :
    mle (zfoldK Ind rb z κ) r =
      ∑ j : Fin (2 ^ p), ∑ t : Fin (2 ^ q), eq r (cube j) * eq rb (cube t) * Ind κ t * z (join j t) := by
  simp only [mle, zfoldK, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Row L3** (`β`, 6 of `|F|` for 7 kinds): the `v_κ` batched by `β` are one weighted claim with
the public weight `W_β(j, t) = eq(r_k, j) eq(r′_blk, t) Σ_κ β^κ Ind_κ(t)`. -/
theorem lin_beta_claim (Ind : Fin (K + 1) → Fin (2 ^ q) → R) (rb : Fin q → R)
    (z : Fin (2 ^ (p + q)) → R) (r : Fin p → R) (β : R) :
    ∑ κ : Fin (K + 1), β ^ κ.val * mle (zfoldK Ind rb z κ) r =
      ∑ j : Fin (2 ^ p), ∑ t : Fin (2 ^ q),
        eq r (cube j) * eq rb (cube t) * (∑ κ : Fin (K + 1), β ^ κ.val * Ind κ t) * z (join j t) := by
  simp only [zfoldK_mle, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun κ _ ↦ by ring

/-- **The walk adjustment.** When the kinds' matrices differ only by their free rows
(`A₀^κ(k, j) = free_κ(k) A₀(k, j)`), `Σ_κ v_κ M̃_κ(r_k)` is one walk of `(A₀, B₀)` with the row
weights `rw′(k) = rw(k) · Σ_κ v_κ free_κ(k)`. -/
theorem lin_walk_adjust (A₀ B₀ : Fin (2 ^ p) → Fin (2 ^ p) → R) (free : Fin (K + 1) → Fin (2 ^ p) → R)
    (rw : Fin (2 ^ p) → R) (α : R) (v : Fin (K + 1) → R) (r : Fin p → R) :
    ∑ κ, v κ * mle (linM (fun k j ↦ free κ k * A₀ k j) (fun k j ↦ free κ k * B₀ k j) rw α) r =
      mle (linM A₀ B₀ (fun k ↦ rw k * ∑ κ, v κ * free κ k) α) r := by
  simp only [mle, linM, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun κ _ ↦ by ring

/-- **Row L3, count.** A wrong family of 7 kind claims survives `β` for at most 6 values. -/
theorem lin_beta_le [IsDomain R] [Fintype R] [DecidableEq R] {v t : Fin 7 → R} (h : v ≠ t) :
    (univ.filter fun β ↦ ∑ κ, β ^ κ.val * v κ = ∑ κ, β ^ κ.val * t κ).card ≤ 6 :=
  batch_pow_bad_le h

end LinKinds

/-! ## The quirky claim's ring-switching weight (row RS1) -/

/-- **The quirky claim splits along the pack.** With the 128 bits of a packed element indexed by
the 6 skip bits and one more bit, `ẑ(λ, r′)` is the sum over them of the skip Lagrange weight at
`λ` times `eq(r′₀, b)` times the bit-plane claim at the remaining coordinates: the low weight `c`
of `rs_column` for Z's claim. -/
theorem quirky_claim_split {ℓ : ℕ} (z : Fin 64 → Fin (2 ^ (1 + ℓ)) → F) (l : F) (r0 : Fin 1 → F)
    (rhi : Fin ℓ → F) :
    ∑ u, eq (Fin.append r0 rhi) (cube u) * (skipExt fun i ↦ z i u).eval l =
      ∑ i : Fin 64, ∑ b : Fin (2 ^ 1),
        lagrangeWeight (fun b : Fin 64 ↦ skipNode (Fin.castLE (by norm_num) b)) l i *
          eq r0 (cube b) * mle (fun v ↦ z i (join b v)) rhi := by
  simp only [skipExt_eval, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := mle_split (z i) r0 rhi
  rw [mle] at this
  rw [show ∑ u, eq (Fin.append r0 rhi) (cube u) * (lagrangeWeight _ l i * z i u) =
      lagrangeWeight (fun b : Fin 64 ↦ skipNode (Fin.castLE (by norm_num) b)) l i *
        ∑ u, eq (Fin.append r0 rhi) (cube u) * z i u by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, this, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

end FR
