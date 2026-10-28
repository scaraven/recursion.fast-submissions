-- New for `flock-recursive` (BLUEPRINT A.9 `finSh`, A.10 S1/S2, §5.2 row S; stage S-G7).
import FRSoundnessFrPend
import FRSoundnessFrExt
import FRVerifierImplNode
import FRSoundnessAccEq

/-!
# S: the S2 weight, its true sum and its extension (the `eqAtR` bridge)

S2 is one product sumcheck `Σ_{y,q} W(y, q) z(y, q)` over the `nb = m − 14` block coordinates
(bound first) and the 10 position coordinates `q < 2^10` of each block (`z(y, q)` the bit at
position `q` of block `y`). The weight `W` is A.9 `finSh`'s, as a table:

* a leaf (**`wLeaf`**): `eq(τ, y)·slot_256(q) + (shift(τ, y) + κ_s eq(0, y))·slot_520(q)`, the
  `h_out` slot (map 0) out, the chain block's `d` slot (map 1) in;
* a node (**`wNode`**, the chain-masked form of revision 3.14): `[lk y] eq(τ, y)·slot_256(q) +
  ([lk (y−1)] eq(τ, y − 1) + κ_s ([y = 0] + [y = N]))·slot_0(q) + Σ_f κ_s^(f+2) W_f(y, q)`, `lk`
  the in-chain successor (`chainLk`), `W_f` the 8 link families' extended indicator (`linkInd`).

`slot_b(q) = Σ_{σ<256} eq(θ, σ)[q = b + σ]` (`slotT`). Everything is over `ℕ`-indexed sums with
`eqAtR` (the verifier's form), so no `Fin`-indexed table meets a concrete size.

* **`sh_sum_leaf`**, **`sh_sum_node`**: the true sum is the verifier's target plus the residual
  `Σ_j κ_s^j R̃_j(τ, θ)` (`resLeaf`, `resNode`: `R_0` the links, `R_1` the starts, `R_(f+2)` the
  families).
* **`res_ne_leaf`**, **`res_ne_node`**: when the S truth fails some residual table is nonzero.
* **`mle_ofFn_split`**: a table's extension at `(r_lo ‖ r_hi)` as a split `eqAtR` sum; with it
  **`final_leaf`**, **`final_node`**: `W̃(r_blk, r_pos)` is A.9's `w_out + w_in` on the operations'
  specifications (`eqPoint`, `shiftEqS`, `shiftMaskS`, `slotWS`, `linkWAllS`).
-/

namespace FR.Snd
open RecursionFast Finset FR.Impl FR.NodeT FR.NodeI

set_option linter.constructorNameAsVariable false

/-! ## Sums over `2^(a+b)` indices and `eqAtR` -/

theorem sum_range_mul_split (n : ℕ) (g : ℕ → F) : ∀ m : ℕ,
    ∑ i ∈ range (n * m), g i = ∑ q ∈ range m, ∑ y ∈ range n, g (y + n * q)
  | 0 => by simp
  | m + 1 => by
    rw [Nat.mul_succ, sum_range_add, sum_range_mul_split n g m, sum_range_succ]
    exact congrArg _ (sum_congr rfl fun y _ => by rw [add_comm])

theorem sum_range_pow_add (a b : ℕ) (g : ℕ → F) :
    ∑ i ∈ range (2 ^ (a + b)), g i = ∑ q ∈ range (2 ^ b), ∑ y ∈ range (2 ^ a), g (y + 2 ^ a * q) :=
  by rw [pow_add, sum_range_mul_split]

theorem eq_cube_eqAtR {n : ℕ} (r : Fin n → F) (u : Fin (2 ^ n)) : eq r (cube u) = eqAtR r u.val :=
  eq_cube r u

theorem sum_eqAtR_one {n : ℕ} (r : Fin n → F) : ∑ u ∈ range (2 ^ n), eqAtR r u = 1 := by
  rw [← eq_sum_one r, ← Fin.sum_univ_eq_sum_range (fun u => eqAtR r u)]
  exact sum_congr rfl fun u _ => (eq_cube_eqAtR r u).symm

theorem sum_eqAtR_mul {n : ℕ} (a b : Fin n → F) :
    ∑ u ∈ range (2 ^ n), eqAtR a u * eqAtR b u = eq a b := by
  rw [← eq_mle a b, ← Fin.sum_univ_eq_sum_range (fun u => eqAtR a u * eqAtR b u)]
  refine sum_congr rfl fun u _ => ?_
  rw [eq_cube_eqAtR, eq_swap, eq_cube_eqAtR]

theorem ptOf_drop {a : ℕ} (rs : List F) (l : ℕ) : (rs.drop a).getD l 0 = rs.getD (a + l) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **A table's extension at a split point**: the low `a` coordinates (`rs`'s first `a`) weigh
the index's low part `y`, the next `b` its high part `q`. -/
theorem mle_ofFn_split (a b : ℕ) (g : ℕ → F) (rs : List F) :
    mle (tbl (a + b) (Array.ofFn (n := 2 ^ (a + b)) fun i => g i.val)) (ptOf (a + b) rs) =
      ∑ q ∈ range (2 ^ b), ∑ y ∈ range (2 ^ a),
        eqAtR (ptOf a rs) y * eqAtR (ptOf b (rs.drop a)) q * g (y + 2 ^ a * q) := by
  rw [tbl_ofFn, mle]
  rw [show (∑ u : Fin (2 ^ (a + b)), eq (ptOf (a + b) rs) (cube u) * g u.val) =
      ∑ u : Fin (2 ^ (a + b)), (fun i => eqAtR (ptOf (a + b) rs) i * g i) u.val from
    sum_congr rfl fun u _ => by rw [eq_cube_eqAtR]]
  refine (Fin.sum_univ_eq_sum_range (fun i => eqAtR (ptOf (a + b) rs) i * g i) _).trans ?_
  rw [sum_range_pow_add]
  refine sum_congr rfl fun q hq => sum_congr rfl fun y hy => ?_
  have hy' := mem_range.1 hy
  have hq' := mem_range.1 hq
  have h1 : (y + 2 ^ a * q) % 2 ^ a = y := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy']
  have h2 : (y + 2 ^ a * q) / 2 ^ a % 2 ^ b = q := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos a), Nat.div_eq_of_lt hy', zero_add,
      Nat.mod_eq_of_lt hq']
  have hl : loP (ptOf (a + b) rs) = ptOf a rs := rfl
  have hh : hiP (ptOf (a + b) rs) = ptOf b (rs.drop a) := by
    funext l; simp only [hiP, ptOf, ptOf_drop]; rfl
  rw [eqAtR_split, h1, h2, hl, hh]

theorem sum_range_ite_lt {n L : ℕ} (h : L ≤ n) (g : ℕ → F) :
    ∑ x ∈ range n, (if x < L then g x else 0) = ∑ x ∈ range L, g x := by
  rw [← sum_range_add_sum_Ico _ h, sum_eq_zero (s := Ico L n) fun x hx => by
    simp [(mem_Ico.1 hx).1], add_zero]
  exact sum_congr rfl fun x hx => by simp [mem_range.1 hx]

theorem sum_perm3 (A B C : Finset ℕ) (g : ℕ → ℕ → ℕ → F) :
    ∑ q ∈ A, ∑ u ∈ B, ∑ y ∈ C, g q u y = ∑ y ∈ C, ∑ u ∈ B, ∑ q ∈ A, g q u y := by
  rw [sum_congr rfl fun q _ => sum_comm, sum_comm]
  exact sum_congr rfl fun y _ => sum_comm

theorem sum_perm4 (A B C D : Finset ℕ) (g : ℕ → ℕ → ℕ → ℕ → F) :
    ∑ q ∈ A, ∑ u ∈ B, ∑ y ∈ C, ∑ p ∈ D, g q u y p =
      ∑ p ∈ D, ∑ y ∈ C, ∑ u ∈ B, ∑ q ∈ A, g q u y p := by
  calc _ = ∑ q ∈ A, ∑ p ∈ D, ∑ u ∈ B, ∑ y ∈ C, g q u y p :=
        sum_congr rfl fun q _ => by rw [sum_congr rfl fun u _ => sum_comm, sum_comm]
    _ = ∑ p ∈ D, ∑ q ∈ A, ∑ u ∈ B, ∑ y ∈ C, g q u y p := sum_comm
    _ = _ := sum_congr rfl fun p _ => sum_perm3 A B C _

/-! ## The S2 weights -/

/-- **A slot's weight** at position `q`: `Σ_{σ<256} eq(θ, σ) [q = b + σ]` (A.8 `slotW`'s table). -/
def slotT (θ : Fin 10 → F) (b q : ℕ) : F := ∑ σ ∈ range 256, eqAtR θ σ * if q = b + σ then 1 else 0

theorem sum_slotT (θ : Fin 10 → F) {b : ℕ} (hb : b + 256 ≤ 2 ^ 10) (g : ℕ → F) :
    ∑ q ∈ range (2 ^ 10), slotT θ b q * g q = ∑ σ ∈ range 256, eqAtR θ σ * g (b + σ) := by
  simp only [slotT, sum_mul, mul_assoc, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun σ hσ => ?_
  rw [← mul_sum, sum_ite_eq', if_pos (mem_range.2 (by have := mem_range.1 hσ; omega))]

/-- The digest bits read through `eq(θ, ·)`: `Σ_{σ<256} eq(θ, σ) d(σ)`. -/
def thS (θ : Fin 10 → F) (d : ℕ → F) : F := ∑ σ ∈ range 256, eqAtR θ σ * d σ

/-- **A leaf's In-block weight** `shift(τ, y) + κ_s eq(0, y)`: block `y`'s input is block
`y − 1`'s output, block `0`'s is the start. -/
def shL {nb : ℕ} (τ : Fin nb → F) (κ : F) (y : ℕ) : F :=
  (if 1 ≤ y then eqAtR τ (y - 1) else 0) + κ * if y = 0 then 1 else 0

/-- **A leaf's S2 weight** (A.9 `finSh`, a leaf): `h_out` (slot `256 + σ`) out at `eq(τ, y)`,
`d` (slot `520 + σ`) in at `shL`. -/
def wLeaf {nb : ℕ} (τ : Fin nb → F) (θ : Fin 10 → F) (κ : F) (y q : ℕ) : F :=
  eqAtR τ y * slotT θ 256 q + shL τ κ y * slotT θ 520 q

/-- **The residual tables** `R_j(u, q)` (`j < J`) batched by `κ_s^j` at `(τ, θ)`. -/
def resSum (nb J : ℕ) (R : ℕ → ℕ → ℕ → F) {nb' : ℕ} (τ : Fin nb' → F) (θ : Fin 10 → F) (κ : F) :
    F :=
  ∑ j ∈ range J, κ ^ j * ∑ q ∈ range (2 ^ 10), ∑ u ∈ range (2 ^ nb),
    eqAtR τ u * eqAtR θ q * R j u q

/-- **A leaf's residuals** (`J = 2`): `R_0` the links `h_out(u) + d(u + 1)` (the last block's
`h_out + h`), `R_1` the start `d(0) + s` (characteristic two), on the slot bits `q < 256`. -/
def resLeaf (nb : ℕ) (z : ℕ → ℕ → F) (sb hb : ℕ → F) (j u q : ℕ) : F :=
  if q < 256 then
    (if j = 0 then z u (256 + q) + (if u + 1 < 2 ^ nb then z (u + 1) (520 + q) else 0) +
        (if u = 2 ^ nb - 1 then hb q else 0)
      else if j = 1 then z 0 (520 + q) + sb q else 0)
  else 0

theorem resLeaf_zero (nb : ℕ) (z : ℕ → ℕ → F) (sb hb : ℕ → F) (u q : ℕ) :
    resLeaf nb z sb hb 0 u q = if q < 256 then z u (256 + q) +
      (if u + 1 < 2 ^ nb then z (u + 1) (520 + q) else 0) +
        (if u = 2 ^ nb - 1 then hb q else 0) else 0 := by
  simp only [resLeaf, ↓reduceIte]

theorem resLeaf_one (nb : ℕ) (z : ℕ → ℕ → F) (sb hb : ℕ → F) (u q : ℕ) :
    resLeaf nb z sb hb 1 u q = if q < 256 then z 0 (520 + q) + sb q else 0 := by
  simp only [resLeaf, one_ne_zero, ↓reduceIte]

/-- **The leaf's true S2 sum** is the target `eq(τ, last) h̃(θ) + κ_s s̃(θ)` plus the residual. -/
theorem sh_sum_leaf {nb : ℕ} (τ : Fin nb → F) (θ : Fin 10 → F) (κ : F) (z : ℕ → ℕ → F)
    (sb hb : ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), wLeaf τ θ κ y q * z y q =
      eqAtR τ (2 ^ nb - 1) * thS θ hb + κ * thS θ sb + resSum nb 2 (resLeaf nb z sb hb) τ θ κ := by
  set O : ℕ → F := fun y => thS θ fun σ => z y (256 + σ)
  set I : ℕ → F := fun y => thS θ fun σ => z y (520 + σ)
  have hL : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), wLeaf τ θ κ y q * z y q =
      ∑ y ∈ range (2 ^ nb), (eqAtR τ y * O y + shL τ κ y * I y) := by
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    simp only [wLeaf, add_mul, sum_add_distrib, mul_assoc]
    rw [← mul_sum, ← mul_sum, sum_slotT θ (by norm_num), sum_slotT θ (by norm_num)]
    rfl
  have hN : 2 ^ nb = (2 ^ nb - 1) + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  have hS : ∑ y ∈ range (2 ^ nb), shL τ κ y * I y =
      ∑ u ∈ range (2 ^ nb), (if u + 1 < 2 ^ nb then eqAtR τ u * I (u + 1) else 0) + κ * I 0 := by
    have e1 : ∑ y ∈ range (2 ^ nb), shL τ κ y * I y =
        ∑ y ∈ range (2 ^ nb), (if 1 ≤ y then eqAtR τ (y - 1) * I y else 0) + κ * I 0 := by
      simp only [shL, add_mul, sum_add_distrib, ite_mul, zero_mul, mul_assoc, mul_ite, mul_one,
        mul_zero, sum_ite_eq', mem_range, Nat.two_pow_pos, if_true]
    have e2 : ∑ y ∈ range (2 ^ nb), (if 1 ≤ y then eqAtR τ (y - 1) * I y else 0) =
        ∑ u ∈ range (2 ^ nb), (if u + 1 < 2 ^ nb then eqAtR τ u * I (u + 1) else 0) := by
      rw [hN, sum_range_succ', sum_range_succ, if_neg (by omega), add_zero, if_neg (by omega),
        add_zero]
      refine sum_congr rfl fun u hu => ?_
      have := mem_range.1 hu
      rw [if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel]
    rw [e1, e2]
  have hR0 : ∀ u, ∑ q ∈ range (2 ^ 10), eqAtR θ q * resLeaf nb z sb hb 0 u q =
      O u + (if u + 1 < 2 ^ nb then I (u + 1) else 0) + (if u = 2 ^ nb - 1 then thS θ hb else 0) := by
    intro u
    simp only [resLeaf_zero, mul_ite, mul_zero]
    rw [sum_range_ite_lt (by norm_num)]
    by_cases h1 : u + 1 < 2 ^ nb
    · have h2 : ¬ u = 2 ^ nb - 1 := by omega
      simp only [h1, h2, if_true, if_false, O, I, thS, mul_add, sum_add_distrib, add_zero,
        mul_zero, sum_const_zero]
    · simp only [h1, if_false, mul_zero, sum_const_zero, add_zero]
      by_cases h2 : u = 2 ^ nb - 1 <;>
        simp only [h2, if_true, if_false, O, I, thS, mul_add, sum_add_distrib, add_zero,
          mul_zero, sum_const_zero]
  have hR1 : ∀ u, ∑ q ∈ range (2 ^ 10), eqAtR θ q * resLeaf nb z sb hb 1 u q = I 0 + thS θ sb := by
    intro u
    simp only [resLeaf_one, mul_ite, mul_zero]
    rw [sum_range_ite_lt (by norm_num)]
    simp only [I, thS, mul_add, sum_add_distrib]
  have hres : resSum nb 2 (resLeaf nb z sb hb) τ θ κ =
      ∑ u ∈ range (2 ^ nb), eqAtR τ u * (O u + (if u + 1 < 2 ^ nb then I (u + 1) else 0) +
        (if u = 2 ^ nb - 1 then thS θ hb else 0)) + κ * (I 0 + thS θ sb) := by
    simp only [resSum, sum_range_succ, sum_range_zero, zero_add, pow_zero, one_mul, pow_one]
    rw [sum_comm, sum_comm (s := range (2 ^ 10))]
    simp only [mul_assoc, ← mul_sum, hR0, hR1, ← sum_mul, sum_eqAtR_one, one_mul]
  rw [hL, hres, sum_add_distrib, hS]
  simp only [mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq', mem_range,
    Nat.sub_lt (Nat.two_pow_pos nb) one_pos, if_true]
  linear_combination (-(eqAtR τ (2 ^ nb - 1) * thS θ hb + κ * thS θ sb)) * CharTwo.two_eq_zero (R := F)

/-! ## The node's weight (chain-masked, with the link families) -/

/-- The node's Out-block weight `[lk y] eq(τ, y)`. -/
def lkW (τ : Fin 16 → F) (y : ℕ) : F := if chainLk y then eqAtR τ y else 0

/-- **The node's In-block weight**: `[lk (y−1)] eq(τ, y − 1) + κ_s ([y = 0] + [y = N])`. -/
def shN (τ : Fin 16 → F) (κ : F) (y : ℕ) : F :=
  (if 1 ≤ y ∧ chainLk (y - 1) then eqAtR τ (y - 1) else 0) +
    κ * ((if y = 0 then 1 else 0) + if y = Layout.chainN then 1 else 0)

/-- Family `f`'s weight at cell `(y, q)`: the extended source-minus-mirror indicator. -/
def famW (f : ℕ) (τ : Fin 16 → F) (θ : Fin 10 → F) (y q : ℕ) : F :=
  ∑ u ∈ range (2 ^ 16), ∑ s ∈ range (2 ^ 10), eqAtR τ u * eqAtR θ s * linkInd f u s y q

/-- **A node's S2 weight** (A.9 `finSh`, a node): `h_out` (slot `256 + σ`) out, `h_in` (slot `σ`)
in, and the families batched by `κ_s^(f+2)`. -/
def wNode (τ : Fin 16 → F) (θ : Fin 10 → F) (κ : F) (y q : ℕ) : F :=
  lkW τ y * slotT θ 256 q + shN τ κ y * slotT θ 0 q +
    ∑ f ∈ range nLinkFam, κ ^ (f + 2) * famW f τ θ y q

/-- **A node's residuals** (`J = 10`): `R_0` the masked links `h_out(u) + h_in(u + 1)`, `R_1` the
starts `h_in(0) + h_in(N)`, `R_(f+2)` family `f`'s source-minus-mirror differences. -/
def resNode (z : ℕ → ℕ → F) (j u q : ℕ) : F :=
  if j = 0 then (if q < 256 ∧ chainLk u then z u (256 + q) + z (u + 1) q else 0)
  else if j = 1 then (if q < 256 then z 0 q + z Layout.chainN q else 0)
  else ∑ y ∈ range (2 ^ 16), ∑ p ∈ range (2 ^ 10), linkInd (j - 2) u q y p * z y p

theorem resNode_zero (z : ℕ → ℕ → F) (u q : ℕ) :
    resNode z 0 u q = if q < 256 ∧ chainLk u then z u (256 + q) + z (u + 1) q else 0 := by
  simp only [resNode, ↓reduceIte]

theorem resNode_one (z : ℕ → ℕ → F) (u q : ℕ) :
    resNode z 1 u q = if q < 256 then z 0 q + z Layout.chainN q else 0 := by
  simp only [resNode, one_ne_zero, ↓reduceIte]

theorem resNode_fam (z : ℕ → ℕ → F) (f u q : ℕ) :
    resNode z (f + 2) u q =
      ∑ y ∈ range (2 ^ 16), ∑ p ∈ range (2 ^ 10), linkInd f u q y p * z y p := by
  simp only [resNode, show f + 2 ≠ 0 by omega, show f + 2 ≠ 1 by omega, ↓reduceIte,
    Nat.add_sub_cancel]

theorem chainLk_lt {y : ℕ} (h : chainLk y) : y + 1 < 2 ^ 16 := by
  unfold chainLk Layout.chainN at h; omega

/-- **The node's true S2 sum is its residual** (the target is `0`: no end term, and the starts'
`κ_s (h̃0 + h̃0)` vanishes). -/
theorem sh_sum_node (τ : Fin 16 → F) (θ : Fin 10 → F) (κ : F) (z : ℕ → ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16), wNode τ θ κ y q * z y q =
      resSum 16 10 (resNode z) τ θ κ := by
  set O : ℕ → F := fun y => thS θ fun σ => z y (256 + σ)
  set I : ℕ → F := fun y => thS θ fun σ => z y σ
  set G : ℕ → F := fun f => ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16), famW f τ θ y q * z y q
  have hL : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16), wNode τ θ κ y q * z y q =
      ∑ y ∈ range (2 ^ 16), (lkW τ y * O y + shN τ κ y * I y) +
        ∑ f ∈ range nLinkFam, κ ^ (f + 2) * G f := by
    have e1 : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16),
        (lkW τ y * slotT θ 256 q + shN τ κ y * slotT θ 0 q) * z y q =
        ∑ y ∈ range (2 ^ 16), (lkW τ y * O y + shN τ κ y * I y) := by
      rw [sum_comm]
      refine sum_congr rfl fun y _ => ?_
      simp only [add_mul, sum_add_distrib, mul_assoc]
      rw [← mul_sum, ← mul_sum, sum_slotT θ (by norm_num), sum_slotT θ (by norm_num)]
      simp only [O, I, thS, zero_add]
    have e2 : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16),
        (∑ f ∈ range nLinkFam, κ ^ (f + 2) * famW f τ θ y q) * z y q =
        ∑ f ∈ range nLinkFam, κ ^ (f + 2) * G f := by
      simp only [G, sum_mul, mul_sum, mul_assoc]
      rw [sum_congr rfl fun q _ => sum_comm, sum_comm]
    simp only [wNode, add_mul (lkW τ _ * _ + _), sum_add_distrib]
    rw [e1, e2, sum_add_distrib]
  have hS : ∑ y ∈ range (2 ^ 16), shN τ κ y * I y =
      ∑ u ∈ range (2 ^ 16), lkW τ u * I (u + 1) + κ * (I 0 + I Layout.chainN) := by
    have hN : Layout.chainN < 2 ^ 16 := by simp [Layout.chainN]
    have e1 : ∑ y ∈ range (2 ^ 16), shN τ κ y * I y =
        ∑ y ∈ range (2 ^ 16), (if 1 ≤ y ∧ chainLk (y - 1) then eqAtR τ (y - 1) * I y else 0) +
          κ * (I 0 + I Layout.chainN) := by
      simp only [shN, add_mul, sum_add_distrib, ite_mul, zero_mul, mul_ite, mul_one, mul_zero,
        one_mul, mul_assoc, ← mul_sum, sum_ite_eq', mem_range, hN, Nat.two_pow_pos, if_true]
    rw [e1, show 2 ^ 16 = (2 ^ 16 - 1) + 1 from rfl, sum_range_succ', sum_range_succ]
    simp only [show ¬ (1 ≤ 0 ∧ chainLk (0 - 1)) from fun h => absurd h.1 (by omega), if_false,
      add_zero, Nat.add_sub_cancel, show ∀ u, 1 ≤ u + 1 from fun u => by omega, true_and]
    have hl : ¬ chainLk (2 ^ 16 - 1) := by unfold chainLk Layout.chainN; omega
    simp only [lkW, hl, if_false, zero_mul, add_zero, ite_mul, zero_mul]
  have hR0 : ∀ u, ∑ q ∈ range (2 ^ 10), eqAtR θ q * resNode z 0 u q =
      if chainLk u then O u + I (u + 1) else 0 := by
    intro u
    simp only [resNode_zero, ite_and, mul_ite, mul_zero]
    rw [sum_range_ite_lt (by norm_num)]
    by_cases h : chainLk u <;> simp only [h, if_true, if_false, sum_const_zero, O, I, thS, mul_add,
      sum_add_distrib]
  have hR1 : ∀ u, ∑ q ∈ range (2 ^ 10), eqAtR θ q * resNode z 1 u q = I 0 + I Layout.chainN := by
    intro u
    simp only [resNode_one, mul_ite, mul_zero]
    rw [sum_range_ite_lt (by norm_num)]
    simp only [I, thS, mul_add, sum_add_distrib]
  have hRf : ∀ f, ∑ q ∈ range (2 ^ 10), ∑ u ∈ range (2 ^ 16), eqAtR τ u * eqAtR θ q *
      resNode z (f + 2) u q = G f := by
    intro f
    simp only [resNode_fam, G, famW, mul_sum, sum_mul, mul_assoc]
    exact sum_perm4 _ _ _ _ _
  have hres : resSum 16 10 (resNode z) τ θ κ =
      ∑ u ∈ range (2 ^ 16), lkW τ u * (O u + I (u + 1)) + κ * (I 0 + I Layout.chainN) +
        ∑ f ∈ range nLinkFam, κ ^ (f + 2) * G f := by
    unfold resSum
    rw [show range 10 = range (nLinkFam + 1 + 1) from rfl, sum_range_succ', sum_range_succ']
    simp only [hRf, pow_zero, one_mul, zero_add, pow_one]
    rw [sum_comm (s := range (2 ^ 10)), sum_comm (s := range (2 ^ 10))]
    simp only [mul_assoc, ← mul_sum, hR0, hR1, ← sum_mul, sum_eqAtR_one, one_mul]
    simp only [lkW, mul_ite, mul_zero, ite_mul, zero_mul]
    ring
  rw [hL, hres, sum_add_distrib, hS]
  simp only [lkW, mul_add, sum_add_distrib, ite_mul, zero_mul]
  ring

/-! ## The S truths fail ⇒ a residual table is nonzero -/

/-- **A leaf's S truth** (A.10 S1, `FRShift.ChainLinks` slot by slot): block `y + 1`'s `d` is block
`y`'s `h_out`, block `0`'s `d` is the start `s`, the last block's `h_out` is `h`. -/
def ShHoldsL (nb : ℕ) (z : ℕ → ℕ → F) (sb hb : ℕ → F) : Prop :=
  (∀ y, y + 1 < 2 ^ nb → ∀ σ < 256, z (y + 1) (520 + σ) = z y (256 + σ)) ∧
    (∀ σ < 256, z 0 (520 + σ) = sb σ) ∧ ∀ σ < 256, z (2 ^ nb - 1) (256 + σ) = hb σ

theorem shHoldsL_of_res {nb : ℕ} {z : ℕ → ℕ → F} {sb hb : ℕ → F}
    (h : ∀ j < 2, ∀ u < 2 ^ nb, ∀ q < 2 ^ 10, resLeaf nb z sb hb j u q = 0) :
    ShHoldsL nb z sb hb := by
  refine ⟨fun y hy σ hσ => ?_, fun σ hσ => ?_, fun σ hσ => ?_⟩
  · have e := h 0 (by norm_num) y (by omega) σ (by omega)
    rw [resLeaf_zero, if_pos hσ, if_pos hy, if_neg (by omega), add_zero] at e
    exact (CharTwo.add_eq_zero.mp e).symm
  · have e := h 1 (by norm_num) 0 (Nat.two_pow_pos _) σ (by omega)
    rw [resLeaf_one, if_pos hσ] at e
    exact CharTwo.add_eq_zero.mp e
  · have e := h 0 (by norm_num) (2 ^ nb - 1) (Nat.sub_lt (Nat.two_pow_pos _) one_pos) σ (by omega)
    rw [resLeaf_zero, if_pos hσ, if_neg (by omega), if_pos rfl, add_zero] at e
    exact CharTwo.add_eq_zero.mp e

/-- **Some leaf residual table is nonzero** when the leaf's S truth fails. -/
theorem res_ne_leaf {nb : ℕ} {z : ℕ → ℕ → F} {sb hb : ℕ → F} (h : ¬ ShHoldsL nb z sb hb) :
    ∃ j < 2, ∃ u < 2 ^ nb, ∃ q < 2 ^ 10, resLeaf nb z sb hb j u q ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (shHoldsL_of_res hc)

theorem fam_src_lt {f t : ℕ} (ht : t < (fam f).n) : (fam f).src t < Layout.wotsSlot := by
  have hw : Layout.wotsSlot = 498 := rfl
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp only [fam, id] at ht ⊢ <;> omega

theorem fam_src_inj {f t t' : ℕ} (h : (fam f).src t = (fam f).src t') : t = t' := by
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp only [fam, id] at h <;> omega

/-- Distinct sources of a family lie in distinct blocks. -/
theorem srcB_inj {f σ σ' t t' : ℕ} (hσ : σ < 2) (hσ' : σ' < 2) (ht : t < (fam f).n)
    (ht' : t' < (fam f).n) (h : srcB σ' f t' = srcB σ f t) : σ' = σ ∧ t' = t := by
  have h1 := fam_src_lt ht
  have h2 := fam_src_lt ht'
  have hw : Layout.wotsSlot = 498 := rfl
  unfold srcB wb at h
  have hs : σ' = σ := by
    rw [hw] at h h1 h2
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;>
      rcases (by omega : σ' = 0 ∨ σ' = 1) with rfl | rfl <;> omega
  subst hs
  exact ⟨rfl, fam_src_inj (f := f) (by omega)⟩

/-- **A family residual at a source's field bit** is the source-minus-mirror difference. -/
theorem resNode_src (z : ℕ → ℕ → F) {f σ t s : ℕ} (hσ : σ < 2) (ht : t < (fam f).n)
    (hs : s < fbits f) :
    resNode z (f + 2) (srcB σ f t) s = z (srcB σ f t) (fpos f s) - z (mirB σ f t) (mpos f t s) := by
  have hb := fam_bounds (s := s) hσ ht
  have hs' : s < 2 ^ 10 := lt_of_lt_of_le hs (fbits_le f)
  have key := linkInd_sum f (fun u' => if u' = srcB σ f t then 1 else 0)
    (fun s' => if s' = s then 1 else 0) z
  simp only [ite_mul, one_mul, zero_mul, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_range,
    hb.1, hs', if_true] at key
  rw [resNode_fam]
  rw [show (∑ y ∈ range (2 ^ 16), ∑ p ∈ range (2 ^ 10), linkInd f (srcB σ f t) s y p * z y p) =
    ∑ y ∈ range (2 ^ 16), ∑ p ∈ range (2 ^ 10), z y p * linkInd f (srcB σ f t) s y p from
    sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => mul_comm _ _, key]
  rw [sum_eq_single σ, sum_eq_single t]
  · simp only [if_true, sum_ite_eq', mem_range, hs]
  · intro t' ht' hne
    rw [if_neg fun he => hne (srcB_inj hσ hσ ht (mem_range.1 ht') he).2]
  · intro h; exact absurd (mem_range.2 ht) h
  · intro σ' hσ' hne
    refine sum_eq_zero fun t' ht' => ?_
    by_cases ht'' : t' < (fam f).n
    · rw [if_neg fun he => hne (srcB_inj hσ (mem_range.1 hσ') ht ht'' he).1]
    · exact absurd (mem_range.1 ht') ht''
  · intro h; exact absurd (mem_range.2 hσ) h

theorem shHoldsN_of_res {z : ℕ → ℕ → F}
    (h : ∀ j < nLinkFam + 2, ∀ u < 2 ^ 16, ∀ q < 2 ^ 10, resNode z j u q = 0) : ShHoldsN z := by
  refine ⟨⟨fun y hy j hj => ?_, fun j hj => ?_⟩, fun f hf σ hσ t ht s hs => ?_⟩
  · have e := h 0 (by decide) y (by have := chainLk_lt hy; omega) j (by omega)
    rw [resNode_zero, if_pos ⟨hj, hy⟩] at e
    exact (CharTwo.add_eq_zero.mp e).symm
  · have e := h 1 (by decide) 0 (Nat.two_pow_pos _) j (by omega)
    rw [resNode_one, if_pos hj] at e
    exact CharTwo.add_eq_zero.mp e
  · have hb := fam_bounds (s := s) hσ ht
    have e := h (f + 2) (by omega) _ hb.1 s (lt_of_lt_of_le hs (fbits_le f))
    rw [resNode_src z hσ ht hs] at e
    exact sub_eq_zero.mp e

/-- **Some node residual table is nonzero** when the node's S truth fails. -/
theorem res_ne_node {z : ℕ → ℕ → F} (h : ¬ ShHoldsN z) :
    ∃ j < nLinkFam + 2, ∃ u < 2 ^ 16, ∃ q < 2 ^ 10, resNode z j u q ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (shHoldsN_of_res hc)

/-! ## The weight's extension is A.9's `w_out + w_in` (the `eqAtR` bridge) -/

theorem sum_slot_eqAtR (θ rp : Fin 10 → F) {b : ℕ} (hb : b + 256 ≤ 2 ^ 10) :
    ∑ q ∈ range (2 ^ 10), eqAtR rp q * slotT θ b q = ∑ σ ∈ range 256, eqAtR θ σ * eqAtR rp (b + σ) := by
  rw [← sum_slotT θ hb]; exact sum_congr rfl fun q _ => mul_comm _ _

theorem slotWS_eq (s : ℕ) (θ rp : Array F) :
    slotWS s θ rp = ∑ σ ∈ range 256, eqAtR (ptA 10 θ) σ * eqAtR (ptA 10 rp) (slotBase s + σ) := rfl

/-- A product weight's extension splits: `Σ_q Σ_y a(y) b(q) A(y) B(q) = (Σ_y a A)(Σ_q b B)`. -/
theorem sum_prod_split (a A : ℕ → F) (b B : ℕ → F) (m n : ℕ) :
    ∑ q ∈ range m, ∑ y ∈ range n, a y * b q * (A y * B q) =
      (∑ y ∈ range n, a y * A y) * ∑ q ∈ range m, b q * B q := by
  rw [mul_comm, sum_mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem eqAtR_zero {n : ℕ} (r : Fin n → F) : eqAtR r 0 = ∏ l : Fin n, (1 - r l) := by
  simp only [eqAtR, Nat.zero_testBit, Bool.false_eq_true, if_false]

theorem eq_zero_pt {n : ℕ} (rb : List F) (hrb : rb.length = n) :
    eqPoint (List.replicate n (0 : F)).toArray rb.toArray = eqAtR (ptOf n rb) 0 := by
  rw [eqPoint_eq, List.size_toArray, List.length_replicate, ptA_toArray, ptA_toArray, eqAtR_zero,
    eq]
  refine prod_congr rfl fun l _ => ?_
  simp [ptOf, List.getD_eq_getElem?_getD]

/-- `shiftEqS` on lists of `n` coordinates: `Σ_u eq(τ, u) eq(r, u + 1)` over `u + 1 < 2^n`. -/
theorem shiftEqS_eq {n : ℕ} (τs rb : List F) (hτ : τs.length = n) (hrb : rb.length = n) :
    shiftEqS τs.toArray rb.toArray = ∑ u ∈ range (2 ^ n),
      eqAtR (ptOf n τs) u * if u + 1 < 2 ^ n then eqAtR (ptOf n rb) (u + 1) else 0 := by
  subst hτ
  show ∑ u : Fin (2 ^ τs.length), ∑ v : Fin (2 ^ τs.length), eq (ptOf τs.length τs) (cube u) *
    succT u v * eq (cube v) (ptOf τs.length rb) = _
  simp only [mul_assoc, ← mul_sum]
  have e : ∀ u : Fin (2 ^ τs.length), ∑ v : Fin (2 ^ τs.length),
      succT u v * eq (cube v) (ptOf τs.length rb) =
        if u.val + 1 < 2 ^ τs.length then eqAtR (ptOf τs.length rb) (u.val + 1) else 0 := by
    intro u
    rw [sum_succT]
    split_ifs with h
    · rw [eq_swap, eq_cube_eqAtR]
    · rfl
  simp only [e, eq_cube_eqAtR]
  exact Fin.sum_univ_eq_sum_range (fun u => eqAtR (ptOf τs.length τs) u *
    if u + 1 < 2 ^ τs.length then eqAtR (ptOf τs.length rb) (u + 1) else 0) _

/-- **The leaf's final value** (A.9 `finSh` (ii), a leaf; revision 3.15's padded points): the
weight's extension at `(r_blk, r_pos)` is `w_out + w_in` on the specifications. -/
theorem final_leaf {nb : ℕ} (hnb : nb ≤ 18) (τs rb : List F) (hτ : τs.length = nb)
    (hrb : rb.length = nb) (θ rp : Array F) (κ : F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb),
        eqAtR (ptOf nb rb) y * eqAtR (ptA 10 rp) q * wLeaf (ptOf nb τs) (ptA 10 θ) κ y q =
      eqPoint (τs ++ List.replicate (18 - nb) 0).toArray (rb ++ List.replicate (18 - nb) 0).toArray *
          slotWS 0 θ rp +
        (shiftEqS (τs ++ List.replicate (18 - nb) 0).toArray
            (rb ++ List.replicate (18 - nb) 0).toArray +
          κ * eqPoint (Array.replicate 18 0) (rb ++ List.replicate (18 - nb) 0).toArray) *
          slotWS 1 θ rp := by
  have h18 : Array.replicate 18 (0 : F) =
      (List.replicate nb (0 : F) ++ List.replicate (18 - nb) (0 : F)).toArray := by
    rw [← List.replicate_add, Nat.add_sub_cancel' hnb]; rfl
  rw [eqPoint_pad _ _ _ (by rw [hτ, hrb]), shiftEqS_pad _ _ _ (by rw [hτ, hrb]), h18,
    eqPoint_pad _ _ _ (by rw [List.length_replicate, hrb]), eq_zero_pt rb hrb, shiftEqS_eq τs rb hτ hrb,
    eqPoint_eq, List.size_toArray, hτ, ptA_toArray nb τs, ptA_toArray nb rb, slotWS_eq, slotWS_eq]
  have hN : 2 ^ nb = (2 ^ nb - 1) + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  have hsh : ∑ y ∈ range (2 ^ nb), eqAtR (ptOf nb rb) y * shL (ptOf nb τs) κ y =
      ∑ u ∈ range (2 ^ nb), eqAtR (ptOf nb τs) u *
        (if u + 1 < 2 ^ nb then eqAtR (ptOf nb rb) (u + 1) else 0) + κ * eqAtR (ptOf nb rb) 0 := by
    simp only [shL, mul_add, sum_add_distrib, mul_ite, mul_zero, mul_one, sum_ite_eq', mem_range,
      Nat.two_pow_pos, if_true]
    rw [hN, sum_range_succ', sum_range_succ, if_neg (by omega), add_zero, if_neg (by omega),
      add_zero]
    have e : ∀ u ∈ range (2 ^ nb - 1), (if 1 ≤ u + 1 then eqAtR (ptOf nb rb) (u + 1) *
        eqAtR (ptOf nb τs) (u + 1 - 1) else 0) = (if u + 1 < 2 ^ nb - 1 + 1 then
          eqAtR (ptOf nb τs) u * eqAtR (ptOf nb rb) (u + 1) else 0) := fun u hu => by
      have := mem_range.1 hu
      rw [if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel, mul_comm]
    rw [sum_congr rfl e, mul_comm κ]
  simp only [wLeaf, mul_add, sum_add_distrib]
  rw [sum_prod_split, sum_prod_split, sum_slot_eqAtR _ _ (by norm_num),
    sum_slot_eqAtR _ _ (by norm_num), sum_eqAtR_mul, eq_swap, hsh]
  rfl

/-- `Σ_{y<2^16} [lk y] g(y)` is the sum over the two chains' link blocks `c·N + k`, `k < N − 1`
(`shiftMaskS`'s index set). -/
theorem sum_chainLk (g : ℕ → F) :
    ∑ y ∈ range (2 ^ 16), (if chainLk y then g y else 0) =
      ∑ c ∈ range 2, ∑ k ∈ range (Layout.chainN - 1), g (c * Layout.chainN + k) := by
  have hN : Layout.chainN = 23146 := rfl
  have hsplit : 2 ^ 16 = (Layout.chainN - 1) + (1 + ((Layout.chainN - 1) + (1 +
      (2 ^ 16 - 2 * Layout.chainN)))) := by rw [hN]; norm_num
  rw [hsplit, sum_range_add, sum_range_add, sum_range_add, sum_range_add, sum_range_one,
    sum_range_one, sum_range_succ, sum_range_one]
  have l1 : ∀ k ∈ range (Layout.chainN - 1), (if chainLk k then g k else 0) = g k := fun k hk => by
    have := mem_range.1 hk; rw [if_pos (by unfold chainLk; omega)]
  have l2 : ¬ chainLk (Layout.chainN - 1 + 0) := by unfold chainLk; omega
  have l3 : ∀ k ∈ range (Layout.chainN - 1), (if chainLk (Layout.chainN - 1 + (1 + k))
      then g (Layout.chainN - 1 + (1 + k)) else 0) = g (1 * Layout.chainN + k) := fun k hk => by
    have := mem_range.1 hk
    rw [if_pos (by unfold chainLk; omega), show Layout.chainN - 1 + (1 + k) =
      1 * Layout.chainN + k by rw [hN]; omega]
  have l4 : ¬ chainLk (Layout.chainN - 1 + (1 + (Layout.chainN - 1 + 0))) := by
    unfold chainLk; omega
  have l5 : ∀ k ∈ range (2 ^ 16 - 2 * Layout.chainN), (if chainLk (Layout.chainN - 1 + (1 +
      (Layout.chainN - 1 + (1 + k)))) then g (Layout.chainN - 1 + (1 + (Layout.chainN - 1 +
        (1 + k)))) else 0) = 0 := fun k _ => by rw [if_neg (by unfold chainLk; omega)]
  rw [sum_congr rfl l1, if_neg l2, sum_congr rfl l3, if_neg l4, sum_congr rfl l5, sum_const_zero]
  simp only [zero_mul, zero_add, add_zero]

theorem linkSum_eq (W : Array F) (ks : F) : ∀ n, n ≤ nLinkFam → ∀ acc pow,
    linkSum W ks n acc pow = acc + ∑ i ∈ range n, pow * ks ^ i * W.getD (nLinkFam - n + i) 0
  | 0, _, acc, pow => by simp [linkSum]
  | n + 1, hn, acc, pow => by
    rw [linkSum, linkSum_eq W ks n (by omega), sum_range_succ', pow_zero, mul_one, add_zero]
    have hs : ∑ i ∈ range n, pow * ks * ks ^ i * W.getD (nLinkFam - n + i) 0 =
        ∑ i ∈ range n, pow * ks ^ (i + 1) * W.getD (nLinkFam - (n + 1) + (i + 1)) 0 :=
      sum_congr rfl fun i _ => by
        rw [show nLinkFam - (n + 1) + (i + 1) = nLinkFam - n + i by omega, pow_succ]; ring
    rw [hs]; ring

/-- **The node's final value** (A.9 `finSh` (ii), a node): the weight's extension at
`(r_blk, r_pos)` is `w_out + w_in` on the specifications (`shiftMaskS`, `slotWS`,
`linkWAllS` at the packed points, `linkSum`). -/
theorem final_node (τs rb : List F) (hτ : τs.length = 16) (hrb : rb.length = 16) (θ rp : Array F)
    (κ : F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16),
        eqAtR (ptOf 16 rb) y * eqAtR (ptA 10 rp) q * wNode (ptOf 16 τs) (ptA 10 θ) κ y q =
      (shiftMaskS (τs ++ [0, 0]).toArray (rb ++ [0, 0]).toArray).1 * slotWS 0 θ rp +
        linkSum (linkWAllS (τs ++ θ.toList).toArray (rb ++ rp.toList).toArray) κ nLinkFam
          (((shiftMaskS (τs ++ [0, 0]).toArray (rb ++ [0, 0]).toArray).2.1 +
            κ * (shiftMaskS (τs ++ [0, 0]).toArray (rb ++ [0, 0]).toArray).2.2) * slotWS 2 θ rp)
          (κ * κ) := by
  set τ := ptOf 16 τs
  set r := ptOf 16 rb
  have hpτ : ptA 16 (τs ++ [0, 0]).toArray = τ := by
    rw [ptA_toArray]; funext l
    simp only [τ, ptOf, show [(0 : F), 0] = List.replicate 2 0 from rfl, getD_pad]
  have hpr : ptA 16 (rb ++ [0, 0]).toArray = r := by
    rw [ptA_toArray]; funext l
    simp only [r, ptOf, show [(0 : F), 0] = List.replicate 2 0 from rfl, getD_pad]
  have hgt : ∀ (xs : List F) (ys : Array F), xs.length = 16 →
      ptA 16 (xs ++ ys.toList).toArray = ptOf 16 xs ∧
        (fun l : Fin 10 => (xs ++ ys.toList).toArray.getD (16 + l.val) 0) = ptA 10 ys := by
    intro xs ys hx
    refine ⟨?_, ?_⟩
    · rw [ptA_toArray]; funext l
      simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_append_left (show l.val < xs.length
        by rw [hx]; exact l.isLt)]
    · funext l
      simp [ptA, Array.getD_eq_getD_getElem?, List.getElem?_append_right (show xs.length ≤ 16 + l
        by omega), hx]
  obtain ⟨ht1, ht2⟩ := hgt τs θ hτ
  obtain ⟨hr1, hr2⟩ := hgt rb rp hrb
  -- the three block weights
  have hE : (shiftMaskS (τs ++ [0, 0]).toArray (rb ++ [0, 0]).toArray).1 =
      ∑ y ∈ range (2 ^ 16), eqAtR r y * lkW τ y := by
    simp only [shiftMaskS, hpτ, hpr, lkW, mul_ite, mul_zero]
    rw [← sum_chainLk (fun y => eqAtR τ y * eqAtR r y)]
    exact sum_congr rfl fun y _ => by split_ifs <;> ring
  have hSh : (shiftMaskS (τs ++ [0, 0]).toArray (rb ++ [0, 0]).toArray).2.1 +
      κ * (shiftMaskS (τs ++ [0, 0]).toArray (rb ++ [0, 0]).toArray).2.2 =
      ∑ y ∈ range (2 ^ 16), eqAtR r y * shN τ κ y := by
    have hN : Layout.chainN < 2 ^ 16 := by simp [Layout.chainN]
    simp only [shiftMaskS, hpτ, hpr]
    rw [← sum_chainLk (fun y => eqAtR τ y * eqAtR r (y + 1))]
    simp only [shN, mul_add, sum_add_distrib, mul_ite, mul_zero, mul_one, ← mul_sum,
      sum_ite_eq', mem_range, hN, Nat.two_pow_pos, if_true]
    rw [show 2 ^ 16 = (2 ^ 16 - 1) + 1 from rfl, sum_range_succ' (fun y => if 1 ≤ y ∧ chainLk (y - 1)
      then eqAtR r y * eqAtR τ (y - 1) else 0), sum_range_succ]
    have hl : ¬ chainLk (2 ^ 16 - 1) := by unfold chainLk Layout.chainN; omega
    simp only [hl, if_false, add_zero, show ¬ (1 ≤ 0 ∧ chainLk (0 - 1)) from fun h => absurd h.1
      (by omega), Nat.add_sub_cancel, show ∀ u, 1 ≤ u + 1 from fun u => by omega, true_and]
    have e : ∀ x ∈ range (2 ^ 16 - 1), (if chainLk x then eqAtR τ x * eqAtR r (x + 1) else 0) =
        (if chainLk x then eqAtR r (x + 1) * eqAtR τ x else 0) := fun x _ => by split_ifs <;> ring
    rw [sum_congr rfl e]; ring
  -- the families
  have hF : ∀ f, ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16), eqAtR r y * eqAtR (ptA 10 rp) q *
      famW f τ (ptA 10 θ) y q = linkWS f τ (ptA 10 θ) r (ptA 10 rp) := by
    intro f
    rw [linkW_mle]
    simp only [famW, mul_sum]
    rw [sum_perm4, sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
      sum_congr rfl fun _ _ => by ring
  have hW : ∀ i < nLinkFam, (linkWAllS (τs ++ θ.toList).toArray (rb ++ rp.toList).toArray).getD i 0 =
      linkWS i τ (ptA 10 θ) r (ptA 10 rp) := by
    intro i hi
    unfold linkWAllS
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hi, Option.getD_some, ht1, ht2,
      hr1, hr2]
  rw [linkSum_eq _ _ _ le_rfl, Nat.sub_self]
  simp only [zero_add]
  have hL8 : ∑ x ∈ range nLinkFam, κ * κ * κ ^ x *
      (linkWAllS (τs ++ θ.toList).toArray (rb ++ rp.toList).toArray).getD x 0 =
      ∑ f ∈ range nLinkFam, κ ^ (f + 2) * linkWS f τ (ptA 10 θ) r (ptA 10 rp) :=
    sum_congr rfl fun i hi => by rw [hW i (mem_range.1 hi)]; ring
  rw [hL8, hE, hSh]
  simp only [wNode, mul_add, sum_add_distrib, mul_sum]
  rw [sum_prod_split, sum_prod_split, sum_slot_eqAtR _ _ (by norm_num),
    sum_slot_eqAtR _ _ (by norm_num), slotWS_eq, slotWS_eq]
  have hfam : ∑ x ∈ range (2 ^ 10), ∑ x_1 ∈ range (2 ^ 16), ∑ i ∈ range nLinkFam,
      eqAtR r x_1 * eqAtR (ptA 10 rp) x * (κ ^ (i + 2) * famW i τ (ptA 10 θ) x_1 x) =
      ∑ f ∈ range nLinkFam, κ ^ (f + 2) * linkWS f τ (ptA 10 θ) r (ptA 10 rp) := by
    rw [sum_congr rfl fun x _ => sum_comm, sum_comm]
    refine sum_congr rfl fun f _ => ?_
    rw [← hF f, mul_sum]
    exact sum_congr rfl fun _ _ => by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  rw [hfam, show slotBase 0 = 256 from rfl, show slotBase 2 = 0 from rfl]
  ring

/-! ## S1's Schwartz–Zippel row over its coordinate list -/

/-- S1's coordinates that the residual reads: `τ`'s first `nb` (of 18 drawn), then `θ`'s 10
(coordinates 18 … 27). -/
def selC (nb : ℕ) (l : List F) : List F := l.take nb ++ (l.drop 18).take 10

/-- **S1's doom on a coordinate prefix**: up to `κ_s` (coordinate 28), some residual table with the
read coordinates bound is nonzero; from `κ_s` on, the batched residual `Σ_j κ_s^j R̃_j(τ, θ)` is
nonzero. -/
def DoomS (nb J : ℕ) (T : ℕ → Array F) (l : List F) : Prop :=
  if l.length ≤ 28 then ∃ j < J, mlDoom (nb + 10) (T j) (selC nb l)
  else ∑ j ∈ range J, l.getD 28 0 ^ j * mle (tbl (nb + 10) (T j)) (ptOf (nb + 10) (selC nb l)) ≠ 0

/-- The per-coordinate losses: one per read multilinear coordinate, `J − 1` at `κ_s`. -/
def bS (nb J i : ℕ) : ℕ :=
  if i < nb then 1 else if i < 18 then 0 else if i < 28 then 1 else if i = 28 then J - 1 else 0

theorem sum_bS {nb J : ℕ} (hnb : nb ≤ 18) : ∑ i ∈ range 30, bS nb J i = nb + 10 + (J - 1) := by
  have h : ∀ i, bS nb J i = (if i < nb then 1 else 0) + (if 18 ≤ i ∧ i < 28 then 1 else 0) +
      (if i = 28 then J - 1 else 0) := fun i => by
    unfold bS; split_ifs <;> omega
  simp only [h, sum_add_distrib, sum_ite_eq', mem_range, show 28 < 30 by norm_num, if_true]
  rw [sum_boole, sum_boole]
  have e1 : (range 30).filter (· < nb) = range nb := by
    ext x; simp only [mem_filter, mem_range]; omega
  have e2 : ((range 30).filter fun x => 18 ≤ x ∧ x < 28).card = 10 := by decide
  rw [e1, e2, card_range]; simp

theorem selC_lt {nb : ℕ} {l : List F} (hl : l.length < nb) (hnb : nb ≤ 18) (c : F) :
    selC nb (l ++ [c]) = selC nb l ++ [c] := by
  have h1 : (l ++ [c]).drop 18 = [] := List.drop_eq_nil_of_le (by simp; omega)
  have h2 : l.drop 18 = [] := List.drop_eq_nil_of_le (by omega)
  simp [selC, h1, h2, List.take_of_length_le (show l.length ≤ nb by omega),
    List.take_of_length_le (show (l ++ [c]).length ≤ nb by simp; omega)]

theorem selC_mid {nb : ℕ} {l : List F} (h1 : nb ≤ l.length) (h2 : l.length < 18) (c : F) :
    selC nb (l ++ [c]) = selC nb l := by
  have e1 : (l ++ [c]).drop 18 = [] := List.drop_eq_nil_of_le (by simp; omega)
  have e2 : l.drop 18 = [] := List.drop_eq_nil_of_le (by omega)
  simp [selC, e1, e2, List.take_append_of_le_length h1]

theorem selC_th {nb : ℕ} {l : List F} (hnb : nb ≤ 18) (h1 : 18 ≤ l.length) (h2 : l.length < 28)
    (c : F) : selC nb (l ++ [c]) = selC nb l ++ [c] := by
  simp only [selC, List.take_append_of_le_length (show nb ≤ l.length by omega),
    List.drop_append_of_le_length h1, List.append_assoc]
  rw [List.take_of_length_le (l := l.drop 18 ++ [c]) (i := 10) (by simp; omega),
    List.take_of_length_le (l := l.drop 18) (i := 10) (by simp; omega)]

theorem selC_end {nb : ℕ} {l : List F} (hnb : nb ≤ 18) (h1 : 28 ≤ l.length) (c : F) :
    selC nb (l ++ [c]) = selC nb l := by
  simp only [selC, List.take_append_of_le_length (show nb ≤ l.length by omega),
    List.drop_append_of_le_length (show 18 ≤ l.length by omega),
    List.take_append_of_le_length (show 10 ≤ (l.drop 18).length by simp; omega)]

theorem selC_length {nb : ℕ} {l : List F} (hnb : nb ≤ 18) (h : 28 ≤ l.length) :
    (selC nb l).length = nb + 10 := by
  rw [selC, List.length_append, List.length_take, List.length_take, List.length_drop]; omega

theorem getD_snoc_28 {l : List F} (h : l.length = 28) (c : F) : (l ++ [c]).getD 28 0 = c := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show l.length ≤ 28 by omega), h]

theorem getD_snoc_lt {l : List F} (h : 28 < l.length) (c : F) :
    (l ++ [c]).getD 28 0 = l.getD 28 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

open Classical in
/-- **S1's per-coordinate loss**: a read multilinear coordinate loses at most one value (some
residual table stays nonzero), an unread one none, `κ_s` at most `J − 1` (a nonzero polynomial of
degree `< J`). -/
theorem doomS_step {nb J : ℕ} (hnb : nb ≤ 18) (hJ : 1 ≤ J) {T : ℕ → Array F}
    (hT : ∀ j, (T j).size = 2 ^ (nb + 10)) (l : List F) (hd : DoomS nb J T l) :
    (univ.filter fun c => ¬ DoomS nb J T (l ++ [c])).card ≤ bS nb J l.length := by
  have hlen : ∀ c, (l ++ [c]).length = l.length + 1 := fun c => by simp
  by_cases hA : l.length ≤ 27
  · have hl : l.length ≤ 28 := by omega
    rw [DoomS, if_pos hl] at hd
    obtain ⟨j₀, hj₀, hm⟩ := hd
    have hsub : ∀ S : List F → List F, (∀ c, selC nb (l ++ [c]) = S [c]) →
        (univ.filter fun c => ¬ DoomS nb J T (l ++ [c])).card ≤
          (univ.filter fun c => ¬ mlDoom (nb + 10) (T j₀) (S [c])).card := fun S hS =>
      card_le_card fun c hc => by
        have hc' := (mem_filter.1 hc).2
        rw [DoomS, if_pos (show (l ++ [c]).length ≤ 28 by rw [hlen]; omega)] at hc'
        refine mem_filter.2 ⟨mem_univ _, fun h => hc' ⟨j₀, hj₀, ?_⟩⟩
        rw [hS c]; exact h
    by_cases h1 : l.length < nb
    · refine (hsub (fun x => selC nb l ++ x) fun c => selC_lt h1 hnb c).trans ?_
      refine (mlDoom_step (hT j₀) _ hm).trans ?_
      simp only [bS, if_pos h1]; split_ifs <;> omega
    by_cases h2 : l.length < 18
    · rw [filter_false_of_mem fun c _ hc => hc (by
        rw [DoomS, if_pos (by rw [hlen]; omega), selC_mid (by omega) h2]; exact ⟨j₀, hj₀, hm⟩)]
      simp
    · refine (hsub (fun x => selC nb l ++ x) fun c => selC_th hnb (by omega) (by omega) c).trans ?_
      refine (mlDoom_step (hT j₀) _ hm).trans ?_
      simp only [bS, if_neg h1, if_neg h2, if_pos (show l.length < 28 by omega)]
      split_ifs <;> omega
  by_cases hB : l.length = 28
  · rw [DoomS, if_pos (by omega)] at hd
    obtain ⟨j₀, hj₀, hm⟩ := hd
    have hsl := selC_length (l := l) hnb (by omega)
    set a : ℕ → F := fun j => mle (tbl (nb + 10) (T j)) (ptOf (nb + 10) (selC nb l))
    have ha : a j₀ ≠ 0 := by
      have := (mlDoom_full (T j₀) (hT j₀) (selC nb l) hsl.ge).1 hm
      rwa [List.take_of_length_le (l := selC nb l) hsl.le] at this
    obtain ⟨k, rfl⟩ : ∃ k, J = k + 1 := ⟨J - 1, by omega⟩
    have hv : (fun i : Fin (k + 1) => a i) ≠ fun _ => 0 := fun he =>
      ha (by simpa using congrFun he ⟨j₀, hj₀⟩)
    refine le_trans (card_le_card fun c hc => ?_) ((batch_pow_bad_le hv).trans ?_)
    · have hc' := (mem_filter.1 hc).2
      rw [DoomS, if_neg (show ¬ (l ++ [c]).length ≤ 28 by rw [hlen]; omega), not_not,
        selC_end (l := l) hnb (by omega), getD_snoc_28 hB] at hc'
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [Fin.sum_univ_eq_sum_range (fun i => c ^ i * a i)]
      simp only [mul_zero, sum_const_zero]
      exact hc'
    · simp [bS, hB, show ¬ 28 < nb by omega]
  · rw [DoomS, if_neg (by omega)] at hd
    rw [filter_false_of_mem fun c _ hc => hc (by
      rw [DoomS, if_neg (by rw [hlen]; omega), selC_end hnb (by omega), getD_snoc_lt (by omega)]
      exact hd)]
    simp

end FR.Snd
