-- New for `flock-recursive` (BLUEPRINT §5.3 step (1), B-5). Nothing is copied; the univariate
-- Berlekamp–Welch uniqueness is the textbook argument.
import FRRS

/-!
# Unique decoding of the Reed–Solomon code (BLUEPRINT §5.3 (1))

Generic over a field `K` and `n` distinct points `x : Fin n → K`, for `RS[K, x, k]` and an error
bound `e` with `2e + k ≤ n` (that is, `2e < d = n − k + 1`):

* `close_unique`: a word has at most one codeword within agreement `n − e`;
* `bw_unique`: **Berlekamp–Welch uniqueness**: if `N(x_j) = E(x_j) · u_j` at every position,
  `deg E ≤ a`, `deg N < a + k`, and `u` agrees with `P(x_j)` (`deg P < k`) at `a + k` positions,
  then `N = E · P`;
* `mul_mem_degreeLT`, `poly_eq_zero_of_vanish`: the degree facts used here and in
  `FRProximityLine`.
-/

namespace FR

open Polynomial Finset

variable {K : Type*} [Field K] {n : ℕ}

/-- `deg p ≤ a`, `deg q < b` give `deg (p q) < a + b`. -/
theorem mul_mem_degreeLT {a b : ℕ} {p q : K[X]} (hp : p ∈ degreeLT K (a + 1))
    (hq : q ∈ degreeLT K b) : p * q ∈ degreeLT K (a + b) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hq0 : q = 0
  · simp [hq0]
  have h1 := (natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp)
  have h2 := (natDegree_lt_iff_degree_lt hq0).2 (mem_degreeLT.1 hq)
  rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt (mul_ne_zero hp0 hq0), natDegree_mul hp0 hq0]
  omega

/-- A polynomial of degree `< m` vanishing at `m` of the distinct points `x j` is zero. -/
theorem poly_eq_zero_of_vanish {x : Fin n → K} (hx : Function.Injective x) {m : ℕ} {p : K[X]}
    (hp : p ∈ degreeLT K m) (S : Finset (Fin n)) (hS : m ≤ S.card)
    (h : ∀ j ∈ S, p.eval (x j) = 0) : p = 0 := by
  classical
  exact poly_eq_of_agree hx (mem_degreeLT.1 hp) (by simp) S hS fun j hj => by simp [h j hj]

variable [DecidableEq K]

/-- **`close_unique`**: if `2e + k ≤ n`, at most one codeword of `RS[K, x, k]` agrees with `u` on
`n − e` positions. -/
theorem close_unique {x : Fin n → K} (hx : Function.Injective x) {k e : ℕ} (h : 2 * e + k ≤ n)
    {u w w' : Fin n → K} (hw : w ∈ rsCode x k) (hw' : w' ∈ rsCode x k)
    (hc : n - e ≤ (agreeSet u w).card) (hc' : n - e ≤ (agreeSet u w').card) : w = w' := by
  refine rs_eq_of_agree hx hw hw' (agreeSet u w ∩ agreeSet u w') ?_ fun j hj => ?_
  · have h1 := card_union_add_card_inter (agreeSet u w) (agreeSet u w')
    have h2 : (agreeSet u w ∪ agreeSet u w').card ≤ n := by
      simpa using card_le_univ (agreeSet u w ∪ agreeSet u w')
    omega
  · obtain ⟨h1, h2⟩ := mem_inter.1 hj
    exact (mem_agreeSet.1 h1).symm.trans (mem_agreeSet.1 h2)

omit [DecidableEq K] in
/-- **`bw_unique`** (Berlekamp–Welch): if `N(x_j) = E(x_j) · u_j` for every `j`, `deg E ≤ a`,
`deg N < a + k`, `deg P < k`, and `u_j = P(x_j)` on a set `S` of `a + k` positions, then
`N = E · P`. -/
theorem bw_unique {x : Fin n → K} (hx : Function.Injective x) {a k : ℕ} {E N P : K[X]}
    (hE : E ∈ degreeLT K (a + 1)) (hN : N ∈ degreeLT K (a + k)) (hP : P ∈ degreeLT K k)
    (u : Fin n → K) (hEN : ∀ j, N.eval (x j) = E.eval (x j) * u j) (S : Finset (Fin n))
    (hS : a + k ≤ S.card) (hagree : ∀ j ∈ S, u j = P.eval (x j)) : N = E * P := by
  rw [← sub_eq_zero]
  refine poly_eq_zero_of_vanish hx (sub_mem hN (mul_mem_degreeLT hE hP)) S hS fun j hj => ?_
  rw [eval_sub, eval_mul, hEN, hagree j hj, sub_self]

end FR
