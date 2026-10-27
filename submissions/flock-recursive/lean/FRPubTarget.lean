-- New for `flock-recursive` (BLUEPRINT rev. 3.8 §2.3 step 2, A.8 `targetS`; owner S-C).
import FRSpartan

/-!
# The public target on the skip set (`targetS`)

The zerocheck's Z2 rebuilds `P^{ab}|_S = P^z|_S + P^e|_S` from the public target `E`
(rev. 3.8, skip-c): `P^e(σ) = Σ_{x′} eq(r, x′) E(x′, σ)` for the 64 skip points `σ`
(`targetS`). The verifier computes it per kind and per pinned position: with the layout `x′ =
(hi, blk)` (high position bits low, blocks high) and `E(σ, hi, t) = Σ_κ Ind_κ(t) E_κ(σ, hi)` (the
kinds are public block intervals, a pinned position's value is constant on its kind),
**`targetS_eq`** gives `P^e(σ) = Σ_hi eq(r_hi, hi) Σ_κ E_κ(σ, hi) · Ĩnd_κ(r_blk)`, and
**`intervalMle_eq`** computes each `Ĩnd_κ(r_blk)` as differences of prefix sums over the kind's
intervals (`prefixP`, `O(n²)` each). Per-block affine patterns (`t_lo`) are not covered here.
-/

namespace FR

open Finset

variable {R : Type*} [CommRing R]

/-- `P^e(σ) = Σ_{x′} eq(r, x′) E(σ, x′)`, the public target on the skip point `σ`. -/
def targetS {ℓ : ℕ} (r : Fin ℓ → R) (E : Fin 64 → Fin (2 ^ ℓ) → R) (σ : Fin 64) : R :=
  ∑ u, eq r (cube u) * E σ u

/-- The weight of `eq(r, x)`, bit by bit. -/
def e1 {n : ℕ} (r : Fin n → R) (l : Fin n) (b : Bool) : R := if b then r l else 1 - r l

/-- **An interval indicator's extension** (`Ĩnd_κ`): differences of prefix sums. -/
theorem intervalMle_eq {n : ℕ} (r : Fin n → R) (ivs : List (ℕ × ℕ))
    (h : ∀ p ∈ ivs, p.1 ≤ p.2) :
    mle (selOf ivs) r = (ivs.map fun p ↦ prefixP n (e1 r) p.2 - prefixP n (e1 r) p.1).sum := by
  induction ivs with
  | nil => simp [selOf, mle]
  | cons p ps ih =>
    have hp := h p (List.mem_cons_self ..)
    rw [List.map_cons, List.sum_cons, ← ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq),
      prefixP_eq, prefixP_eq, ← Finset.sum_sub_distrib]
    simp only [selOf, List.map_cons, List.sum_cons, mle, mul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hx : eq r (cube x) = ∏ l : Fin n, e1 r l (x.val.testBit l) := by
      rw [eq_cube]; exact Finset.prod_congr rfl fun l _ ↦ by unfold e1; split_ifs <;> rfl
    rw [hx]
    split_ifs <;> first | ring1 | (exfalso; omega)

/-- **`targetS_eq`** (A.8 `targetS`): per kind and position, `P^e(σ) = Σ_hi eq(r_hi, hi)
Σ_κ E_κ(σ, hi) · Ĩnd_κ(r_blk)`. -/
theorem targetS_eq {p q K : ℕ} (rhi : Fin p → R) (rb : Fin q → R) (Ind : Fin K → Fin (2 ^ q) → R)
    (Ek : Fin K → Fin 64 → Fin (2 ^ p) → R) (E : Fin 64 → Fin (2 ^ (p + q)) → R)
    (hE : ∀ σ hi t, E σ (join hi t) = ∑ κ, Ind κ t * Ek κ σ hi) (σ : Fin 64) :
    targetS (Fin.append rhi rb) E σ =
      ∑ hi, eq rhi (cube hi) * ∑ κ, Ek κ σ hi * mle (Ind κ) rb := by
  rw [targetS, ← (joinEquiv p q).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun hi _ ↦ ?_
  simp only [show ∀ t, (joinEquiv p q) (hi, t) = join hi t from fun _ ↦ rfl, eq_append_join, hE,
    mle, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

end FR
