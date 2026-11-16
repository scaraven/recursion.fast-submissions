-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBClearedJet.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LvmJBHeight
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Operations

-- (GOLF2: 15 declarations that `certified` does not use moved verbatim to `LvmWhirDoomJ2Off`, outside its import closure.)

-- ===== merged from `LvmJBJetRecursion` (GOLF module merge: `LvmJBJetRecursion.lean` is now a stub importing `LvmJBClearedJet`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBJetRecursion.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# The jet recursion, over a free variable

This file constructs the finite implicit-function jet of §1 and proves its defining
property.  Two design decisions remove machinery relative to both BCIKS and the plan:

1. **No field extension, no quotient ring.**  The recursion

     `α_t = -ξ⁻¹ · [Uᵗ] R(x₀ + U, Γ_{t-1}(U), Z)`

   never uses `R(x₀, α₀, Z) = 0`: the extraction of the diagonal term
   `∑_j R_{0j} · j · α₀^{j-1} · α_t = ξ · α_t` is an algebraic identity.  So the initial
   root `α₀` can be kept as a *free* symbol, the recursion run over any field `K`
   (downstream, `K = Frac(F[Z][T])` with `α₀ = T`), and the conclusion holds
   unconditionally:

     `R(x₀ + U, Γ_k(U), Z) ≡ R(x₀, α₀, Z)  (mod U^{r+1})`.

   Specialising `(Z, T) ↦ (z, t_z)` at a root `t_z` of the branch factor `H` kills the
   right-hand side *at the end*.  This meshes with the §2 machinery, whose
   `badSpecializations` already quantifies over pairs `(z, t)`.

2. **Hasse–Taylor updates.**  The step `Γ_t = Γ_{t-1} + α_t U^t` is analysed through
   `f(γ + δ) = ∑_ρ (D^ρ f)(γ) · δ^ρ` (Hasse derivatives, so valid in every
   characteristic), never through the multinomial expansion of the full composition.

Throughout, `R : K[X][X]` has the `U`-variable *inner* and the `Y`-variable *outer*;
`R.eval γ` for `γ : K[X]` is substitution of the jet into `Y`.

## Main results

* `jet` — the recursion; `jet R α₀ t` is the `t`-jet `Γ_t ∈ K[U]`.
* `coeff_eval_jet_eq_zero` — the vanishing `[Uˢ] R(Γ_t) = 0` for `1 ≤ s ≤ t`.
* `eval_jet_sub_C_dvd` — the packaged jet property
  `U^{r+1} ∣ R(Γ_k) - C (R(x₀, α₀))`.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### The two structural constants

`xi` and `jetConst` make sense over any commutative ring; keeping them at that
generality is what lets the *same* names be used for the generic branch (over
`FractionRing (F[Z][T])`) and for each of its specialisations (over `F`), so that
specialising is a single naturality lemma rather than a re-derivation. -/

section Base

variable {B : Type*} [CommRing B]

/-- The simple-root value `ξ = (D¹_Y R)(x₀, α₀)`: evaluate the first Hasse derivative
of `R` at `U = 0`, `Y = α₀`.  (The recentering `X = x₀ + U` is assumed already
performed in `R`, so `U = 0` is the point `x₀`.) -/
noncomputable def xi (R : B[X][X]) (α₀ : B) : B :=
  ((hasseDeriv 1 R).map (evalRingHom 0)).eval α₀

/-- The obstruction constant `r₀ = R(x₀, α₀)`.  In the intended instantiation this is
`R(x₀, T, Z)`, killed later by specialising `T` to a root of the branch factor. -/
noncomputable def jetConst (R : B[X][X]) (α₀ : B) : B :=
  (R.map (evalRingHom 0)).eval α₀

end Base

variable {K : Type*} [Field K]

/-! ### The recursion -/

/-- The jet recursion: `Γ_0 = α₀` and
`Γ_{t+1} = Γ_t - ξ⁻¹ · ([U^{t+1}] R(Γ_t)) · U^{t+1}`. -/
noncomputable def jet (R : K[X][X]) (α₀ : K) : ℕ → K[X]
  | 0 => C α₀
  | t + 1 =>
      jet R α₀ t
        - C ((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1))) * X ^ (t + 1)

@[simp] theorem jet_zero (R : K[X][X]) (α₀ : K) : jet R α₀ 0 = C α₀ := rfl

theorem jet_succ (R : K[X][X]) (α₀ : K) (t : ℕ) :
    jet R α₀ (t + 1) =
      jet R α₀ t
        - C ((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1))) * X ^ (t + 1) := rfl

/-- The jet has degree at most its order. -/
theorem natDegree_jet_le (R : K[X][X]) (α₀ : K) : ∀ t, (jet R α₀ t).natDegree ≤ t
  | 0 => by simp
  | t + 1 => by
      rw [jet_succ]
      refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact le_trans (natDegree_jet_le R α₀ t) (by omega)
      · exact natDegree_C_mul_X_pow_le _ _

/-- The constant coefficient of every jet is the initial value `α₀`. -/
theorem jet_coeff_zero (R : K[X][X]) (α₀ : K) : ∀ t, (jet R α₀ t).coeff 0 = α₀
  | 0 => by simp
  | t + 1 => by
      rw [jet_succ, coeff_sub, coeff_mul_X_pow']
      simp [jet_coeff_zero R α₀ t]

/-! ### Hasse–Taylor expansion of an evaluation -/

/-- Taylor expansion of `f.eval (γ + δ)` in the increment `δ`, with Hasse-derivative
coefficients.  Valid over any commutative ring; this is the only expansion tool the
whole jet analysis uses. -/
theorem eval_add_eq_sum_hasseDeriv {S : Type*} [CommRing S] (f : S[X]) (γ δ : S) :
    f.eval (γ + δ) = ∑ ρ ∈ range (f.natDegree + 1), (hasseDeriv ρ f).eval γ * δ ^ ρ := by
  have h1 : f.eval (γ + δ) = f.eval (δ + γ) := by rw [add_comm]
  rw [h1, ← taylor_eval]
  rw [eval_eq_sum_range' (n := f.natDegree + 1) (by rw [natDegree_taylor]; omega)]
  exact Finset.sum_congr rfl fun ρ _ => by rw [taylor_coeff]

/-! ### Constant coefficients of evaluations -/

/-- Extracting the constant `U`-coefficient of `S.eval γ` only sees the constant
coefficients: it equals the `U = 0` slice of `S` evaluated at `γ(0)`. -/
theorem coeff_zero_eval {B : Type*} [CommRing B] (S : B[X][X]) (γ : B[X]) :
    (S.eval γ).coeff 0 = (S.map (evalRingHom 0)).eval (γ.coeff 0) := by
  induction S using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      rw [eval_monomial, map_monomial, eval_monomial]
      rw [coeff_zero_eq_eval_zero, eval_mul, eval_pow]
      rw [coeff_zero_eq_eval_zero]
      simp

/-- The `ξ`-transport: at every stage of the recursion, the constant coefficient of the
first Hasse derivative evaluated at the jet is still `ξ`. -/
theorem coeff_zero_hasseDeriv_eval_jet (R : K[X][X]) (α₀ : K) (t : ℕ) :
    ((hasseDeriv 1 R).eval (jet R α₀ t)).coeff 0 = xi R α₀ := by
  rw [coeff_zero_eval, jet_coeff_zero, xi]

/-! ### The update analysis -/

/-- The Taylor form of one recursion step. -/
theorem eval_jet_succ (R : K[X][X]) (α₀ : K) (t : ℕ) :
    R.eval (jet R α₀ (t + 1)) =
      ∑ ρ ∈ range (R.natDegree + 1),
        (hasseDeriv ρ R).eval (jet R α₀ t) *
          (C (-((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1)))) * X ^ (t + 1)) ^ ρ := by
  have h : jet R α₀ (t + 1) =
      jet R α₀ t +
        C (-((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1)))) * X ^ (t + 1) := by
    rw [jet_succ, map_neg]
    ring
  rw [h, eval_add_eq_sum_hasseDeriv]

/-- Coefficients strictly below the update order are unchanged by one recursion step. -/
theorem coeff_eval_jet_succ_of_le (R : K[X][X]) (α₀ : K) {s t : ℕ} (hs : s ≤ t) :
    (R.eval (jet R α₀ (t + 1))).coeff s = (R.eval (jet R α₀ t)).coeff s := by
  rw [eval_jet_succ, finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro ρ _ hρ
    have hpow : (C (-((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1)))) *
        X ^ (t + 1)) ^ ρ =
        C ((-((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1)))) ^ ρ) *
          X ^ ((t + 1) * ρ) := by
      rw [mul_pow, ← C_pow, ← pow_mul]
    rw [hpow, ← mul_assoc, coeff_mul_X_pow']
    have : ¬ (t + 1) * ρ ≤ s := by
      have hρ1 : 1 ≤ ρ := Nat.one_le_iff_ne_zero.mpr hρ
      nlinarith
    simp [this]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **The cancellation.**  At the update order itself, the `ρ = 1` Taylor term
contributes `ξ · (-ξ⁻¹ · b)` against the old coefficient `b`, so the new coefficient
vanishes.  This needs `ξ ≠ 0` and nothing else. -/
theorem coeff_eval_jet_succ_self (R : K[X][X]) (α₀ : K) (t : ℕ) (hξ : xi R α₀ ≠ 0) :
    (R.eval (jet R α₀ (t + 1))).coeff (t + 1) = 0 := by
  -- `R` is not constant in `Y`: otherwise `ξ = 0`.
  have hdeg : 1 ≤ R.natDegree := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro h0
    have hC : R = C (R.coeff 0) := eq_C_of_natDegree_eq_zero h0
    have : xi R α₀ = 0 := by
      rw [xi, hC, hasseDeriv_C _ _ (by norm_num)]
      simp
    exact hξ this
  set b := (R.eval (jet R α₀ t)).coeff (t + 1) with hb
  set c := -((xi R α₀)⁻¹ * b) with hc
  rw [eval_jet_succ, finsetSum_coeff]
  -- Only `ρ = 0` and `ρ = 1` survive at coefficient `t + 1`.
  have hsub : ({0, 1} : Finset ℕ) ⊆ range (R.natDegree + 1) := by
    intro ρ hρ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ
    rcases hρ with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  have hzero : ∀ ρ ∈ range (R.natDegree + 1), ρ ∉ ({0, 1} : Finset ℕ) →
      ((hasseDeriv ρ R).eval (jet R α₀ t) *
        (C c * X ^ (t + 1)) ^ ρ).coeff (t + 1) = 0 := by
    intro ρ _ hρnot
    have hρ2 : 2 ≤ ρ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hρnot
      omega
    have hpow : (C c * X ^ (t + 1)) ^ ρ = C (c ^ ρ) * X ^ ((t + 1) * ρ) := by
      rw [mul_pow, ← C_pow, ← pow_mul]
    rw [hpow, ← mul_assoc, coeff_mul_X_pow']
    have : ¬ (t + 1) * ρ ≤ t + 1 := by nlinarith
    simp [this]
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
  -- The `ρ = 0` term: the old coefficient `b`.
  have h0 : ((hasseDeriv 0 R).eval (jet R α₀ t) *
      (C c * X ^ (t + 1)) ^ 0).coeff (t + 1) = b := by
    rw [pow_zero, mul_one, hasseDeriv_zero']
  -- The `ρ = 1` term: `ξ · c = -b`.
  have h1 : ((hasseDeriv 1 R).eval (jet R α₀ t) *
      (C c * X ^ (t + 1)) ^ 1).coeff (t + 1) = xi R α₀ * c := by
    rw [pow_one, ← mul_assoc, coeff_mul_X_pow']
    simp only [le_refl, if_true, Nat.sub_self]
    rw [coeff_mul_C, coeff_zero_hasseDeriv_eval_jet]
  rw [h0, h1, hc]
  field_simp
  ring

/-! ### The vanishing theorem and the jet property -/

/-- **The vanishing.**  All `U`-coefficients of `R(Γ_t)` in orders `1, …, t` are zero:
the `t`-jet solves the equation to order `t`. -/
theorem coeff_eval_jet_eq_zero (R : K[X][X]) (α₀ : K) (hξ : xi R α₀ ≠ 0) :
    ∀ t, ∀ s, 1 ≤ s → s ≤ t → (R.eval (jet R α₀ t)).coeff s = 0 := by
  intro t
  induction t with
  | zero => (clear * -; omega)
  | succ t ih =>
      intro s hs1 hst
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · rw [coeff_eval_jet_succ_of_le R α₀ (by (clear * - hlt; omega))]
        exact ih s hs1 (by (clear * - hlt; omega))
      · have : s = t + 1 := by (clear * - hst hge; omega)
        rw [this]
        exact coeff_eval_jet_succ_self R α₀ t hξ

/-- The constant coefficient of `R(Γ_t)` is the obstruction `r₀ = R(x₀, α₀)`,
independently of `t`. -/
theorem coeff_zero_eval_jet (R : K[X][X]) (α₀ : K) (t : ℕ) :
    (R.eval (jet R α₀ t)).coeff 0 = jetConst R α₀ := by
  rw [coeff_zero_eval, jet_coeff_zero, jetConst]

end JBAgreement
end
-- ===== end of `LvmJBJetRecursion` =====

-- ===== merged from `LvmJBJetLedger` (GOLF module merge: `LvmJBJetLedger.lean` is now a stub importing `LvmJBClearedJet`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBJetLedger.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# The ledger: linear size growth along the jet recursion

This file proves the load-bearing estimate of the finite-jet argument: the jet
coefficients, cleared by the denominator `ξ^(2t-1)`, have *sizes growing linearly
in `t`*.  Both relevant sizes — the `Z`-height and the `T`-degree of numerators in
`A = F[Z][T]` — are handled at once through an abstract `SizeSystem`.

## The ledger

For the cleared coefficients

  `c_{r,s}(t) = ξ^(ledger t s) · [Uˢ]((D^r_Y R)(Γ_t))`,

the clearing exponents form the *ledger*

  `ledger t s = 0` (`s = 0`), `2s - 1` (`1 ≤ s ≤ t`), `2s - 2` (`s > t`),

and the whole analysis rests on a single inequality (`ledger_slack`): under the
Hasse–Taylor update `Γ_t = Γ_{t-1} + α_t U^t`, every term has nonnegative ledger slack

  `ledger (t-1) s' + ρ·(2t-1) ≤ ledger t s`,   `s = s' + t·ρ`.

This replaces the multi-index combinatorics of the height calculation (BCIKS
Claim 5.10): the "at least two nonzero parts" phenomenon is absorbed into the ledger
table.

## The collapse

Choosing the size bound *proportional to the ledger*,

  `size(c_{r,s}(t)) ≤ (m₀ + mξ) · (ledger t s + 1)`,

makes the inductive step automatic: a term with ledger slack `σ` picks up size at most
`ρ`-fold the jet coefficient bound plus `σ · mξ`, and the ledger identity converts this
into exactly the target bound.  No further case analysis is needed beyond
`ledger_slack` itself.

## Main results

* `SizeSystem` — the abstract size interface; `heightSizeSystem`, `degreeSizeSystem`.
* `ledger_slack` — the slack inequality.
* `jet_ledger` — the invariant: integrality and linear size of all cleared
  coefficients.
* `jet_coeff_integral` — the corollary used downstream: `ξ^(2t-1) · α_t` is integral
  of size at most `(mR + d·mα + mξ) · (2t - 1)`.  Linear in `t`: this is the estimate
  that puts `2r + 1` for the chosen jet order — not `D_X` — into the §3 branch bound. Weighted factor selection
  then sums exact capacities, improving the final threshold from the original `η⁵`
  and the intermediate uniform-bucket `η⁴` to `η³`.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### Abstract size systems -/

/-- An abstract *size* on a commutative ring: `P g m` says "`g` has size at most `m`".
Sizes are stable under negation and addition, and add under multiplication.  Both the
`Z`-height (`IsHeightLE`) and the `T`-degree on `F[Z][T]` are instances. -/
structure SizeSystem (A : Type*) [CommRing A] where
  P : A → ℕ → Prop
  mono : ∀ {g m m'}, P g m → m ≤ m' → P g m'
  zero : ∀ m, P 0 m
  one : P 1 0
  neg : ∀ {g m}, P g m → P (-g) m
  add : ∀ {g h m}, P g m → P h m → P (g + h) m
  mul : ∀ {g h m m'}, P g m → P h m' → P (g * h) (m + m')

namespace SizeSystem

variable {A : Type*} [CommRing A] (SS : SizeSystem A)

theorem pow {g : A} {m : ℕ} (h : SS.P g m) (n : ℕ) : SS.P (g ^ n) (n * m) := by
  induction n with
  | zero => simpa using SS.one
  | succ n ih =>
      rw [pow_succ]
      exact SS.mono (SS.mul ih h) (le_of_eq (by ring))

theorem nsmul {g : A} {m : ℕ} (h : SS.P g m) (n : ℕ) : SS.P (n • g) m := by
  induction n with
  | zero => simpa using SS.zero m
  | succ n ih =>
      rw [succ_nsmul]
      exact SS.add ih h

theorem sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) {m : ℕ}
    (hf : ∀ i ∈ s, SS.P (f i) m) : SS.P (∑ i ∈ s, f i) m := by
  induction s using Finset.induction with
  | empty => simpa using SS.zero m
  | insert x s hx ih =>
      rw [Finset.sum_insert hx]
      exact SS.add (hf x (Finset.mem_insert_self x s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end SizeSystem

/-- Negation preserves heights. -/
theorem IsHeightLE.neg {F : Type*} [CommRing F] {p : F[X][X]} {a : ℕ}
    (hp : IsHeightLE p a) : IsHeightLE (-p) a := by
  intro i
  rw [coeff_neg, natDegree_neg]
  exact hp i

/-- The `Z`-height as a size system on `F[Z][T]`. -/
def heightSizeSystem (F : Type*) [CommRing F] : SizeSystem (F[X][X]) where
  P := IsHeightLE
  mono := fun h hle => h.mono hle
  zero := fun _ => IsHeightLE.zero
  one := by
    intro i
    rcases eq_or_ne i 0 with rfl | h
    · simp
    · simp [coeff_one, h]
  neg := IsHeightLE.neg
  add := IsHeightLE.add
  mul := IsHeightLE.mul

/-- The degree (in the outer variable) as a size system on `R[X]`. -/
def degreeSizeSystem (R : Type*) [CommRing R] : SizeSystem (R[X]) where
  P := fun p m => p.natDegree ≤ m
  mono := fun h hle => h.trans hle
  zero := fun m => by simp
  one := by simp
  neg := fun h => by rwa [natDegree_neg]
  add := fun h₁ h₂ => le_trans (natDegree_add_le _ _) (max_le h₁ h₂)
  mul := fun h₁ h₂ => natDegree_mul_le_of_le h₁ h₂

/-! ### The ledger and its slack inequality -/

/-- The clearing exponent for the cleared coefficient `c_{r,s}(t)`. -/
def ledger (t s : ℕ) : ℕ :=
  if s = 0 then 0 else if s ≤ t then 2 * s - 1 else 2 * s - 2

@[simp] theorem ledger_zero_right (t : ℕ) : ledger t 0 = 0 := by simp [ledger]

theorem ledger_self_succ (t : ℕ) : ledger t (t + 1) = 2 * t := by
  simp only [ledger, if_neg (Nat.succ_ne_zero t), if_neg (by omega : ¬ t + 1 ≤ t)]
  omega

/-- **The slack inequality.**  Under the Hasse–Taylor update at order `t + 1`, a term
landing in coefficient `s = s' + (t+1)·ρ` carries the denominator
`ledger t s' + ρ·(2t+1)`, which never exceeds the target `ledger (t+1) s`.

The case `ρ = 0, s' = t + 1` is the crossing where the ledger increments; the cases
`ρ ≥ 1` encode "only previously computed coefficients are available", which in the
multi-index formulation is the *two nonzero parts* argument. -/
theorem ledger_slack (t s' ρ : ℕ) :
    ledger t s' + ρ * (2 * t + 1) ≤ ledger (t + 1) (s' + (t + 1) * ρ) := by
  rcases ρ with _ | ρ'
  · -- ρ = 0 : monotonicity of the ledger in `t`.
    simp only [mul_zero, zero_mul, add_zero]
    unfold ledger
    split_ifs <;> first | contradiction | omega
  rcases ρ' with _ | ρ''
  · -- ρ = 1 : everything is linear.
    simp only [zero_add, mul_one, one_mul]
    unfold ledger
    split_ifs <;> first | contradiction | omega
  · -- ρ ≥ 2 : the landing coefficient is beyond `t + 1`; linearize the products.
    have hnorm : ρ'' + 1 + 1 = ρ'' + 2 := by omega
    rw [hnorm]
    have hkey : ledger t s' + 2 ≤ 2 * s' + (ρ'' + 2) := by
      unfold ledger
      split_ifs <;> (clear hnorm; omega)
    have hs : t + 1 < s' + (t + 1) * (ρ'' + 2) := by
      have hexp : (t + 1) * (ρ'' + 2) = t * ρ'' + ρ'' + 2 * t + 2 := by ring
      rw [hexp]
      generalize t * ρ'' = q
      (clear * - hkey hexp; omega)
    have hs0 : ¬ (s' + (t + 1) * (ρ'' + 2) = 0) := fun h => Nat.not_lt_zero _ (h ▸ hs)
    have hsgt : ¬ (s' + (t + 1) * (ρ'' + 2) ≤ t + 1) := not_le.mpr hs
    conv_rhs => rw [ledger]
    rw [if_neg hs0, if_neg hsgt]
    have hexp2 : 2 * (s' + (t + 1) * (ρ'' + 2)) =
        2 * s' + (ρ'' + 2) * (2 * t + 1) + (ρ'' + 2) := by ring
    rw [hexp2]
    generalize (ρ'' + 2) * (2 * t + 1) = w at *
    (clear * - hkey hexp2; omega)

/-! ### Setup: integral models -/

variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
variable (SS : SizeSystem A)
variable (R : K[X][X]) (R₀ : A[X][X]) (α₀ : K) (a₀ : A) (ξ₀ : A)
variable (d mR mα mξ : ℕ)

section Ledger

variable (hR : R = R₀.map (mapRingHom (algebraMap A K)))
variable (hα : α₀ = algebraMap A K a₀)
variable (hd : R₀.natDegree ≤ d)
variable (hmR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR)
variable (hmα : SS.P a₀ mα)
variable (hmξ : SS.P ξ₀ mξ)
variable (hξint : algebraMap A K ξ₀ = xi R α₀)
variable (hξ0 : xi R α₀ ≠ 0)

include hR hd in
/-- The `Y`-degree of `R` is bounded by `d`. -/
theorem natDegree_R_le : R.natDegree ≤ d := by
  rw [hR]
  exact le_trans (natDegree_map_le) hd

include hR hα hd hmR hmα in
/-- Derivative-sensitive version of `base_integral`.  Evaluating `D^r R` at the
constant `a₀` costs only `d-r` powers of `a₀`; coefficients beyond that range
vanish by the `Y`-degree bound. -/
theorem base_integral_refined (r s : ℕ) :
    ∃ g : A, algebraMap A K g = ((hasseDeriv r R).eval (C α₀)).coeff s ∧
      SS.P g (mR + (d - r) * mα) := by
  have hRd : R.natDegree ≤ d := natDegree_R_le R R₀ d hR hd
  have hdeg : (hasseDeriv r R).natDegree < d + 1 := by
    have h₁ := natDegree_hasseDeriv_le R r
    omega
  have hexp : (hasseDeriv r R).eval (C α₀) =
      ∑ j ∈ range (d + 1), (hasseDeriv r R).coeff j * (C α₀) ^ j :=
    eval_eq_sum_range' hdeg _
  refine ⟨∑ j ∈ range (d + 1),
      (j + r).choose r • ((R₀.coeff (j + r)).coeff s) * a₀ ^ j, ?_, ?_⟩
  · rw [hexp, finsetSum_coeff, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hC : ((C α₀ : K[X]) ^ j) = C (α₀ ^ j) := by rw [← C_pow]
    rw [hC, coeff_mul_C, hasseDeriv_coeff]
    rw [← nsmul_eq_mul, coeff_smul]
    rw [map_mul, map_nsmul, map_pow, ← hα]
    have hcoeff : algebraMap A K ((R₀.coeff (j + r)).coeff s) =
        (R.coeff (j + r)).coeff s := by
      simp [hR, coeff_map]
    rw [hcoeff]
  · refine SS.sum _ _ fun j hj => ?_
    by_cases hjr : j + r ≤ d
    · refine SS.mono (SS.mul (SS.nsmul (hmR (j + r) s) _) (SS.pow hmα j)) ?_
      have hjsub : j ≤ d - r := by omega
      have hjmul : j * mα ≤ (d - r) * mα := Nat.mul_le_mul_right _ hjsub
      omega
    · have hcoeff0 : R₀.coeff (j + r) = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (lt_of_not_ge hjr))
      rw [hcoeff0, coeff_zero, nsmul_zero, zero_mul]
      exact SS.zero _


/-- Pulling a natural scalar out of an evaluation. -/
theorem eval_nsmul' (S : K[X][X]) (γ : K[X]) (n : ℕ) :
    (n • S).eval γ = n • (S.eval γ) := by
  rw [nsmul_eq_mul, eval_mul, eval_natCast, nsmul_eq_mul]

/-- The `(t+1)`-st jet coefficient in closed form. -/
theorem jet_coeff_succ_self (t : ℕ) :
    (jet R α₀ (t + 1)).coeff (t + 1) =
      -((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1))) := by
  rw [jet_succ, coeff_sub, coeff_mul_X_pow']
  have h0 : (jet R α₀ t).coeff (t + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_jet_le R α₀ t) (by omega))
  simp [h0]

/-- The Taylor form of one recursion step, for an arbitrary polynomial `S`. -/
theorem eval_jet_succ_general (S : K[X][X]) (t : ℕ) :
    S.eval (jet R α₀ (t + 1)) =
      ∑ ρ ∈ range (S.natDegree + 1),
        (hasseDeriv ρ S).eval (jet R α₀ t) *
          (C ((jet R α₀ (t + 1)).coeff (t + 1)) * X ^ (t + 1)) ^ ρ := by
  have hj : jet R α₀ (t + 1) =
      jet R α₀ t + C ((jet R α₀ (t + 1)).coeff (t + 1)) * X ^ (t + 1) := by
    conv_lhs => rw [jet_succ]
    rw [jet_coeff_succ_self, map_neg]
    ring
  conv_lhs => rw [hj]
  exact eval_add_eq_sum_hasseDeriv S _ _

include hR hd in
/-- **The update coefficient formula.**  One recursion step, at the level of a single
`U`-coefficient of a single Hasse derivative. -/
theorem coeff_eval_hasseDeriv_jet_succ (r s t : ℕ) :
    ((hasseDeriv r R).eval (jet R α₀ (t + 1))).coeff s =
      ∑ ρ ∈ range (d + 1),
        (ρ + r).choose ρ •
          (if (t + 1) * ρ ≤ s
           then ((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff (s - (t + 1) * ρ) *
                  ((jet R α₀ (t + 1)).coeff (t + 1)) ^ ρ
           else 0) := by
  have hRd : R.natDegree ≤ d := natDegree_R_le R R₀ d hR hd
  set cJ := (jet R α₀ (t + 1)).coeff (t + 1) with hcJdef
  rw [eval_jet_succ_general R α₀ (hasseDeriv r R) t]
  -- Extend the summation range to `d + 1`.
  have hsub : range ((hasseDeriv r R).natDegree + 1) ⊆ range (d + 1) := by
    intro ρ hρ
    have h1 := natDegree_hasseDeriv_le R r
    have h2 := Finset.mem_range.mp hρ
    exact Finset.mem_range.mpr (by omega)
  have hzero : ∀ ρ ∈ range (d + 1), ρ ∉ range ((hasseDeriv r R).natDegree + 1) →
      (hasseDeriv ρ (hasseDeriv r R)).eval (jet R α₀ t) *
        (C cJ * X ^ (t + 1)) ^ ρ = 0 := by
    intro ρ _ hρnot
    have hgt : (hasseDeriv r R).natDegree < ρ := by
      apply Nat.lt_of_not_ge
      intro h
      exact hρnot (Finset.mem_range.mpr (by omega))
    have hz : hasseDeriv ρ (hasseDeriv r R) = 0 := by
      apply Polynomial.ext
      intro n
      rw [hasseDeriv_coeff, coeff_zero, coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
    rw [hz, eval_zero, zero_mul]
  rw [Finset.sum_subset hsub hzero, finsetSum_coeff]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  -- Rewrite the iterated Hasse derivative.
  have hcomp : hasseDeriv ρ (hasseDeriv r R) =
      (ρ + r).choose ρ • hasseDeriv (ρ + r) R := by
    have := LinearMap.congr_fun (hasseDeriv_comp (R := K[X]) ρ r) R
    simpa using this
  rw [hcomp, eval_nsmul', smul_mul_assoc, coeff_smul]
  congr 1
  -- Extract the coefficient of the product with the explicit `X`-power.
  have hpow : (C cJ * X ^ (t + 1)) ^ ρ = C (cJ ^ ρ) * X ^ ((t + 1) * ρ) := by
    rw [mul_pow, ← C_pow, ← pow_mul]
  rw [hpow, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

/-- The `s = 0` column is `t`-independent: it always equals the base value. -/
theorem coeff_zero_column (r t : ℕ) :
    ((hasseDeriv r R).eval (jet R α₀ t)).coeff 0 =
      ((hasseDeriv r R).eval (C α₀)).coeff 0 := by
  rw [coeff_zero_eval, coeff_zero_eval, jet_coeff_zero, coeff_C_zero]

include hR hd hmξ hξint hξ0 in
/-- **Refined ledger with derivative-sensitive base sizes.**

If the constant-jet coefficient of `D^r R` has size `base r`, where `base` decreases
under further Hasse differentiation, then the cleared `(r,s)` coefficient has size

`base r + slope * ledger t s`.

This retains the degree drop from differentiating in `Y`.  For `T`-degree one takes
`base r = d - r`, `slope = d`; for `Z`-height one takes the constant function `dZ`.
The ordinary ledger above deliberately forgets this information and is consequently
three times looser in the branch capacity. -/
theorem jet_ledger_refined (base : ℕ → ℕ) (slope : ℕ)
    (hbase : ∀ r s, ∃ g : A,
      algebraMap A K g = ((hasseDeriv r R).eval (C α₀)).coeff s ∧ SS.P g (base r))
    (hbase_mono : ∀ r ρ, base (ρ + r) ≤ base r)
    (hbase0 : base 0 ≤ slope) (hmξslope : mξ ≤ slope) :
    ∀ t r s, ∃ g : A,
      algebraMap A K g =
        xi R α₀ ^ ledger t s * (((hasseDeriv r R).eval (jet R α₀ t)).coeff s) ∧
      SS.P g (base r + slope * ledger t s) := by
  intro t
  induction t with
  | zero =>
      intro r s
      obtain ⟨g, hg, hgs⟩ := hbase r s
      refine ⟨ξ₀ ^ ledger 0 s * g, ?_, ?_⟩
      · rw [map_mul, map_pow, hξint, hg, jet_zero]
      · refine SS.mono (SS.mul (SS.pow hmξ _) hgs) ?_
        have h₁ : ledger 0 s * mξ ≤ ledger 0 s * slope :=
          Nat.mul_le_mul_left _ hmξslope
        calc
          ledger 0 s * mξ + base r ≤ ledger 0 s * slope + base r :=
            Nat.add_le_add_right h₁ _
          _ = base r + slope * ledger 0 s := by ring
  | succ t ih =>
      intro r s
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · obtain ⟨g, hg, hgs⟩ := hbase r 0
        refine ⟨g, ?_, ?_⟩
        · rw [ledger_zero_right, pow_zero, one_mul,
            coeff_zero_column R α₀ r (t + 1), hg]
        · simpa using hgs
      · choose G hGmap hGsize using ih
        set cJ := (jet R α₀ (t + 1)).coeff (t + 1) with hcJdef
        have hG0 := hGmap 0 (t + 1)
        rw [ledger_self_succ, hasseDeriv_zero'] at hG0
        have hGhat : algebraMap A K (-(G 0 (t + 1))) =
            xi R α₀ ^ (2 * t + 1) * cJ := by
          rw [map_neg, hG0, hcJdef, jet_coeff_succ_self, pow_succ]
          field_simp
        have hGhatSize : SS.P (-(G 0 (t + 1))) (slope * (2 * t + 1)) := by
          have h := hGsize 0 (t + 1)
          rw [ledger_self_succ] at h
          exact SS.neg (SS.mono h (by nlinarith))
        refine ⟨∑ ρ ∈ range (d + 1),
            if (t + 1) * ρ ≤ s
            then (ρ + r).choose ρ •
              (G (ρ + r) (s - (t + 1) * ρ) * (-(G 0 (t + 1))) ^ ρ *
                ξ₀ ^ (ledger (t + 1) s - ledger t (s - (t + 1) * ρ) -
                  ρ * (2 * t + 1)))
            else 0, ?_, ?_⟩
        · rw [coeff_eval_hasseDeriv_jet_succ R R₀ α₀ d hR hd r s t,
            Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          by_cases hcond : (t + 1) * ρ ≤ s
          · rw [if_pos hcond, if_pos hcond]
            set s' := s - (t + 1) * ρ with hs'def
            have hslack := ledger_slack t s' ρ
            have hsum : s' + (t + 1) * ρ = s := by
              rw [hs'def]
              generalize (t + 1) * ρ = v at hcond ⊢
              omega
            rw [hsum] at hslack
            have hexact : ledger t s' + ρ * (2 * t + 1) +
                (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1)) =
                ledger (t + 1) s := by
              generalize ρ * (2 * t + 1) = w at hslack ⊢
              omega
            rw [map_nsmul, map_mul, map_mul, map_pow, map_pow]
            rw [hGmap (ρ + r) s', hGhat, hξint]
            rw [mul_smul_comm]
            congr 1
            rw [mul_pow, ← pow_mul]
            calc xi R α₀ ^ ledger t s' *
                  (((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') *
                  (xi R α₀ ^ ((2 * t + 1) * ρ) * cJ ^ ρ) *
                  xi R α₀ ^ (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1))
                = xi R α₀ ^ (ledger t s' + ρ * (2 * t + 1) +
                    (ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1))) *
                  ((((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') * cJ ^ ρ) := by
                    rw [pow_add, pow_add]
                    ring
              _ = xi R α₀ ^ ledger (t + 1) s *
                  ((((hasseDeriv (ρ + r) R).eval (jet R α₀ t)).coeff s') * cJ ^ ρ) := by
                    rw [hexact]
          · rw [if_neg hcond, if_neg hcond]
            simp
        · refine SS.sum _ _ fun ρ _ => ?_
          by_cases hcond : (t + 1) * ρ ≤ s
          · rw [if_pos hcond]
            set s' := s - (t + 1) * ρ with hs'def
            have hslack := ledger_slack t s' ρ
            have hsum : s' + (t + 1) * ρ = s := by
              rw [hs'def]
              generalize (t + 1) * ρ = v at hcond ⊢
              omega
            rw [hsum] at hslack
            set σ := ledger (t + 1) s - ledger t s' - ρ * (2 * t + 1) with hσdef
            have hexact : ledger t s' + ρ * (2 * t + 1) + σ =
                ledger (t + 1) s := by
              rw [hσdef]
              generalize ρ * (2 * t + 1) = w at hslack ⊢
              omega
            refine SS.mono (SS.nsmul (SS.mul (SS.mul (hGsize (ρ + r) s')
              (SS.pow hGhatSize ρ)) (SS.pow hmξ σ)) _) ?_
            have hb := hbase_mono r ρ
            have hξ := Nat.mul_le_mul_left σ hmξslope
            calc
              (base (ρ + r) + slope * ledger t s') +
                    ρ * (slope * (2 * t + 1)) + σ * mξ
                  ≤ (base r + slope * ledger t s') +
                    ρ * (slope * (2 * t + 1)) + σ * slope := by omega
              _ = base r + slope *
                    (ledger t s' + ρ * (2 * t + 1) + σ) := by ring
              _ = base r + slope * ledger (t + 1) s := by rw [hexact]
          · rw [if_neg hcond]
            exact SS.zero _

include hR hd hmξ hξint hξ0 in
/-- The refined numerator bound for the `(t+1)`-st Newton coefficient. -/
theorem jet_coeff_integral_refined (base : ℕ → ℕ) (slope : ℕ)
    (hbase : ∀ r s, ∃ g : A,
      algebraMap A K g = ((hasseDeriv r R).eval (C α₀)).coeff s ∧ SS.P g (base r))
    (hbase_mono : ∀ r ρ, base (ρ + r) ≤ base r)
    (hbase0 : base 0 ≤ slope) (hmξslope : mξ ≤ slope) (t : ℕ) :
    ∃ g : A,
      algebraMap A K g =
        xi R α₀ ^ (2 * t + 1) * ((jet R α₀ (t + 1)).coeff (t + 1)) ∧
      SS.P g (slope * (2 * t + 1)) := by
  obtain ⟨g, hg, hgs⟩ := jet_ledger_refined SS R R₀ α₀ ξ₀ d mξ hR hd hmξ hξint hξ0
    base slope hbase hbase_mono hbase0 hmξslope t 0 (t + 1)
  rw [ledger_self_succ, hasseDeriv_zero'] at hg
  rw [ledger_self_succ] at hgs
  refine ⟨-g, ?_, ?_⟩
  · rw [map_neg, hg, jet_coeff_succ_self, pow_succ]
    field_simp
  · exact SS.neg (SS.mono hgs (by nlinarith [hbase0]))

/-- Jet coefficients are stable: `(Γ_T).coeff t` does not depend on `T` once `T ≥ t`. -/
theorem jet_coeff_stable (t : ℕ) : ∀ T, t ≤ T → (jet R α₀ T).coeff t = (jet R α₀ t).coeff t := by
  intro T
  induction T with
  | zero =>
      intro h
      have ht0 : t = 0 := by omega
      subst ht0
      rfl
  | succ T ihT =>
      intro h
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · rfl
      · rw [jet_succ, coeff_sub, coeff_mul_X_pow']
        rw [if_neg (by (clear * - hlt; omega))]
        rw [sub_zero]
        exact ihT (by (clear * - hlt; omega))

end Ledger

end JBAgreement
end
-- ===== end of `LvmJBJetLedger` =====

-- ===== merged from `LvmJBJet` (GOLF module merge: `LvmJBJet.lean` is now a stub importing `LvmJBClearedJet`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBJet.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# §1: stop the Hensel lift after `r + 1` coefficients

BCIKS construct the infinite Hensel series `γ = ∑_{t ≥ 0} α_t U^t` and devote their
Step 6 to proving `α_t = 0` for `t > r`.  That step is what drags the `X`-degree `D_X`
of the interpolant into the branch threshold, and it is the source of the extra factor
of `η`.

The finite-jet argument never forms the series.  It keeps only the `r`-jet

  `Γ_k(X) = ∑_{t = 0}^{r} α_t U^t`,   `U = X - x₀`,

and observes that this is already everything the affine-gluing argument needs.  The
justification is *finite Hensel uniqueness*, which this file proves in the two forms it
is used.

## Main results

* `eq_of_sub_isNilpotent_of_isUnit_derivative` — uniqueness of a root lifting a simple
  root modulo a nilpotent ideal.  Working modulo `U ^ (r+1)` makes `U` nilpotent, so
  this is exactly the statement that the truncated implicit-function recursion has a
  unique solution.  It holds over an arbitrary commutative ring, so no function field,
  valuation, or power series ring is required.

* `eq_of_sub_dvd_of_degree_le` — two polynomials of degree at most `r` that agree
  modulo `U ^ (r+1)` are equal.  This is the step "both sides have degree at most `r`,
  so `π_z(Γ_k) = p_z` as polynomials".

Together these give the conclusion of §1: the specialised jet *is* the proximate, with
no infinite series and no Step 6.
-/

namespace JBAgreement

open Polynomial

/-! ### Finite Hensel uniqueness -/

/-! ### Degree truncation -/

/-- **Two `r`-jets that agree are equal.**

If `p` and `q` both have degree at most `r` and agree modulo `(X - x₀) ^ (r+1)`, they
are equal.  This is the second half of §1: the specialised jet `π_z(Γ_k)` and the
proximate `p_z` agree to order `r + 1` and both have degree at most `r`, hence coincide
as polynomials. -/
theorem eq_of_sub_dvd_of_degree_le {F : Type*} [Field F] {p q : F[X]} {r : ℕ} {x₀ : F}
    (hp : p.degree ≤ (r : ℕ)) (hq : q.degree ≤ (r : ℕ))
    (hdvd : (X - C x₀) ^ (r + 1) ∣ (p - q)) : p = q := by
  rw [← not_ne_iff]
  intro hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : ((X - C x₀) ^ (r + 1)).degree ≤ (p - q).degree :=
    degree_le_of_dvd hdvd hsub
  have hpow : ((X - C x₀) ^ (r + 1)).degree = ((r + 1 : ℕ) : WithBot ℕ) := by
    simp [degree_pow, degree_X_sub_C]
  have hle : (p - q).degree ≤ ((r : ℕ) : WithBot ℕ) :=
    le_trans (degree_sub_le p q) (max_le hp hq)
  rw [hpow] at hdeg
  have hfin : ((r + 1 : ℕ) : WithBot ℕ) ≤ ((r : ℕ) : WithBot ℕ) := le_trans hdeg hle
  rw [Nat.cast_le] at hfin
  omega

/-! ### Interpolation: pinning the jet down from `r + 1` coordinates

This is the last step of §3.  The incidence count produces `r + 1` coordinates on which
the jet `Γ_k` agrees with `v₀ + Z v₁`; both sides have `X`-degree at most `r`, so they
agree identically. -/

/-- Two polynomials of degree at most `r` agreeing at `r + 1` distinct points are equal. -/
theorem eq_of_eval_eq_of_degree_le {F : Type*} [Field F] [DecidableEq F] {p q : F[X]}
    {r : ℕ} (hp : p.degree ≤ (r : ℕ)) (hq : q.degree ≤ (r : ℕ))
    (T : Finset F) (hT : r + 1 ≤ T.card)
    (heval : ∀ x ∈ T, p.eval x = q.eval x) : p = q := by
  rw [← not_ne_iff]
  intro hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  -- `T` consists of roots of `p - q`.
  have hTroots : T ⊆ (p - q).roots.toFinset := by
    intro x hx
    have : (p - q).eval x = 0 := by
      simp [eval_sub, heval x hx]
    simpa [Multiset.mem_toFinset, mem_roots, hsub] using this
  have hnatdeg : (p - q).natDegree ≤ r := by
    have hle : (p - q).degree ≤ ((r : ℕ) : WithBot ℕ) :=
      le_trans (degree_sub_le p q) (max_le hp hq)
    exact natDegree_le_iff_degree_le.mpr hle
  have hcard : T.card ≤ r :=
    le_trans (le_trans (Finset.card_le_card hTroots) (p - q).roots.toFinset_card_le)
      (le_trans (card_roots' (p - q)) hnatdeg)
  omega

/-! ### The Newton step

Existence of the jet is a Newton iteration.  Because we only ever work modulo
`U ^ (r+1)`, the ideal is nilpotent and the iteration terminates after finitely many
steps — there is no completeness or power-series input.  This is the "finite recursion"
of §1, in the form that works in every characteristic. -/

end JBAgreement
end
-- ===== end of `LvmJBJet` =====

-- ===== merged from `LvmJBIntegral` (GOLF module merge: `LvmJBIntegral.lean` is now a stub importing `LvmJBClearedJet`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBIntegral.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Integral models: naturality, homogeneous evaluation, and uniqueness in `F[U]`

The finite-jet argument runs the recursion *generically*, over `K = Frac(F[Z][T])`, and
then reads off the answer at each branch point `(z, t_z)`.  Passing from the generic
statement to the specialised one is the only place where the two worlds meet, and this
file supplies the three tools that make the passage a formality.

## 1. Naturality

`xi` and `jetConst` are defined over an arbitrary commutative ring, and commute with any
coefficient homomorphism (`xi_map`, `jetConst_map`).  So the generic `ξ` and the
specialised `ξ(z, t_z)` are literally the same construction applied to two different
homomorphisms out of `A = F[Z][T]`, and no compatibility hypothesis has to be carried.

## 2. Homogeneous evaluation

Denominators are the obstacle: the generic jet lives over `K`, not over `A`, so it
cannot be pushed through a homomorphism `A → F` directly.  The fix is to clear them once
and for all.  For `P` of `Y`-degree at most `d`,

  `evalH P d c γ̂ = ∑_{j ≤ d} P_j · γ̂ʲ · c^(d-j)`

is the *homogenised* evaluation, a polynomial expression in the coefficients of `P`, in
`γ̂` and in `c`.  It is therefore natural in the coefficient ring (`evalH_map`), and it
computes the honest evaluation whenever the denominators can be divided out:

  `evalH P d c (C c * γ) = C (c ^ d) · P.eval γ`   (`evalH_C_mul`).

Reading the first identity forwards over `K` and backwards over `F` is exactly the
transfer we need — and it never mentions localisation, completions, or valuations.

## 3. Uniqueness modulo `U^{r+1}`

`eq_of_dvd_eval` is finite Hensel uniqueness in the only form the endgame needs, stated
directly in `F[U]`: two polynomials of degree at most `r`, with the same constant term,
both annihilating `R` modulo `U^{r+1}`, coincide as soon as `∂_Y R` is nonzero at the
base point.  Instead of a nilpotent-ideal argument it uses that `U` is prime in `F[U]`:
the difference `δ` satisfies `U^{r+1} ∣ δ · v` with `v(0) ≠ 0`, so `U^{r+1} ∣ δ`, so
`δ = 0` by degree.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### Naturality of the structural constants -/

section Naturality

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Hasse derivatives commute with coefficient homomorphisms. -/
theorem hasseDeriv_map (φ : A →+* B) (P : A[X]) (n : ℕ) :
    (hasseDeriv n P).map φ = hasseDeriv n (P.map φ) := by
  apply Polynomial.ext
  intro i
  rw [coeff_map, hasseDeriv_coeff, hasseDeriv_coeff, coeff_map, map_mul, map_natCast]

/-- Taking the `U = 0` slice commutes with coefficient homomorphisms. -/
theorem map_evalRingHom_zero_comm (φ : A →+* B) (P : A[X][X]) :
    (P.map (mapRingHom φ)).map (evalRingHom 0) = (P.map (evalRingHom 0)).map φ := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro p
  simp

/-- **Naturality of `ξ`.**  The simple-root value of a specialised branch is the
specialisation of the generic simple-root value. -/
theorem xi_map (φ : A →+* B) (P : A[X][X]) (a : A) :
    xi (P.map (mapRingHom φ)) (φ a) = φ (xi P a) := by
  unfold xi
  rw [← hasseDeriv_map, map_evalRingHom_zero_comm, eval_map, eval₂_hom]

/-- **Naturality of the obstruction constant.** -/
theorem jetConst_map (φ : A →+* B) (P : A[X][X]) (a : A) :
    jetConst (P.map (mapRingHom φ)) (φ a) = φ (jetConst P a) := by
  unfold jetConst
  rw [map_evalRingHom_zero_comm, eval_map, eval₂_hom]

end Naturality

/-! ### Homogeneous evaluation -/

section EvalH

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The *homogenised* evaluation of `P` (of `Y`-degree at most `d`) at the "numerator"
`γ̂` over the "denominator" `c`:

  `evalH P d c γ̂ = ∑_{j ≤ d} P_j · γ̂ ^ j · c ^ (d - j)`.

Being a polynomial expression in the data, it survives every ring homomorphism; and when
`γ̂ = c · γ` it equals `c ^ d · P(γ)`. -/
noncomputable def evalH (P : A[X][X]) (d : ℕ) (c : A) (γ : A[X]) : A[X] :=
  ∑ j ∈ range (d + 1), P.coeff j * γ ^ j * C (c ^ (d - j))

/-- **Naturality of the homogenised evaluation.** -/
theorem evalH_map (φ : A →+* B) (P : A[X][X]) (d : ℕ) (c : A) (γ : A[X]) :
    evalH (P.map (mapRingHom φ)) d (φ c) (γ.map φ) = (evalH P d c γ).map φ := by
  unfold evalH
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, map_C, ← map_pow,
    coeff_map]
  rfl

/-- **Homogenised evaluation computes the honest one.**  This is the bridge used twice:
forwards over `K` (where `γ̂` is the cleared generic jet) and backwards over `F` (where
dividing by `c ^ d ≠ 0` recovers the specialised jet). -/
theorem evalH_C_mul (P : A[X][X]) {d : ℕ} (hd : P.natDegree ≤ d) (c : A) (γ : A[X]) :
    evalH P d c (C c * γ) = C (c ^ d) * P.eval γ := by
  unfold evalH
  rw [eval_eq_sum_range' (n := d + 1) (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
  have hsplit : c ^ d = c ^ j * c ^ (d - j) := by
    rw [← pow_add]; congr 1; omega
  rw [mul_pow, ← C_pow, hsplit, C_mul]
  ring

end EvalH

/-! ### Finite Hensel uniqueness in `F[U]` -/

section Uniqueness

variable {F : Type*} [Field F]

/-- A polynomial with nonzero constant term is coprime to `X ^ n`. -/
theorem isCoprime_X_pow_of_coeff_zero_ne_zero {v : F[X]} (hv : v.coeff 0 ≠ 0) (n : ℕ) :
    IsCoprime ((X : F[X]) ^ n) v :=
  IsCoprime.pow_left ((Polynomial.irreducible_X).coprime_iff_not_dvd.mpr
    (fun h => hv (Polynomial.X_dvd_iff.mp h)))

/-- **Finite Hensel uniqueness, in the form used by the endgame.**

If `γ` and `π` both have degree at most `r`, share their constant term, both annihilate
`R` modulo `U ^ (r+1)`, and `∂_Y R` evaluated at `π` has nonzero constant term, then
`γ = π`.

The proof is the Taylor expansion `R(γ) - R(π) = δ · (∂_Y R(π) + c δ)` together with the
primality of `U`: the second factor has nonzero constant term, so all of `U ^ (r+1)`
must divide `δ`, which has degree at most `r`. -/
theorem eq_of_dvd_eval (R : F[X][X]) {γ π : F[X]} {r : ℕ}
    (hγ : γ.natDegree ≤ r) (hπ : π.natDegree ≤ r)
    (hconst : γ.coeff 0 = π.coeff 0)
    (hRγ : (X : F[X]) ^ (r + 1) ∣ R.eval γ)
    (hRπ : (X : F[X]) ^ (r + 1) ∣ R.eval π)
    (hunit : ((hasseDeriv 1 R).eval π).coeff 0 ≠ 0) :
    γ = π := by
  set δ : F[X] := γ - π with hδdef
  obtain ⟨c, hc⟩ := R.binomExpansion π δ
  have hπδ : π + δ = γ := by rw [hδdef]; ring
  rw [hπδ] at hc
  -- `R(γ) - R(π) = δ * v` with `v = ∂_Y R(π) + c δ`.
  set v : F[X] := (hasseDeriv 1 R).eval π + c * δ with hvdef
  have hfac : R.eval γ - R.eval π = δ * v := by
    rw [hc, hvdef, hasseDeriv_one]
    ring
  -- `δ` has zero constant term, so `v` has nonzero constant term.
  have hδ0 : δ.coeff 0 = 0 := by rw [hδdef, coeff_sub, hconst, sub_self]
  have hv0 : v.coeff 0 ≠ 0 := by
    rw [hvdef, coeff_add, mul_coeff_zero, hδ0, mul_zero, add_zero]
    exact hunit
  -- Divide out the coprime factor.
  have hdvd : (X : F[X]) ^ (r + 1) ∣ δ * v := by
    rw [← hfac]; exact dvd_sub hRγ hRπ
  have hδdvd : (X : F[X]) ^ (r + 1) ∣ δ :=
    (isCoprime_X_pow_of_coeff_zero_ne_zero hv0 (r + 1)).dvd_of_dvd_mul_right hdvd
  -- Degree forces `δ = 0`.
  refine eq_of_sub_dvd_of_degree_le (x₀ := (0 : F)) (r := r) ?_ ?_ ?_
  · exact natDegree_le_iff_degree_le.mp hγ
  · exact natDegree_le_iff_degree_le.mp hπ
  · simpa using hδdvd

end Uniqueness

end JBAgreement
end
-- ===== end of `LvmJBIntegral` =====

/-!
# The cleared jet, and the passage from generic to specialised

The jet `Γ_r` of §1 lives over the fraction field `K = Frac A`; the counting argument of
§3 needs a polynomial over `A` itself.  Multiplying through by `ξ^(2r+1)` — the largest
denominator the ledger ever produces — turns it into one:

  `γ̂ = ξ^(2r+1) · Γ_r ∈ A[U]`,

with coefficients of size `O(r)` by `jet_coeff_integral`.  That is `exists_clearedJet`.

The point of clearing is that `γ̂` and the *homogenised* evaluation `evalH` are algebraic
over `A`, so both survive an arbitrary specialisation `A → F`, whereas `Γ_k` does not.
The generic jet property `U^{r+1} ∣ R(Γ_r) - r₀` therefore becomes an identity in `A[U]`

  `U^{r+1} ∣ evalH R₀ d (ξ^(2r+1)) γ̂ - C (ξ^((2r+1)d) · H₀)`,

which is the last statement of `exists_clearedJet`, and which specialises for free.

`clearedJet_spec` then closes the loop: at a branch point — a pair `(z, t_z)` with
`H₀(z, t_z) = 0` and `ξ(z, t_z) ≠ 0` — the specialised cleared jet, divided by the now
invertible `ξ(z, t_z)^(2r+1)`, *is* the proximate `p_z`.  This is §1's conclusion, and
the proof is `eq_of_dvd_eval`: both are degree-`r` roots of the specialised branch modulo
`U^{r+1}` with the same constant term.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### Existence of the cleared jet -/

section Cleared

variable {A : Type*} [CommRing A] [IsDomain A]

end Cleared

/-! ### Specialisation: the cleared jet at a branch point is the proximate -/

section Spec

variable {A : Type*} [CommRing A] {F : Type*} [Field F]

/-- **The specialised jet is the proximate (§1, conclusion).**

Let `φ : A → F` be a specialisation, `γ` the cleared jet, and suppose

* `φ` kills the obstruction: `φ (jetConst R₀ a₀) = 0` — i.e. `(z, t_z)` is a branch point;
* `φ ξ ≠ 0` — the branch is unramified there (the good slice `x₀`);
* `π` is a polynomial of degree at most `r` lying on the specialised branch,
  `R₀^φ (π) = 0`, with `π(0) = φ a₀`.

Then `π` is determined: `C (φ ξ ^ (2r+1)) * π = γ^φ`.

This is what makes the counting of §3 about the *proximates*: a coefficient identity for
`γ` over `A` is, at every branch point, a statement about `p_z`. -/
theorem clearedJet_spec_exp (R₀ : A[X][X]) (a₀ : A) (d r E : ℕ) (hd : R₀.natDegree ≤ d)
    (γ : A[X]) (hγdeg : γ.natDegree ≤ r)
    (hγ0 : γ.coeff 0 = xi R₀ a₀ ^ E * a₀)
    (hγjet : (X : A[X]) ^ (r + 1) ∣
      evalH R₀ d (xi R₀ a₀ ^ E) γ
        - C (xi R₀ a₀ ^ (E * d) * jetConst R₀ a₀))
    (φ : A →+* F) (hφH : φ (jetConst R₀ a₀) = 0) (hφξ : φ (xi R₀ a₀) ≠ 0)
    (π : F[X]) (hπdeg : π.natDegree ≤ r) (hπ0 : π.coeff 0 = φ a₀)
    (hπroot : (R₀.map (mapRingHom φ)).eval π = 0) :
    C (φ (xi R₀ a₀) ^ E) * π = γ.map φ := by
  set Rf : F[X][X] := R₀.map (mapRingHom φ) with hRf
  set c : F := φ (xi R₀ a₀) ^ E with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ hφξ
  set γ' : F[X] := γ.map φ with hγ'
  -- The specialised cleared jet, with the denominator divided out.
  set δ : F[X] := C c⁻¹ * γ' with hδ
  have hγ'δ : γ' = C c * δ := by
    rw [hδ, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]
  -- The jet property specialises.
  have hspec : (X : F[X]) ^ (r + 1) ∣ evalH Rf d c γ' := by
    have hmap := Polynomial.map_dvd φ hγjet
    rw [Polynomial.map_sub, ← evalH_map φ R₀ d _ γ, map_C, map_mul, map_pow, hφH,
      mul_zero, map_zero, sub_zero, ← hRf] at hmap
    simpa [hc] using hmap
  -- Divide out `c ^ d`.
  have hRfd : Rf.natDegree ≤ d := le_trans natDegree_map_le hd
  have hδroot : (X : F[X]) ^ (r + 1) ∣ Rf.eval δ := by
    rw [hγ'δ, evalH_C_mul Rf hRfd] at hspec
    have hcop : IsCoprime ((X : F[X]) ^ (r + 1)) (C (c ^ d)) := by
      refine isCoprime_X_pow_of_coeff_zero_ne_zero ?_ _
      rw [coeff_C_zero]
      exact pow_ne_zero d hc0
    exact hcop.dvd_of_dvd_mul_left hspec
  -- `π` and `δ` agree.
  have hδdeg : δ.natDegree ≤ r :=
    le_trans (natDegree_C_mul_le _ _) (le_trans natDegree_map_le hγdeg)
  have hδ0 : δ.coeff 0 = π.coeff 0 := by
    rw [hδ, coeff_C_mul, hγ', coeff_map, hγ0, map_mul, map_pow, ← hc, ← mul_assoc,
      inv_mul_cancel₀ hc0, one_mul, hπ0]
  have hπdvd : (X : F[X]) ^ (r + 1) ∣ Rf.eval π := by rw [hπroot]; exact dvd_zero _
  have hunit : ((hasseDeriv 1 Rf).eval π).coeff 0 ≠ 0 := by
    rw [coeff_zero_eval, hπ0, ← xi, hRf, xi_map φ R₀ a₀]
    exact hφξ
  have := eq_of_dvd_eval Rf hδdeg hπdeg hδ0 hδroot hπdvd hunit
  rw [hγ'δ, ← this, hδ]

end Spec

end JBAgreement
