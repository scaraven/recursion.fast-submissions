-- New for lvm6 (WP W1). The final level's tail sumcheck (FORMAT6 v2.2.1 §6.6, `i = 4`: three plain
-- rounds `R(2, 2)`, each `E(2)` then `G(2)`) and its terminal check, over any field with the group
-- rule of `ChalIface`, after leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Tail.lean`
-- (`TailInv`, `card_tailBad_le`, `tailSpec`, `tailDone_ne`) @ fdb317982 and season 1's
-- `LvmWhirLevelFinal` (its `tailSpec`). The claim is `Σ_{x ∈ {0,1}^n} Φ(τ ++ x)·M(τ ++ x) = c` for
-- functions `Φ`, `M` affine in each remaining variable; a round's polynomial is `c₀ + c₁X + c₂X²`
-- with `c₁ = c − 2c₀ − c₂` (in characteristic 2: FORMAT6's `c₁ = claim + c₂`).
import Lvm6WhirRound

/-!
# The tail sumcheck (W1)

* `cubeSum n f`: the sum of `f` over `{0,1}^n` (first variable first). `MA n f`: `f` is affine in
  each of its first `n` arguments.
* `sumP I g Φ M n τ c`: `n` rounds (two reads, one `g`-bit value `r`, the claim `s(r)`), then the
  terminal check `Φ(τ) M(τ) = c`.
* `card_sumBad_le`: a round with a false claim keeps it false except at `≤ 2` values.
* **`sumSpec`**: from `cubeSum n (Φ·M)(τ ++ ·) ≠ c` the program returns `false`; each round's group
  escapes within `eSum g = 2^-g · 2/|F|`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
  Polynomial
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Sums over the cube and multiaffinity -/

/-- The sum over `{0,1}^n`, first variable first. -/
def cubeSum : ℕ → (List F → F) → F
  | 0, f => f []
  | n + 1, f => cubeSum n (fun x ↦ f (0 :: x)) + cubeSum n (fun x ↦ f (1 :: x))

/-- `f` is affine in each of its first `n` arguments. -/
def MA : ℕ → (List F → F) → Prop
  | 0, _ => True
  | n + 1, f => (∀ X x, f (X :: x) = (1 - X) * f (0 :: x) + X * f (1 :: x)) ∧
      ∀ X, MA n fun x ↦ f (X :: x)

theorem cubeSum_add (n : ℕ) (f g : List F → F) :
    cubeSum n (fun x ↦ f x + g x) = cubeSum n f + cubeSum n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [cubeSum]
    rw [ih (fun x ↦ f (0 :: x)) (fun x ↦ g (0 :: x)), ih (fun x ↦ f (1 :: x)) (fun x ↦ g (1 :: x))]
    ring

/-- The cube sum of polynomials. -/
noncomputable def cubeSumP : ℕ → (List F → F[X]) → F[X]
  | 0, f => f []
  | n + 1, f => cubeSumP n (fun x ↦ f (0 :: x)) + cubeSumP n (fun x ↦ f (1 :: x))

theorem eval_cubeSumP (r : F) : ∀ (n : ℕ) (f : List F → F[X]),
    (cubeSumP n f).eval r = cubeSum n fun x ↦ (f x).eval r
  | 0, _ => rfl
  | n + 1, f => by
    simp only [cubeSumP, cubeSum, eval_add, eval_cubeSumP r n]

theorem natDegree_cubeSumP_le {d : ℕ} : ∀ (n : ℕ) (f : List F → F[X]),
    (∀ x, (f x).natDegree ≤ d) → (cubeSumP n f).natDegree ≤ d
  | 0, _, h => h []
  | n + 1, f, h => (natDegree_add_le _ _).trans (max_le (natDegree_cubeSumP_le n _ fun x ↦ h _)
      (natDegree_cubeSumP_le n _ fun x ↦ h _))

/-- The affine polynomial through `a` at `0` and `b` at `1`. -/
noncomputable def affP (a b : F) : F[X] := C a + X * C (b - a)

theorem eval_affP (a b r : F) : (affP a b).eval r = (1 - r) * a + r * b := by
  simp [affP]; ring

theorem natDegree_affP_le (a b : F) : (affP a b).natDegree ≤ 1 := by
  unfold affP
  refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
  refine natDegree_mul_le.trans ?_
  simp

/-! ## One round -/

/-- The prover's round polynomial `c₀ + c₁ X + c₂ X²` with `c₁ = c − 2c₀ − c₂`. -/
def roundPoly (c c₀ c₂ r : F) : F := c₀ + (c - 2 * c₀ - c₂) * r + c₂ * r ^ 2

noncomputable def roundPolyP (c c₀ c₂ : F) : F[X] := C c₀ + C (c - 2 * c₀ - c₂) * X + C c₂ * X ^ 2

theorem eval_roundPolyP (c c₀ c₂ r : F) : (roundPolyP c c₀ c₂).eval r = roundPoly c c₀ c₂ r := by
  simp [roundPolyP, roundPoly]

theorem natDegree_roundPolyP_le (c c₀ c₂ : F) : (roundPolyP c c₀ c₂).natDegree ≤ 2 := by
  unfold roundPolyP
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · simp
  · exact natDegree_C_mul_le _ _ |>.trans (by simp)
  · exact natDegree_C_mul_le _ _ |>.trans (by simp)

/-- The doom of the tail at prefix `τ` with `n` variables left. -/
def SumBad (Φ M : List F → F) (n : ℕ) (τ : List F) (c : F) : Prop :=
  cubeSum n (fun x ↦ Φ (τ ++ x) * M (τ ++ x)) ≠ c

open Classical in
/-- **A round's bad values**: at most two. -/
theorem card_sumBad_le {Φ M : List F → F} {n : ℕ} {τ : List F} {c : F}
    (hΦ : MA (n + 1) fun x ↦ Φ (τ ++ x)) (hM : MA (n + 1) fun x ↦ M (τ ++ x))
    (hb : SumBad Φ M (n + 1) τ c) (c₀ c₂ : F) :
    (univ.filter fun r ↦ ¬ SumBad Φ M n (τ ++ [r]) (roundPoly c c₀ c₂ r)).card ≤ 2 := by
  -- the true round polynomial
  let tP : F[X] := cubeSumP n fun x ↦ affP (Φ (τ ++ 0 :: x)) (Φ (τ ++ 1 :: x)) *
    affP (M (τ ++ 0 :: x)) (M (τ ++ 1 :: x))
  have ht : ∀ r, tP.eval r = cubeSum n (fun x ↦ Φ (τ ++ [r] ++ x) * M (τ ++ [r] ++ x)) := by
    intro r
    rw [eval_cubeSumP]
    congr 1
    funext x
    have h1 := hΦ.1 r x
    have h2 := hM.1 r x
    simp only at h1 h2
    rw [eval_mul, eval_affP, eval_affP, List.append_assoc, List.singleton_append, h1, h2]
  have hdeg : tP.natDegree ≤ 2 := natDegree_cubeSumP_le n _ fun x ↦ by
    have h1 := natDegree_affP_le (Φ (τ ++ 0 :: x)) (Φ (τ ++ 1 :: x))
    have h2 := natDegree_affP_le (M (τ ++ 0 :: x)) (M (τ ++ 1 :: x))
    exact natDegree_mul_le.trans (by omega)
  set D := roundPolyP c c₀ c₂ - tP
  have hD : D ≠ 0 := by
    intro h0
    have e0 := congrArg (eval 0) h0
    have e1 := congrArg (eval 1) h0
    simp only [D, eval_sub, eval_zero, sub_eq_zero, eval_roundPolyP, ht] at e0 e1
    apply hb
    show cubeSum n (fun x ↦ Φ (τ ++ 0 :: x) * M (τ ++ 0 :: x)) +
      cubeSum n (fun x ↦ Φ (τ ++ 1 :: x) * M (τ ++ 1 :: x)) = c
    have h0' : cubeSum n (fun x ↦ Φ (τ ++ 0 :: x) * M (τ ++ 0 :: x)) = roundPoly c c₀ c₂ 0 := by
      rw [e0]; simp only [List.append_assoc, List.singleton_append]
    have h1' : cubeSum n (fun x ↦ Φ (τ ++ 1 :: x) * M (τ ++ 1 :: x)) = roundPoly c c₀ c₂ 1 := by
      rw [e1]; simp only [List.append_assoc, List.singleton_append]
    rw [h0', h1']
    simp only [roundPoly]; ring
  have hsub : (univ.filter fun r ↦ ¬ SumBad Φ M n (τ ++ [r]) (roundPoly c c₀ c₂ r)) ⊆
      D.roots.toFinset := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SumBad, not_not] at hr
    rw [Multiset.mem_toFinset, mem_roots hD]
    show eval r (roundPolyP c c₀ c₂ - tP) = 0
    rw [eval_sub, eval_roundPolyP, ht, hr, sub_self]
  calc _ ≤ D.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ D.roots.card := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := card_roots' _
    _ ≤ 2 := (natDegree_sub_le _ _).trans (max_le (natDegree_roundPolyP_le c c₀ c₂) hdeg)

/-! ## The program and its specification -/

variable (I : ChalIface F)

/-- **The tail sumcheck**: `n` rounds, then the terminal check `Φ(τ) M(τ) = c`. -/
def sumP (g : ℕ) (Φ M : List F → F) : (n : ℕ) → List F → F → VerifierProgram Bool
  | 0, τ, c => pure (decide (Φ τ * M τ = c))
  | n + 1, τ, c => readF I >>= fun c₀ ↦ readF I >>= fun c₂ ↦ I.grp g 0 >>= fun v ↦
      sumP g Φ M n (τ ++ [v.getD 0 0]) (roundPoly c c₀ c₂ (v.getD 0 0))

/-- A tail round's escape: `2^-g · 2/|F|`. -/
noncomputable def eSum (F : Type) [Fintype F] (g : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ g * 2 / (Fintype.card F : ℝ≥0∞)

variable {εmax : ℝ≥0∞}

/-- **The tail sumcheck rejects a false claim** (leanVM `tailSpec` + `tailDone_ne`): from
`SumBad Φ M n τ c`, with `Φ`, `M` affine in each remaining variable, the program returns `false`;
each round's group escapes within `eSum g ≤ εmax`. -/
noncomputable def sumSpec (g : ℕ) (hg : g ≤ I.gmax) (he : eSum F g < 1) (heT : eSum F g ≤ εmax)
    (Φ M : List F → F) : (n : ℕ) → (τ : List F) → (c : F) →
      (MA n fun x ↦ Φ (τ ++ x)) → (MA n fun x ↦ M (τ ++ x)) →
      Spec (sumP I g Φ M n τ c) (fun _ ↦ SumBad Φ M n τ c) (fun b _ ↦ b = false) εmax 0 0
  | 0, τ, c, _, _ =>
    (Spec.ret (Post := fun b (_ : List Ev) ↦ b = false) (decide (Φ τ * M τ = c))).mono
      (fun _ hb ↦ by simp only [SumBad, cubeSum, List.append_nil] at hb; simp [hb])
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1, τ, c, hΦ, hM => by
    classical
    have h0 : (0 : ℝ≥0∞) ≤ εmax := by positivity
    refine ((readFSpec I (Inv := fun _ ↦ SumBad Φ M (n + 1) τ c) h0).mono (fun _ h ↦ h)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c₀ ↦ ?_
    refine ((readFSpec I (Inv := fun _ ↦ SumBad Φ M (n + 1) τ c) h0).mono (fun _ h ↦ h)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c₂ ↦ ?_
    refine ((I.grpSpec g 0 hg (fun _ ↦ SumBad Φ M (n + 1) τ c)
      (fun u _ ↦ SumBad Φ M n (τ ++ [u 0]) (roundPoly c c₀ c₂ (u 0))) (eSum F g) he
      fun _ hb ↦ ?_).mono (fun _ h ↦ h) (fun _ _ h ↦ h) heT le_rfl le_rfl).bind' fun v ↦ ?_
    · unfold grpE eSum
      have hq : (Fintype.card F : ℝ≥0∞) ^ (0 + 1) = Fintype.card F := by simp
      rw [hq]
      gcongr
      have hc := card_sumBad_le hΦ hM hb c₀ c₂
      refine le_trans (Nat.cast_le.mpr (Finset.card_le_card_of_injOn (fun u ↦ u 0)
        (t := univ.filter fun r ↦ ¬ SumBad Φ M n (τ ++ [r]) (roundPoly c c₀ c₂ r))
        (fun u hu ↦ ?_) (fun u _ u' _ h ↦ funext fun i ↦ by fin_cases i; exact h))) ?_
      · simpa using hu
      · exact_mod_cast hc
    · exact (sumSpec g hg he heT Φ M n (τ ++ [v.getD 0 0]) _
        (by simpa [List.append_assoc] using hΦ.2 (v.getD 0 0))
        (by simpa [List.append_assoc] using hM.2 (v.getD 0 0))).mono
        (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm6.Whir
