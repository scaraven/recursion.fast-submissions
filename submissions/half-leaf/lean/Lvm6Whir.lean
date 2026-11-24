-- New for lvm6 (WP W1, first slice). One WHIR level with a next one as a specification of the
-- verifier language: the level's fold rounds (`Lvm6WhirRound.roundsSpecJ`) then its interface
-- (`Lvm6WhirLevel.tailSpec`), after leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Spec.lean`
-- `levelsSpec` (its `level :: next :: rest` case, one step) @ fdb317982.
import Lvm6WhirLevel

/-!
# One level of the affine WHIR opening (W1, first slice)

`levelP I L g gO gQ ht wd i ℓ vals`: `ℓ` fold rounds (`g`-bit pairs), then the next commitment, the
high part, the OOD group (`gO` bits), its value, the query message (`gQ` bits) and the openings of
commitment `i`. **`levelSpec`**: from the descent invariant for the level's word at `a`, the program
returns `(rounds, interface)` with the descent invariant for the next word at `A'`: the word folded
by the rounds, the weight folded and glued, the claim folded and glued, and the predicate pulled
back through the rounds and handed over by `nextB`. Every group escapes within `εmax`: the fold
pairs `eRound g (par s)`, the OOD point `eOod`, the query message `eQry`. Lead `0`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
  LeanVM.Protocol.Whir.AffineCombiner
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] (I : ChalIface F) {n n' m' : ℕ}
  (L : TailIface F n n' m')

/-- **One WHIR level with a next one**: its `ℓ` fold rounds, then its interface. -/
def levelP (g gO gQ ht wd i ℓ : ℕ)
    (vals : List (Rnd F) → List F → (Fin L.t → Fin n) → List (List K) → Fin L.t → F) :
    VerifierProgram (List (Rnd F) × TailOut F L.ko L.t n) :=
  roundsP I g ℓ >>= fun rs ↦ tailP L I ht wd i gO gQ (vals rs) >>= fun o ↦ pure (rs, o)

/-- The doom after the level: the next level's descent invariant. -/
def levelPost (par : ℕ → RoundPar) (ℓ t : ℕ) (Qf : List (ℕ × ℕ × Word) → Wd F n (0 + ℓ))
    (W : Tup F (0 + ℓ) →ₗ[F] F) (σ : F) (a A' : ℕ)
    (B : List (ℕ × ℕ × Word) → Tup F (0 + ℓ) → Prop) (nxt : List (ℕ × ℕ × Word) → Wd F n' m')
    (ro : List (Rnd F) × TailOut F L.ko L.t n) (cs : List (ℕ × ℕ × Word)) : Prop :=
  tailPost L (fun cs ↦ foldsQ L.dom ℓ ro.1 (Qf cs)) nxt (foldsW ℓ ro.1 W) (foldsC ℓ ro.1 σ)
    (aOut (fun s ↦ (par s).A) a t ℓ) A'
    (fun cs ↦ pulls L.dom (fun s ↦ (par s).A) L.d t ℓ ro.1 (Qf cs) (B cs)) ro.2 cs

variable {εmax : ℝ≥0∞}

/-- **One level of the affine WHIR opening, with the descent invariant** (BLUEPRINT T3, W1's
first slice): the level's fold rounds (round `s` at `par s`, chained thresholds, from `a` at round
`t`) and its interface (`tailSpec`), every group within `εmax`. -/
noncomputable def levelSpec (g gO gQ ht wd i ℓ t : ℕ) (hg : g ≤ I.gmax) (hgO : gO ≤ I.gmax)
    (hgQ : gQ ≤ I.gmax) (par : ℕ → RoundPar)
    (hpar : ∀ s, t ≤ s → s < t + ℓ → RoundOK (Fintype.card F) n L.d (par s))
    (he : ∀ s, t ≤ s → s < t + ℓ → eRound F g (par s) < 1)
    (heT : ∀ s, t ≤ s → s < t + ℓ → eRound F g (par s) ≤ εmax)
    (hchain : ∀ s, t ≤ s → s + 1 < t + ℓ → (par s).A ≤ (par (s + 1)).A - 1)
    (Qf : List (ℕ × ℕ × Word) → Wd F n (0 + ℓ)) (W : Tup F (0 + ℓ) →ₗ[F] F) (σ : F) (a : ℕ)
    (ha : 0 < ℓ → a ≤ (par t).A - 1) (B : List (ℕ × ℕ × Word) → Tup F (0 + ℓ) → Prop)
    (vals : List (Rnd F) → List F → (Fin L.t → Fin n) → List (List K) → Fin L.t → F)
    (Rd : List (ℕ × ℕ × Word) → Prop) (nxt : List (ℕ × ℕ × Word) → Wd F n' m') (A' : ℕ)
    (hWH : ∀ rs hi, foldsW ℓ rs W (L.hp hi) = 0)
    (hstab : ∀ cs c, cs.length = i + 1 → Rd cs →
      Qf (cs ++ [c]) = Qf cs ∧ B (cs ++ [c]) = B cs ∧ Rd (cs ++ [c]))
    (hread : ∀ rs h, (commits h).length = i + 2 → Rd (commits h) → ∀ ps rows,
      answer h i (List.ofFn fun k ↦ (ps k : ℕ)) = some rows → ∀ hi,
        vals rs hi ps rows = fun k ↦ foldsQ L.dom ℓ rs (Qf (commits h)) lane0 (ps k) -
          (L.hp hi lane0).eval (L.dom (ps k)))
    (hgap : n' * L.d' < A' * A')
    (heO : eOod L gO (jl n' A' L.d') < 1) (heOT : eOod L gO (jl n' A' L.d') ≤ εmax)
    (heQ : eQry L gQ (jl n' A' L.d') (aOut (fun s ↦ (par s).A) a t ℓ) < 1)
    (heQT : eQry L gQ (jl n' A' L.d') (aOut (fun s ↦ (par s).A) a t ℓ) ≤ εmax) :
    Spec (levelP I L g gO gQ ht wd i ℓ vals)
      (fun h ↦ (commits h).length = i + 1 ∧ Rd (commits h) ∧
        TViol L.dom (Qf (commits h)) W σ a L.d (B (commits h)))
      (fun ro h ↦ levelPost L par ℓ t Qf W σ a A' B nxt ro (commits h)) εmax 0 0 :=
  ((roundsSpecJ I L.dom (fun cs ↦ cs.length = i + 1 ∧ Rd cs) g hg par ℓ t hpar he heT hchain Qf W σ
      a ha B).mono (fun _ h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind'
    fun rs ↦ ((tailSpec L I ht wd i gO gQ hgO hgQ (vals rs) Rd (fun cs ↦ foldsQ L.dom ℓ rs (Qf cs))
        nxt (foldsW ℓ rs W) (hWH rs) (foldsC ℓ rs σ) (aOut (fun s ↦ (par s).A) a t ℓ) A'
        (fun cs ↦ pulls L.dom (fun s ↦ (par s).A) L.d t ℓ rs (Qf cs) (B cs))
        (fun cs c hl hR ↦ by
          obtain ⟨hQ, hB, hR'⟩ := hstab cs c hl hR
          exact ⟨by rw [hQ], by rw [hQ, hB], hR'⟩)
        (hread rs) hgap heO heOT heQ heQT).mono (fun _ h ↦ ⟨h.1.1, h.1.2, h.2⟩) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl).bind' fun o ↦
      Spec.ret (Post := fun ro h ↦ levelPost L par ℓ t Qf W σ a A' B nxt ro (commits h)) (rs, o)

/-- **Non-vacuity of the round hypotheses**: PARAM's level-0 round 1 at `M = 24` (`κ = 18`, `R = 2`, six
folds, `A_end = 526,656`, witness `(110, 9008, 526,635)`, fold grind 10) meets `RoundOK` at
`|E2| = 2^128` with numerator `foldBudget 10 · 2^128`, i.e. `eRound = 7·2^-131 = εI`. -/
theorem roundOK_L0R1 : RoundOK (2 ^ 128) (roundN 18 2) (roundD 18 6)
    ⟨roundA 6 526656 1, 110, 9008, 526635, Lvm6.Params.foldBudget 10 * 2 ^ 128⟩ :=
  roundOK_of_foldRoundOK (by decide +kernel)

end Lvm6.Whir
