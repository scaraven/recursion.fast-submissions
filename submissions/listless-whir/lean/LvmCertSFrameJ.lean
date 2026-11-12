-- New for lvm2 (J2C-B, J2′): frame rules for the INV certificate's openings (J2C-DES §3 T3). Statements written at
-- G0 by the lead; the proofs are J2C-B's.
import LvmCertSFrame

/-!
# Frame rules for J2′'s openings (J2C-DES §3, T3)

* **`Spec.traced`**: `Spec.frame` with the run recorded in the post: a predicate `J` of the start, and the
  completed run `l` from it (`p.after l = ret a`). J2C-DES §4 note 4: used three times (the roots from `· = []`,
  `mid`, `C_rec`'s prefix) to get `(recPrefixProg mid x).after h₁ = ret (cl, a)`.
* **`Spec.orPost`**: `Spec.orStableRet` for a sub-program with a postcondition (`PostA ∨ M'`).
* **`Spec.liftT`**: a specification that never returns (post `False`) at follower's allowance `0` holds at any
  allowance `T` (J2C-DES §4 note 2: `finSuffixSpecR` has `T = 0`; `orStable` needs the follower's lead).
-/

set_option autoImplicit false

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

section

variable {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop}
  {εmax L T : ENNReal}

namespace Spec

open Classical in
/-- **The frame rule with the run recorded** (J2C-DES T3): from `Pre ∧ J`, the post adds that the history
is `h₀ ++ l` for a start `h₀` with `J h₀` and a completed run `l` of `p` returning the value. -/
noncomputable def traced (S : Spec p Pre Post εmax L T) (J : List Ev → Prop) :
    Spec p (fun h ↦ Pre h ∧ J h)
      (fun a h ↦ Post a h ∧ ∃ h₀ l, h = h₀ ++ l ∧ J h₀ ∧ p.after l = some (.ret a)) εmax L T where
  D h₀ l := J h₀ ∧ S.D h₀ l
  V h₀ l := if J h₀ then S.V h₀ l else 1
  le_one h₀ l := by split_ifs; exacts [S.le_one _ _, le_rfl]
  start_D h₀ h := ⟨h.2, S.start_D h₀ h.1⟩
  start_V h₀ h := by simp only [h.2, ↓reduceIte]; exact S.start_V h₀ h.1
  read x hl ha hD := ⟨hD.1, S.read x hl ha hD.2⟩
  grind hl ha hD := ⟨hD.1, S.grind hl ha hD.2⟩
  commit word hl ha hw hD := ⟨hD.1, S.commit word hl ha hw hD.2⟩
  sample {h₀ _ _} hl ha := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.sample hl ha
    · simp only [hJ0, ↓reduceIte]; exact avg_le_one _ fun _ ↦ le_rfl
  query {h₀ _ _ _ _ _} hl ha hans := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.query hl ha hans
    · simp only [hJ0, ↓reduceIte]; exact le_rfl
  moveEnd {h₀ _ _} hl ha hm hD := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.moveEnd hl ha hm fun h ↦ hD ⟨hJ0, h⟩
    · simp only [hJ0, ↓reduceIte]; exact le_rfl
  retEnd {h₀ _ _} hl ha hD := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.retEnd hl ha fun h ↦ hD ⟨hJ0, h⟩
    · simp only [hJ0, ↓reduceIte]; exact le_rfl
  retDoom hl ha hD := by simp only [hD.1, ↓reduceIte]; exact S.retDoom hl ha hD.2
  post hl ha hD := ⟨S.post hl ha hD.2, _, _, rfl, hD.1, ha⟩
  bound hl hne hm hD := by simp only [hD.1, ↓reduceIte]; exact S.bound hl hne hm hD.2

/-- The doom of a traced specification. -/
theorem traced_D (S : Spec p Pre Post εmax L T) (J : List Ev → Prop) (h₀ l : List Ev) :
    (S.traced J).D h₀ l ↔ J h₀ ∧ S.D h₀ l := Iff.rfl

open Classical in
/-- **`orStableRet` with a post** (J2C-DES T3): from `A ∨ M`, `S`'s post where `A` held, else `M'`, which
every completed run turns `M` into. -/
noncomputable def orPost {A M M' : List Ev → Prop} {PostA : α → List Ev → Prop}
    (S : Spec p A PostA εmax L T)
    (hM : ∀ h₀ l a, p.Reach h₀ l → p.after l = some (.ret a) → M h₀ → M' (h₀ ++ l)) (hT : T ≤ εmax) :
    Spec p (fun h ↦ A h ∨ M h) (fun a h ↦ PostA a h ∨ M' h) εmax (max L T) T where
  D h₀ l := if A h₀ then S.D h₀ l else M h₀
  V h₀ l := if A h₀ then S.V h₀ l else if M h₀ then min 1 T else 1
  le_one h₀ l := by split_ifs; exacts [S.le_one _ _, min_le_left _ _, le_rfl]
  start_D h₀ h := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte]; exact S.start_D h₀ hA
    · simp only [hA, ↓reduceIte]; exact h.resolve_left hA
  start_V h₀ h := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte]; exact (S.start_V h₀ hA).trans (le_max_left _ _)
    · simp only [hA, h.resolve_left hA, ↓reduceIte]
      exact (min_le_right _ _).trans (le_max_right _ _)
  read {h₀ _ _} x hl ha hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.read x hl ha hD
    · simp only [hA, ↓reduceIte] at hD ⊢; exact hD
  grind {h₀ _ _ _} hl ha hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.grind hl ha hD
    · simp only [hA, ↓reduceIte] at hD ⊢; exact hD
  commit {h₀ _ _ _ _} word hl ha hw hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.commit word hl ha hw hD
    · simp only [hA, ↓reduceIte] at hD ⊢; exact hD
  sample {h₀ _ _} hl ha := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte]; exact S.sample hl ha
    · by_cases hM0 : M h₀
      · simp only [hA, hM0, ↓reduceIte, avg_const, le_refl]
      · simp only [hA, hM0, ↓reduceIte]; exact avg_le_one _ fun _ ↦ le_rfl
  query {h₀ _ _ _ _ _} hl ha hans := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte]; exact S.query hl ha hans
    · simp only [hA, ↓reduceIte]; exact le_rfl
  moveEnd {h₀ _ _} hl ha hm hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.moveEnd hl ha hm hD
    · simp only [hA, ↓reduceIte] at hD ⊢; simp [hD]
  retEnd {h₀ _ _} hl ha hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.retEnd hl ha hD
    · simp only [hA, ↓reduceIte] at hD ⊢; simp [hD]
  retDoom {h₀ _ _} hl ha hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.retDoom hl ha hD
    · simp only [hA, ↓reduceIte] at hD ⊢; simp [hD]
  post {h₀ _ _} hl ha hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD; exact .inl (S.post hl ha hD)
    · simp only [hA, ↓reduceIte] at hD; exact .inr (hM _ _ _ hl ha hD)
  bound {h₀ _} hl hne hm hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.bound hl hne hm hD
    · simp only [hA, ↓reduceIte] at hD ⊢
      simp only [hD, ↓reduceIte]
      calc (2 : ENNReal)⁻¹ ^ grindBits _ * min 1 T ≤ 1 * min 1 T := by
            gcongr; exact pow_le_one₀ (by simp) (ENNReal.inv_le_one.2 (by norm_num))
        _ ≤ εmax := by rw [one_mul]; exact (min_le_right _ _).trans hT

/-- **A specification that never returns holds at any follower's allowance** (J2C-DES T3). -/
noncomputable def liftT {A : List Ev → Prop} (S : Spec p A (fun _ _ ↦ False) εmax L 0) (T : ENNReal) :
    Spec p A (fun _ _ ↦ False) εmax L T :=
  { S with retDoom := fun hl ha hD ↦ (S.post hl ha hD).elim }

/-- The doom of a lifted specification. -/
theorem liftT_D {A : List Ev → Prop} (S : Spec p A (fun _ _ ↦ False) εmax L 0) (T : ENNReal) :
    (S.liftT T).D = S.D := rfl

end Spec

end

end LeanVM.Protocol.Compile
