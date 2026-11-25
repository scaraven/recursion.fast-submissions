-- New for lvm6 (WP W1, first slice). The fold rounds of one WHIR level as a specification of the
-- verifier language (season 1's `Spec` calculus), after leanVM `formal/lean_vm/LeanVM/Protocol/Whir/
-- Sound/{Folds,FoldRoundCwyz}.lean` @ fdb317982: four scalars `u₀, w, c₀, c₁`, then the pair
-- `(α, β)` as one ground group (`I.grp g 1`; F1's `grp6` when deployed, `Lvm6WhirE2`) in place of leanVM's
-- `grind` + two draws; the doom is the descent invariant `TViol` of `Lvm6WhirTuple`.
import Lvm6WhirTuple
import Lvm6WhirGround
import Lvm6Params

/-!
# The fold rounds of a level (W1)

* `Rnd F`: a round's message `(u₀, w, c₀, c₁)` and challenges `(α, β)`.
* `roundP I g`: the round's program: four reads (`readF`), a group of two values (`I.grp g 1`).
* `RoundPar`, `RoundOK q n d p`: a round's threshold `A`, CWYZ26 witness `(m, D, B)` and escape
  numerator `N` with `nAff + 2 jl n (A − 1) d q ≤ N`; `eRound g p = 2^-g N / |F|²`.
* **`roundSpec`**: one round, from `TViol` at `A − 1` to `TViol` at `A` for the fold, the folded
  weight and claim, and the pulled-back predicate; the ground pair's escape is `eRound`.
* `roundsP I g j`, **`roundsSpec`**: `j` rounds, round `t` at `par t`, the thresholds chained
  (`A_t ≤ A_{t+1} − 1`); `foldsQ`, `foldsW`, `foldsC`, `pulls`, `aOut` thread the word, weight,
  claim, predicate and threshold.
* `roundOK_of_foldRoundOK`: PARAM's `foldRoundOK` (leanVM's bodies) gives `RoundOK` at
  `q = 2^128`, `N = budget · 2^128` (M1's `foldRoundOK_sound`; `params_foldRoundOK` is `rfl`).
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
  LeanVM.Protocol.Whir.AffineCombiner
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] (I : ChalIface F)

/-! ## Reads -/

/-- One scalar, read as a value of `F`. -/
def readF : VerifierProgram F := VerifierProgram.readScalar >>= fun x ↦ pure (I.rd x)

/-- `k` scalars. -/
def readFs : ℕ → VerifierProgram (List F)
  | 0 => pure []
  | k + 1 => readF I >>= fun x ↦ readFs k >>= fun xs ↦ pure (x :: xs)

variable {εmax : ℝ≥0∞}

/-- A read keeps an invariant of the commitments. -/
noncomputable def readFSpec {Inv : List (ℕ × ℕ × Word) → Prop} {T : ℝ≥0∞} (hT : T ≤ εmax) :
    Spec (readF I) (fun h ↦ Inv (commits h)) (fun _ h ↦ Inv (commits h)) εmax 0 T :=
  (Spec.readE (Post := fun _ h ↦ Inv (commits h))
      (fun h₀ x hI ↦ by rwa [commits_append_read]) hT).bind' fun x ↦
    Spec.ret (Post := fun (_ : F) h ↦ Inv (commits h)) (I.rd x)

/-- Reads keep an invariant of the commitments. -/
noncomputable def readFsSpec {Inv : List (ℕ × ℕ × Word) → Prop} {T : ℝ≥0∞} (hT : T ≤ εmax)
    (h0 : (0 : ℝ≥0∞) ≤ εmax) :
    (k : ℕ) → Spec (readFs I k) (fun h ↦ Inv (commits h)) (fun _ h ↦ Inv (commits h)) εmax
      (if k = 0 then T else 0) T
  | 0 => Spec.ret (Post := fun (_ : List F) h ↦ Inv (commits h)) []
  | k + 1 => by
    refine ((readFSpec I (Inv := Inv) (T := if k = 0 then T else 0) ?_).bind' fun x ↦
      (readFsSpec hT h0 k).bind' fun xs ↦
        Spec.ret (Post := fun (_ : List F) h ↦ Inv (commits h)) (x :: xs)).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl
    split_ifs
    · exact hT
    · exact h0

/-! ## One round -/

/-- A fold round's message and challenges. -/
structure Rnd (F : Type) where
  u₀ : F
  w : F
  c₀ : F
  c₁ : F
  α : F
  β : F

instance : Inhabited (Rnd F) := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- **A fold round**: `u₀, w, c₀, c₁`, then `(α, β)` as one ground group of `g` bits. -/
def roundP (g : ℕ) : VerifierProgram (Rnd F) :=
  readF I >>= fun u₀ ↦ readF I >>= fun w ↦ readF I >>= fun c₀ ↦ readF I >>= fun c₁ ↦
    I.grp g 1 >>= fun v ↦ pure ⟨u₀, w, c₀, c₁, v.getD 0 0, v.getD 1 0⟩

/-- A round's parameters: threshold, CWYZ26 witness, escape numerator. -/
structure RoundPar where
  A : ℕ
  mm : ℕ
  D : ℕ
  Bb : ℕ
  N : ℕ

/-- The round's hypotheses at field size `q`, `n` columns and degree `d`. -/
def RoundOK (q n d : ℕ) (p : RoundPar) : Prop :=
  n * d < (p.A - 1) * (p.A - 1) ∧ Admissible n d p.A p.mm p.D p.Bb ∧
    nAff q n d p.A p.mm p.D p.Bb + 2 * jl n (p.A - 1) d * (q : ℚ) ≤ p.N

/-- The ground pair's escape: `2^-g · N / |F|²`. -/
noncomputable def eRound (F : Type) [Fintype F] (g : ℕ) (p : RoundPar) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ g * (p.N : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 2

variable {n m : ℕ} (dom : Fin n ↪ F)

/-- The doom after a round, for the round `r`. -/
def roundPost (Qf : List (ℕ × ℕ × Word) → Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F)
    (A d : ℕ) (B : List (ℕ × ℕ × Word) → Tup F (m + 1) → Prop) (r : Rnd F)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  TViol dom (foldQ dom r.α r.β (Qf cs)) (foldFn W r.α) (foldClaim σ r.α r.β r.u₀ r.w r.c₀ r.c₁) A d
    (pullT dom (Qf cs) A d r.α r.β (B cs))

open Classical in
/-- The round's bad pairs are at most `N`. -/
theorem card_roundBad_le {d : ℕ} {p : RoundPar} (hp : RoundOK (Fintype.card F) n d p)
    (Q : Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (B : Tup F (m + 1) → Prop)
    (hv : TViol dom Q W σ (p.A - 1) d B) (u₀ w c₀ c₁ : F) :
    (univ.filter fun u : Fin 2 → F ↦ ¬ TViol dom (foldQ dom (u 0) (u 1) Q) (foldFn W (u 0))
        (foldClaim σ (u 0) (u 1) u₀ w c₀ c₁) p.A d (pullT dom Q p.A d (u 0) (u 1) B)).card
      ≤ p.N := by
  classical
  have h := card_foldEsc_le dom Q W σ hp.1 hp.2.1 hv u₀ w c₀ c₁
  have hN : ((foldEsc dom Q W σ p.A d B u₀ w c₀ c₁).card : ℚ) ≤ p.N := h.trans hp.2.2
  have hinj : (univ.filter fun u : Fin 2 → F ↦ ¬ TViol dom (foldQ dom (u 0) (u 1) Q) (foldFn W (u 0))
        (foldClaim σ (u 0) (u 1) u₀ w c₀ c₁) p.A d (pullT dom Q p.A d (u 0) (u 1) B)).card ≤
      (foldEsc dom Q W σ p.A d B u₀ w c₀ c₁).card := by
    refine Finset.card_le_card_of_injOn (fun u ↦ (u 0, u 1)) (fun u hu ↦ ?_) (fun u _ v _ huv ↦ ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
      simp only [foldEsc, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      exact hu
    · simp only [Prod.mk.injEq] at huv
      funext i
      fin_cases i
      · exact huv.1
      · exact huv.2
  exact_mod_cast (Nat.cast_le.mpr hinj).trans hN

/-- One fold round, framed by an invariant `J` of the commitments (the rounds commit nothing). -/
noncomputable def roundSpecJ (J : List (ℕ × ℕ × Word) → Prop) (g : ℕ) (hg : g ≤ I.gmax) {d : ℕ}
    {p : RoundPar} (hp : RoundOK (Fintype.card F) n d p) (he : eRound F g p < 1)
    (heT : eRound F g p ≤ εmax) (Qf : List (ℕ × ℕ × Word) → Wd F n (m + 1))
    (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (B : List (ℕ × ℕ × Word) → Tup F (m + 1) → Prop) :
    Spec (roundP I g)
      (fun h ↦ J (commits h) ∧ TViol dom (Qf (commits h)) W σ (p.A - 1) d (B (commits h)))
      (fun r h ↦ J (commits h) ∧ roundPost dom Qf W σ p.A d B r (commits h)) εmax 0 0 := by
  classical
  have h0 : (0 : ℝ≥0∞) ≤ εmax := by positivity
  set Inv : List (ℕ × ℕ × Word) → Prop := fun cs ↦
    J cs ∧ TViol dom (Qf cs) W σ (p.A - 1) d (B cs)
  unfold roundP
  refine (readFSpec I (Inv := Inv) h0).bind' fun u₀ ↦ (readFSpec I (Inv := Inv) h0).bind' fun w ↦
    (readFSpec I (Inv := Inv) h0).bind' fun c₀ ↦ (readFSpec I (Inv := Inv) h0).bind' fun c₁ ↦ ?_
  refine ((I.grpSpec g 1 hg Inv (fun u cs ↦ J cs ∧ TViol dom (foldQ dom (u 0) (u 1) (Qf cs))
      (foldFn W (u 0)) (foldClaim σ (u 0) (u 1) u₀ w c₀ c₁) p.A d
      (pullT dom (Qf cs) p.A d (u 0) (u 1) (B cs))) (eRound F g p) he fun cs hI ↦ ?_).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) heT le_rfl le_rfl).bind' fun v ↦ ?_
  · unfold grpE eRound
    gcongr
    refine le_trans (Finset.card_le_card (t := univ.filter fun u : Fin 2 → F ↦ ¬ TViol dom
      (foldQ dom (u 0) (u 1) (Qf cs)) (foldFn W (u 0)) (foldClaim σ (u 0) (u 1) u₀ w c₀ c₁)
      p.A d (pullT dom (Qf cs) p.A d (u 0) (u 1) (B cs))) fun u hu ↦ ?_) ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact fun h ↦ hu ⟨hI.1, h⟩
    · exact card_roundBad_le dom hp _ W σ _ hI.2 u₀ w c₀ c₁
  · exact (Spec.ret (Post := fun r h ↦ J (commits h) ∧ roundPost dom Qf W σ p.A d B r (commits h))
      ⟨u₀, w, c₀, c₁, v.getD 0 0, v.getD 1 0⟩).mono (fun h hG ↦ hG) (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl

/-- **One fold round** (BLUEPRINT T3 in the doom calculus): from the descent invariant at
`A − 1`, the round returns `r` with the invariant at `A` for the fold by `(r.α, r.β)`, the folded
weight, the claim `foldClaim`, and `B` pulled back; the ground pair escapes within
`eRound g p ≤ εmax`. -/
noncomputable def roundSpec (g : ℕ) (hg : g ≤ I.gmax) {d : ℕ} {p : RoundPar}
    (hp : RoundOK (Fintype.card F) n d p) (he : eRound F g p < 1) (heT : eRound F g p ≤ εmax)
    (Qf : List (ℕ × ℕ × Word) → Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F)
    (B : List (ℕ × ℕ × Word) → Tup F (m + 1) → Prop) :
    Spec (roundP I g) (fun h ↦ TViol dom (Qf (commits h)) W σ (p.A - 1) d (B (commits h)))
      (fun r h ↦ roundPost dom Qf W σ p.A d B r (commits h)) εmax 0 0 :=
  (roundSpecJ I dom (fun _ ↦ True) g hg hp he heT Qf W σ B).mono (fun _ h ↦ ⟨trivial, h⟩)
    (fun _ _ h ↦ h.2) le_rfl le_rfl le_rfl

/-! ## The rounds of a level -/

/-- `j` fold rounds. -/
def roundsP (g : ℕ) : ℕ → VerifierProgram (List (Rnd F))
  | 0 => pure []
  | j + 1 => roundP I g >>= fun r ↦ roundsP g j >>= fun rs ↦ pure (r :: rs)

/-- The word folded by `j` rounds, first round first. -/
def foldsQ : (j : ℕ) → List (Rnd F) → Wd F n (m + j) → Wd F n m
  | 0, _, Q => Q
  | j + 1, rs, Q => foldsQ j rs.tail (foldQ dom (rs.headD default).α (rs.headD default).β Q)

/-- The weight folded by `j` rounds. -/
noncomputable def foldsW : (j : ℕ) → List (Rnd F) → (Tup F (m + j) →ₗ[F] F) → (Tup F m →ₗ[F] F)
  | 0, _, W => W
  | j + 1, rs, W => foldsW j rs.tail (foldFn W (rs.headD default).α)

/-- The claim after `j` rounds. -/
def foldsC : (j : ℕ) → List (Rnd F) → F → F
  | 0, _, σ => σ
  | j + 1, rs, σ =>
    let r := rs.headD default
    foldsC j rs.tail (foldClaim σ r.α r.β r.u₀ r.w r.c₀ r.c₁)

/-- The predicate pulled back through `j` rounds, round `t` at threshold `Ar t`. -/
def pulls (Ar : ℕ → ℕ) (d : ℕ) : (t j : ℕ) → List (Rnd F) → Wd F n (m + j) →
    (Tup F (m + j) → Prop) → Tup F m → Prop
  | _, 0, _, _, B => B
  | t, j + 1, rs, Q, B =>
    let r := rs.headD default
    pulls Ar d (t + 1) j rs.tail (foldQ dom r.α r.β Q) (pullT dom Q (Ar t) d r.α r.β B)

/-- The threshold after `j` rounds from `a`, round `t` producing `Ar t`. -/
def aOut (Ar : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | a, _, 0 => a
  | _, t, j + 1 => aOut Ar (Ar t) (t + 1) j

/-- The doom after `j` rounds. -/
def roundsPost (par : ℕ → RoundPar) (d : ℕ) (j t : ℕ) (Qf : List (ℕ × ℕ × Word) → Wd F n (m + j))
    (W : Tup F (m + j) →ₗ[F] F) (σ : F) (a : ℕ) (B : List (ℕ × ℕ × Word) → Tup F (m + j) → Prop)
    (rs : List (Rnd F)) (cs : List (ℕ × ℕ × Word)) : Prop :=
  TViol dom (foldsQ dom j rs (Qf cs)) (foldsW j rs W) (foldsC j rs σ) (aOut (fun s ↦ (par s).A) a t j) d
    (pulls dom (fun s ↦ (par s).A) d t j rs (Qf cs) (B cs))

/-- The fold rounds of a level, framed by an invariant `J` of the commitments. Only the rounds run,
`s ∈ [t, t + j)`, carry hypotheses. -/
noncomputable def roundsSpecJ (J : List (ℕ × ℕ × Word) → Prop) (g : ℕ) (hg : g ≤ I.gmax) {d : ℕ}
    (par : ℕ → RoundPar) :
    (j t : ℕ) → (∀ s, t ≤ s → s < t + j → RoundOK (Fintype.card F) n d (par s)) →
      (∀ s, t ≤ s → s < t + j → eRound F g (par s) < 1) →
      (∀ s, t ≤ s → s < t + j → eRound F g (par s) ≤ εmax) →
      (∀ s, t ≤ s → s + 1 < t + j → (par s).A ≤ (par (s + 1)).A - 1) →
      (Qf : List (ℕ × ℕ × Word) → Wd F n (m + j)) → (W : Tup F (m + j) →ₗ[F] F) →
      (σ : F) → (a : ℕ) → (0 < j → a ≤ (par t).A - 1) →
      (B : List (ℕ × ℕ × Word) → Tup F (m + j) → Prop) →
      Spec (roundsP I g j)
        (fun h ↦ J (commits h) ∧ TViol dom (Qf (commits h)) W σ a d (B (commits h)))
        (fun rs h ↦ J (commits h) ∧ roundsPost dom par d j t Qf W σ a B rs (commits h)) εmax 0 0
  | 0, t, _, _, _, _, Qf, W, σ, a, _, B =>
    Spec.ret (Post := fun rs h ↦ J (commits h) ∧ roundsPost dom par d 0 t Qf W σ a B rs (commits h)) []
  | j + 1, t, hpar, he, heT, hchain, Qf, W, σ, a, ha, B =>
    ((roundSpecJ I dom J g hg (hpar t le_rfl (by omega)) (he t le_rfl (by omega))
        (heT t le_rfl (by omega)) Qf W σ B).mono
        (fun _ hv ↦ ⟨hv.1, hv.2.mono (ha (by omega)) le_rfl fun _ h ↦ h⟩) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl).bind'
      fun r ↦ ((roundsSpecJ J g hg par j (t + 1)
          (fun s h1 h2 ↦ hpar s (by omega) (by omega)) (fun s h1 h2 ↦ he s (by omega) (by omega))
          (fun s h1 h2 ↦ heT s (by omega) (by omega)) (fun s h1 h2 ↦ hchain s (by omega) (by omega))
          (fun cs ↦ foldQ dom r.α r.β (Qf cs)) (foldFn W r.α)
          (foldClaim σ r.α r.β r.u₀ r.w r.c₀ r.c₁) (par t).A
          (fun hj ↦ hchain t le_rfl (by omega))
          (fun cs ↦ pullT dom (Qf cs) (par t).A d r.α r.β (B cs))).mono
          (fun _ hv ↦ hv) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun rs ↦
        Spec.ret (Post := fun rs h ↦ J (commits h) ∧
            roundsPost dom par d (j + 1) t Qf W σ a B rs (commits h))
          (r :: rs) |>.mono (fun _ hv ↦ hv) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **The fold rounds of a level**: `j` rounds from round index `t`, each round `s ∈ [t, t + j)` at
`par s` (`RoundOK`, escape `eRound g (par s) ≤ εmax`), thresholds chained; from `TViol` at
`a ≤ A_t − 1` to `TViol` at `aOut` for the folded word, weight and claim, with the predicate pulled
back through every round. Lead `0`. -/
noncomputable def roundsSpec (g : ℕ) (hg : g ≤ I.gmax) {d : ℕ} (par : ℕ → RoundPar) (j t : ℕ)
    (hpar : ∀ s, t ≤ s → s < t + j → RoundOK (Fintype.card F) n d (par s))
    (he : ∀ s, t ≤ s → s < t + j → eRound F g (par s) < 1)
    (heT : ∀ s, t ≤ s → s < t + j → eRound F g (par s) ≤ εmax)
    (hchain : ∀ s, t ≤ s → s + 1 < t + j → (par s).A ≤ (par (s + 1)).A - 1)
    (Qf : List (ℕ × ℕ × Word) → Wd F n (m + j)) (W : Tup F (m + j) →ₗ[F] F)
    (σ : F) (a : ℕ) (ha : 0 < j → a ≤ (par t).A - 1)
    (B : List (ℕ × ℕ × Word) → Tup F (m + j) → Prop) :
    Spec (roundsP I g j) (fun h ↦ TViol dom (Qf (commits h)) W σ a d (B (commits h)))
      (fun rs h ↦ roundsPost dom par d j t Qf W σ a B rs (commits h)) εmax 0 0 :=
  (roundsSpecJ I dom (fun _ ↦ True) g hg par j t hpar he heT hchain Qf W σ a ha B).mono
    (fun _ h ↦ ⟨trivial, h⟩) (fun _ _ h ↦ h.2) le_rfl le_rfl le_rfl

/-! ## PARAM's round check -/

/-- PARAM's `foldRoundOK` is M1's (leanVM's body, both). -/
theorem params_foldRoundOK : Lvm6.Params.foldRoundOK = foldRoundOK := rfl

/-- **A round of PARAM's table gives `RoundOK`** at `q = 2^128`, with numerator `budget · 2^128`. -/
theorem roundOK_of_foldRoundOK {κ R k Aend j mm D Bb budget : ℕ}
    (h : Lvm6.Params.foldRoundOK κ R k Aend j mm D Bb budget = true) :
    RoundOK (2 ^ 128) (roundN κ R) (roundD κ k) ⟨roundA k Aend j, mm, D, Bb, budget * 2 ^ 128⟩ := by
  rw [params_foldRoundOK] at h
  obtain ⟨hadm, hgap, hbud⟩ := foldRoundOK_sound h
  refine ⟨hgap, hadm, ?_⟩
  have hq : (0 : ℚ) < (2 : ℚ) ^ 128 := by positivity
  have hb : (qE : ℚ) = 2 ^ 128 := by norm_num [qE]
  rw [hb] at hbud
  push_cast
  have := (div_le_div_iff_of_pos_right (c := (2 : ℚ) ^ 128) hq).mpr hbud
  have e1 : ((2 : ℚ) ^ 128 * nAff (2 ^ 128) (roundN κ R) (roundD κ k) (roundA k Aend j) mm D Bb +
      2 * (jl (roundN κ R) (roundA k Aend j - 1) (roundD κ k) : ℚ) * (2 ^ 128) ^ 2) / 2 ^ 128 =
      nAff (2 ^ 128) (roundN κ R) (roundD κ k) (roundA k Aend j) mm D Bb +
        2 * (jl (roundN κ R) (roundA k Aend j - 1) (roundD κ k) : ℚ) * 2 ^ 128 := by
    field_simp
  have e2 : (budget : ℚ) * (2 ^ 128) ^ 2 / 2 ^ 128 = budget * 2 ^ 128 := by field_simp
  rw [e1, e2] at this
  exact_mod_cast this

end Lvm6.Whir
