-- New for lvm6 (WP W1, second slice). The final WHIR level as a specification of the verifier
-- language, after leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/LevelFinal.lean` @ fdb317982
-- (`finalTail`, `escRet_queryCheck_le`, `final_agree`): the fold rounds, the final polynomial
-- in the clear, the query group (`I.grp`, F1's group rule when deployed), the openings and the row check,
-- then the terminal claim check. The terminal check (leanVM's tail sumcheck, FORMAT6 v2.2.1 §6.6
-- `R(2, 2)` x 3) is the parameter `chk` with its specification as a hypothesis; the weight the
-- verifier holds is the parameter `WtIface` (its meaning `den` a linear functional on tuples).
import Lvm6Whir

/-!
# The final level (W1)

* `WtIface F`: **the weight as the verifier holds it**: a type `Wt m` for each number `m` of lane
  variables, its meaning `den w : Tup F m →ₗ F`, and a fold `wFold` meaning `foldFn`. `wFolds`
  folds by a list of rounds (`den_wFolds`).
* `FinIface F n`: the final level's code facts: domain, degree, the final polynomial `fpoly s` of
  its `nf` scalars (degree `≤ d`), and the positions (`t` of them from `kq + 1` challenges, with
  `card_pos` as in `TailIface`).
* `finP`: `ℓ` fold rounds, the `nf` scalars, the position group (`gq` bits), the openings of
  commitment `i`, the row check (each opened row, folded by the rounds, is the final polynomial at
  its column), then `chk` on the folded weight, the folded claim and the scalars.
* **`finSpec`**: from the descent invariant (predicate `True`) at `a`, the program rejects. The
  position group escapes within `eFin g A = 2^-g ((A − 1)/n)^t` at the threshold `A` after the
  rounds; `chk` rejects whenever the final polynomial violates the claim (hypothesis `hchk`).
* `pulls_true`: the predicate `True`, pulled back through rounds, stays true.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
  LeanVM.Protocol.Whir.AffineCombiner
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The verifier's weight -/

/-- **The weight as the verifier holds it**: data `Wt m` for `m` lane variables, meaning `den`. -/
structure WtIface (F : Type) [Field F] where
  Wt : ℕ → Type
  den : {m : ℕ} → Wt m → (Tup F m →ₗ[F] F)
  /-- The verifier's fold of a weight by `α`. -/
  wFold : {m : ℕ} → Wt (m + 1) → F → Wt m
  den_wFold : ∀ {m : ℕ} (w : Wt (m + 1)) (α : F), den (wFold w α) = foldFn (den w) α

variable (WI : WtIface F)

/-- The weight folded by `j` rounds, first round first. -/
def wFolds {m : ℕ} : (j : ℕ) → List (Rnd F) → WI.Wt (m + j) → WI.Wt m
  | 0, _, w => w
  | j + 1, rs, w => wFolds j rs.tail (WI.wFold w (rs.headD default).α)

omit [Fintype F] [DecidableEq F] in
theorem den_wFolds {m : ℕ} : ∀ (j : ℕ) (rs : List (Rnd F)) (w : WI.Wt (m + j)),
    WI.den (wFolds WI j rs w) = foldsW j rs (WI.den w)
  | 0, _, _ => rfl
  | j + 1, rs, w => by
    rw [wFolds, den_wFolds j, WI.den_wFold]
    rfl

/-! ## The predicate `True` through the rounds -/

omit [Fintype F] [DecidableEq F] in
/-- An everywhere-true predicate, pulled back through rounds, is everywhere true. -/
theorem pulls_true {n m : ℕ} (dom : Fin n ↪ F) (Ar : ℕ → ℕ) (d : ℕ) :
    ∀ (t j : ℕ) (rs : List (Rnd F)) (Q : Wd F n (m + j)) (B : Tup F (m + j) → Prop),
      (∀ U, B U) → ∀ U, pulls dom Ar d t j rs Q B U
  | _, 0, _, _, _, hB, U => hB U
  | t, j + 1, rs, _, _, hB, U => pulls_true dom Ar d (t + 1) j rs.tail _ _ (fun _ _ T _ ↦ hB T) U

/-! ## The final level's code facts and program -/

/-- **The code facts of the final level.** -/
structure FinIface (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) where
  dom : Fin n ↪ F
  /-- The degree of the level's rounds and of the final polynomial. -/
  d : ℕ
  /-- The final polynomial from its `nf` scalars (message and high part). -/
  nf : ℕ
  fpoly : List F → Tup F 0
  fdeg : ∀ s, DegLE d (fpoly s)
  /-- The positions: `t` columns from `kq + 1` challenges. -/
  kq : ℕ
  t : ℕ
  pos : (Fin (kq + 1) → F) → Fin t → Fin n
  card_pos : ∀ S : Finset (Fin n), ((univ.filter fun v ↦ ∀ k, pos v k ∈ S).card : ℝ≥0∞) ≤
    (Fintype.card F : ℝ≥0∞) ^ (kq + 1) * ((S.card : ℝ≥0∞) / n) ^ t

variable (I : ChalIface F) {n : ℕ} (Fv : FinIface F n)

/-- The final positions of a group's answers. -/
def fPos (qv : List F) : Fin Fv.t → Fin n := Fv.pos (gv qv)

/-- **The final level** (FORMAT6 v2.2.1 §6.6, `i = 4`): `ℓ` fold rounds, the final polynomial's
`nf` scalars, the position group, the openings of commitment `i`, the row check (`fv` folds the
opened rows by the rounds), then the terminal check `chk` (a failed row check rejects at once, `fail`). -/
def finP (g gq i ℓ : ℕ) (fv : List (Rnd F) → (Fin Fv.t → Fin n) → List (List K) → Fin Fv.t → F)
    (chk : WI.Wt 0 → F → List F → VerifierProgram Bool) (w : WI.Wt (0 + ℓ)) (σ : F) :
    VerifierProgram Bool :=
  roundsP I g ℓ >>= fun rs ↦ readFs I Fv.nf >>= fun s ↦ I.grp gq Fv.kq >>= fun qv ↦
  queryOpenings i (List.ofFn fun k ↦ (fPos Fv qv k : ℕ)) >>= fun rows ↦
  if ∀ k, fv rs (fPos Fv qv) rows k = (Fv.fpoly s lane0).eval (Fv.dom (fPos Fv qv k)) then
    chk (wFolds WI ℓ rs w) (foldsC ℓ rs σ) s
  else VerifierProgram.fail

/-- The position group's escape: `2^-g ((A − 1)/n)^t`. -/
noncomputable def eFin (g A : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ g * (((A - 1 : ℕ) : ℝ≥0∞) / n) ^ Fv.t

/-- The positions are good for the final polynomial: if it agrees with the folded word on fewer
than `A` columns, a position falls outside the agreement. -/
def PosOK (A : ℕ) (P : Tup F 0) (f : Wd F n 0) (u : Fin (Fv.kq + 1) → F) : Prop :=
  (agree Fv.dom P f).card < A → ∃ k, Fv.pos u k ∉ agree Fv.dom P f

open Classical in
/-- **The position group's bad values**: at most `|F|^(kq+1) ((A − 1)/n)^t`. -/
theorem card_posBad_le (A : ℕ) (P : Tup F 0) (f : Wd F n 0) :
    ((univ.filter fun u ↦ ¬ PosOK Fv A P f u).card : ℝ≥0∞) ≤
      (Fintype.card F : ℝ≥0∞) ^ (Fv.kq + 1) * (((A - 1 : ℕ) : ℝ≥0∞) / n) ^ Fv.t := by
  set S := agree Fv.dom P f
  by_cases hS : S.card < A
  · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
      (t := univ.filter fun v ↦ ∀ k, Fv.pos v k ∈ S) fun u hu ↦ ?_)) ((Fv.card_pos S).trans ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, PosOK, not_imp, not_exists,
        not_not] at hu ⊢
      exact hu.2
    · gcongr
      exact_mod_cast (by omega : S.card ≤ A - 1)
  · have : (univ.filter fun u ↦ ¬ PosOK Fv A P f u) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun u _ hu ↦ hu fun h ↦ absurd h hS
    rw [this]
    simp

variable {εmax : ℝ≥0∞}

/-- **The final WHIR level, with the descent invariant** (BLUEPRINT T3, W1): from the descent
invariant for the level's word at `a` with the predicate `True`, every group escapes within
`εmax` (the fold pairs `eRound g (par s)`, the positions `eFin gq A`), and the program rejects.
Hypotheses: the rounds' (as `roundsSpec`); `fv` reads the level's word folded by the rounds
(`hread`); `chk` rejects whenever the final polynomial violates the folded claim (`hchk`). -/
noncomputable def finSpec (g gq i ℓ t₀ : ℕ) (hg : g ≤ I.gmax) (hgq : gq ≤ I.gmax)
    (par : ℕ → RoundPar)
    (hpar : ∀ s, t₀ ≤ s → s < t₀ + ℓ → RoundOK (Fintype.card F) n Fv.d (par s))
    (he : ∀ s, t₀ ≤ s → s < t₀ + ℓ → eRound F g (par s) < 1)
    (heT : ∀ s, t₀ ≤ s → s < t₀ + ℓ → eRound F g (par s) ≤ εmax)
    (hchain : ∀ s, t₀ ≤ s → s + 1 < t₀ + ℓ → (par s).A ≤ (par (s + 1)).A - 1)
    (fv : List (Rnd F) → (Fin Fv.t → Fin n) → List (List K) → Fin Fv.t → F)
    (chk : WI.Wt 0 → F → List F → VerifierProgram Bool)
    (word : List (ℕ × ℕ × Word) → Wd F n (0 + ℓ))
    (hread : ∀ h, (commits h).length = i + 1 → ∀ rs ps rows,
      answer h i (List.ofFn fun k ↦ (ps k : ℕ)) = some rows →
        fv rs ps rows = fun k ↦ foldsQ Fv.dom ℓ rs (word (commits h)) lane0 (ps k))
    (w : WI.Wt (0 + ℓ)) (σ : F) (a : ℕ) (ha : 0 < ℓ → a ≤ (par t₀).A - 1)
    (hchk : ∀ rs s, Nonempty (Spec (chk (wFolds WI ℓ rs w) (foldsC ℓ rs σ) s)
      (fun _ ↦ WI.den (wFolds WI ℓ rs w) (Fv.fpoly s) ≠ foldsC ℓ rs σ) (fun b _ ↦ b = false)
      εmax 0 0))
    (heF : eFin Fv gq (aOut (fun s ↦ (par s).A) a t₀ ℓ) < 1)
    (heFT : eFin Fv gq (aOut (fun s ↦ (par s).A) a t₀ ℓ) ≤ εmax) :
    Spec (finP WI I Fv g gq i ℓ fv chk w σ)
      (fun h ↦ (commits h).length = i + 1 ∧
        TViol Fv.dom (word (commits h)) (WI.den w) σ a Fv.d (fun _ ↦ True))
      (fun b _ ↦ b = false) εmax 0 0 := by
  classical
  have h0 : (0 : ℝ≥0∞) ≤ εmax := by positivity
  have hq : Fintype.card F ≠ 0 := Fintype.card_ne_zero
  set A := aOut (fun s ↦ (par s).A) a t₀ ℓ
  let Inv : List (Rnd F) → List (ℕ × ℕ × Word) → Prop := fun rs cs ↦
    cs.length = i + 1 ∧ TViol Fv.dom (foldsQ Fv.dom ℓ rs (word cs)) (WI.den (wFolds WI ℓ rs w))
      (foldsC ℓ rs σ) A Fv.d (fun _ ↦ True)
  unfold finP
  -- the fold rounds
  refine ((roundsSpecJ I Fv.dom (fun cs ↦ cs.length = i + 1) g hg par ℓ t₀ hpar he heT hchain word
    (WI.den w) σ a ha (fun _ _ ↦ True)).mono (fun _ h ↦ h) (fun rs h hp ↦ (⟨hp.1, by
      rw [den_wFolds]
      exact hp.2.mono le_rfl le_rfl fun U _ ↦ pulls_true Fv.dom _ _ _ _ _ _ _ (fun _ ↦ trivial) U⟩ :
        Inv rs (commits h))) le_rfl le_rfl le_rfl).bind' fun rs ↦ ?_
  -- the final polynomial
  refine ((readFsSpec I (Inv := Inv rs) (T := 0) h0 h0 Fv.nf).mono (fun _ h ↦ h) (fun _ _ h ↦ h)
    le_rfl (by split_ifs <;> simp) le_rfl).bind' fun s ↦ ?_
  -- the position group
  let Qf : List (ℕ × ℕ × Word) → Wd F n 0 := fun cs ↦ foldsQ Fv.dom ℓ rs (word cs)
  refine ((I.grpSpec gq Fv.kq hgq (Inv rs) (fun u cs ↦ Inv rs cs ∧ PosOK Fv A (Fv.fpoly s) (Qf cs) u)
    (eFin Fv gq A) heF fun cs hI ↦ ?_).mono (fun _ h ↦ h) (fun _ _ h ↦ h) heFT le_rfl
    le_rfl).bind' fun qv ↦ ?_
  · unfold grpE
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ gq * ((Fintype.card F : ℝ≥0∞) ^ (Fv.kq + 1) *
            (((A - 1 : ℕ) : ℝ≥0∞) / n) ^ Fv.t) / (Fintype.card F : ℝ≥0∞) ^ (Fv.kq + 1) := by
          gcongr
          refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
            (t := univ.filter fun u ↦ ¬ PosOK Fv A (Fv.fpoly s) (Qf cs) u)
            fun u hu ↦ ?_)) (card_posBad_le Fv A _ _)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          exact fun h ↦ hu ⟨hI, h⟩
      _ = eFin Fv gq A := by
          have hQ0 : (Fintype.card F : ℝ≥0∞) ^ (Fv.kq + 1) ≠ 0 := pow_ne_zero _ (by simp [hq])
          have hQt : (Fintype.card F : ℝ≥0∞) ^ (Fv.kq + 1) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
          rw [mul_comm ((Fintype.card F : ℝ≥0∞) ^ (Fv.kq + 1)), ← mul_assoc,
            ENNReal.mul_div_cancel_right hQ0 hQt, eFin]
  -- the openings
  set ps := fPos Fv qv
  let Post : List (List K) → List Ev → Prop := fun rows h ↦
    (Inv rs (commits h) ∧ PosOK Fv A (Fv.fpoly s) (Qf (commits h)) (gv qv)) ∧
      fv rs ps rows = fun k ↦ Qf (commits h) lane0 (ps k)
  refine ((Spec.ofNoMove (p := queryOpenings i (List.ofFn fun k ↦ (ps k : ℕ)))
    (Pre := fun h ↦ Inv rs (commits h) ∧ PosOK Fv A (Fv.fpoly s) (Qf (commits h)) (gv qv))
    (Post := Post) (T := 0) (noMv_queryP _ _).noMove (e := 0) (by norm_num) fun h₀ hP ↦ ?_).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun rows ↦ ?_
  · unfold escRet
    rw [retExp_queryP]
    split
    · rename_i rows hans
      rw [List.append_nil] at hans
      have hv := hread h₀ hP.1.1 rs ps rows hans
      have hpost : Post rows (h₀ ++ [] ++ [Ev.query rows]) := by
        simp only [Post, List.append_nil, commits_append_query]
        exact ⟨hP, hv⟩
      rw [List.append_nil] at hpost
      simp [hpost]
    · exact le_rfl
  -- the row check, then the terminal check
  refine Spec.ite (fun hc ↦ (Classical.choice (hchk rs s)).mono (fun h hp ↦ ?_) (fun _ _ h ↦ h)
    le_rfl le_rfl le_rfl) (fun _ ↦ Spec.fail)
  obtain ⟨⟨⟨-, hT⟩, hpos⟩, hv⟩ := hp
  have hall : ∀ k, ps k ∈ agree Fv.dom (Fv.fpoly s) (Qf (commits h)) := fun k ↦ by
    rw [mem_agree0, ← hc k, hv]
  have hA : A ≤ (agree Fv.dom (Fv.fpoly s) (Qf (commits h))).card := by
    by_contra hlt
    obtain ⟨k, hk⟩ := hpos (by omega)
    exact hk (hall k)
  exact hT (Fv.fpoly s) (Fv.fdeg s) hA trivial

end Lvm6.Whir
