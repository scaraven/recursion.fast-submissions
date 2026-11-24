-- New for lvm6 (WP W2, second slice). The opening's unconditional specification for the extractor (ASM's
-- `Stmt.openGood6` on `lvm6/W2-asm`): from one commitment, on acceptance the history carries every level's
-- facts — the rounds' `GoodRs` (`Lvm6WhirExc`), the transitions' `OodOK`/`TailBackP`/values, the final
-- polynomial's agreement and claim — each attached to the run of its piece in the history (`OpenSem`). The
-- groups' escapes are the doom specification's (`eRound`, `eOod`, `eQry`, `eFin`, the terminal check's).
import Lvm6WhirExc
import Lvm6WhirCommit

/-!
# The opening for the extractor (W2)

* `RunAt p N N' a h`: `p` ran on the events `[N, N')` of `h`, returning `a` (stable under extension);
  `ret_run_unique`: two returning runs of `p` that prefix the same list coincide (so `OpenSem`'s
  existential decomposition is the run's).
* `Spec.runRec`, `Spec.atLen`, `Spec.frameAll`, `specKeep`, `chkU`: plumbing.
* `TailBackP`, `TailFacts` (a level's transition, on the tail's output `o`), **`tailSpecU`**.
* **`OpenSem I lad w σ a cs l`**: the facts on the opening's local events `l` with the final commitments
  `cs`: per level an existential decomposition of `l` into the runs of `roundsP`, `tailP` (mid) or
  `roundsP`, `readFs` (final) with their values, and the facts on those values.
* **`ladSpecU`**: the ladder from `(commits h).length = lad.i + 1` and `h.length = N` to
  `b = true → OpenSem … (commits h) (h.drop N)`; **`openGood_W1`**: the deployed instance, the
  unfolded `Stmt.openGood6 GWD (whirAt whirP)`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
  LeanVM.Protocol.Whir.AffineCombiner LeanVM.Protocol.Whir
open scoped ENNReal

/-! ## Runs in a history -/

section Runs

variable {α : Type}

/-- **`p` ran on the events `[N, N')` of `h`**, returning `a`. -/
def RunAt (p : VerifierProgram α) (N N' : ℕ) (a : α) (h : List Ev) : Prop :=
  N ≤ N' ∧ N' ≤ h.length ∧ p.after ((h.drop N).take (N' - N)) = some (.ret a)

theorem RunAt.append {p : VerifierProgram α} {N N' : ℕ} {a : α} {h : List Ev} (r : RunAt p N N' a h)
    (l : List Ev) : RunAt p N N' a (h ++ l) := by
  obtain ⟨h1, h2, h3⟩ := r
  refine ⟨h1, by simp; omega, ?_⟩
  rwa [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem after_ret_append {p : VerifierProgram α} {l : List Ev} {a : α} (h : p.after l = some (.ret a))
    (e : Ev) (es : List Ev) : p.after (l ++ e :: es) = none := by
  rw [VerifierProgram.after_append, h]
  cases e <;> simp [VerifierProgram.after]

/-- **Returning runs are prefix-free**: two returning runs of `p` that prefix the same list coincide. -/
theorem ret_run_unique {p : VerifierProgram α} {l₁ l₂ l₁' l₂' : List Ev} {a a' : α}
    (h1 : p.after l₁ = some (.ret a)) (h1' : p.after l₁' = some (.ret a')) (he : l₁ ++ l₂ = l₁' ++ l₂') :
    l₁ = l₁' ∧ a = a' := by
  rcases List.append_eq_append_iff.mp he with ⟨c, rfl, -⟩ | ⟨c, rfl, -⟩
  · rcases c with _ | ⟨e, es⟩
    · simp only [List.append_nil] at h1 h1' ⊢
      rw [h1] at h1'
      simpa using h1'
    · rw [after_ret_append h1 e es] at h1'
      exact absurd h1' (by simp)
  · rcases c with _ | ⟨e, es⟩
    · simp only [List.append_nil] at h1 h1' ⊢
      rw [h1] at h1'
      simpa using h1'
    · rw [after_ret_append h1' e es] at h1
      exact absurd h1 (by simp)

variable {p : VerifierProgram α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop} {ε L T : ℝ≥0∞}

/-- **Record the run**: from start length `N`, the postcondition also gives the run on `[N, |h|)`. -/
noncomputable def _root_.LeanVM.Protocol.Compile.Spec.runRec (S : Spec p Pre Post ε L T) (N : ℕ) :
    Spec p (fun h ↦ Pre h ∧ h.length = N) (fun a h ↦ Post a h ∧ RunAt p N h.length a h) ε L T :=
  (S.mono (fun _ h ↦ h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).traceAnd
    (fun a h ↦ RunAt p N h.length a h) fun h₀ l a hp _ ha ↦ by
      have e : ((h₀ ++ l).drop N).take ((h₀ ++ l).length - N) = l := by
        rw [← hp.2]; simp
      refine ⟨by simp [← hp.2], le_rfl, ?_⟩
      rw [e]; exact ha

/-- **Fix the start length**. -/
noncomputable def _root_.LeanVM.Protocol.Compile.Spec.atLen
    (S : ∀ N, Spec p (fun h ↦ Pre h ∧ h.length = N) Post ε L T) : Spec p Pre Post ε L T :=
  (Spec.exPre (ι := ℕ) (Pre := fun N h ↦ Pre h ∧ h.length = N) S).mono
    (fun h hp ↦ ⟨h.length, hp, rfl⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **Frame a fact every extension keeps.** -/
noncomputable def _root_.LeanVM.Protocol.Compile.Spec.frameAll (S : Spec p Pre Post ε L T)
    (J : List Ev → Prop) (hJ : ∀ h l, J h → J (h ++ l)) :
    Spec p (fun h ↦ Pre h ∧ J h) (fun a h ↦ Post a h ∧ J h) ε L T :=
  S.frame J fun h₀ l _ hj ↦ hJ h₀ l hj

/-- Any program, doom everywhere, potential `0` (ASM's `specTriv`). -/
def specKeep (p : VerifierProgram α) {εmax : ℝ≥0∞} :
    Spec p (fun _ ↦ True) (fun _ _ ↦ True) εmax 0 0 where
  D _ _ := True
  V _ _ := 0
  le_one _ _ := zero_le_one
  start_D _ _ := trivial
  start_V _ _ := le_rfl
  read _ _ _ _ := trivial
  grind _ _ _ := trivial
  commit _ _ _ _ _ := trivial
  sample _ _ := by simp
  query _ _ _ := le_rfl
  moveEnd _ _ _ hD := (hD trivial).elim
  retEnd _ _ hD := (hD trivial).elim
  retDoom _ _ _ := by simp
  post _ _ _ := trivial
  bound _ _ _ _ := by simp

open Classical in
/-- **A terminal check, unconditionally**: from its doom form under `P`, on acceptance `P → Q`. -/
noncomputable def chkU (q : VerifierProgram Bool) (P Q : Prop) {εmax : ℝ≥0∞}
    (hq : P → Nonempty (Spec q (fun _ ↦ ¬ Q) (fun b _ ↦ b = false) εmax 0 0)) :
    Spec q (fun _ ↦ True) (fun b _ ↦ b = true → P → Q) εmax 0 0 :=
  if hP : P then
    if hQ : Q then (specKeep q).mono (fun _ h ↦ h) (fun _ _ _ _ _ ↦ hQ) le_rfl le_rfl le_rfl
    else (hq hP).some.mono (fun _ _ ↦ hQ) (fun b _ hb hb' ↦ by simp [hb] at hb') le_rfl le_rfl le_rfl
  else (specKeep q).mono (fun _ h ↦ h) (fun _ _ _ _ hp ↦ absurd hp hP) le_rfl le_rfl le_rfl

theorem take_commits_append {k : ℕ} {h : List Ev} (hk : k ≤ (commits h).length) (l : List Ev) :
    (commits (h ++ l)).take k = (commits h).take k := by
  rw [commits_app, List.take_append_of_le_length hk]

theorem le_commits_append {k : ℕ} {h : List Ev} (hk : k ≤ (commits h).length) (l : List Ev) :
    k ≤ (commits (h ++ l)).length := by
  rw [commits_app, List.length_append]; omega

end Runs

/-! ## A level's transition -/

section Tail

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n n' m' : ℕ} (L : TailIface F n n' m')

/-- `TailBack` at the positions `ps` and `λ` (`TailBack L … v lam = TailBackP L … (L.pos v) lam`). -/
def TailBackP (f : Wd F n 0) (g : Wd F n' m') (W : Tup F 0 →ₗ[F] F) (σ y : F) (A A' : ℕ) (hi : List F)
    (z : Fin (L.ko + 1) → F) (ps : Fin L.t → Fin n) (lam : F) : Prop :=
  ∀ U ∈ tupleList L.dom' g A' L.d', glued L W z lam ps U = gluedC σ y lam (qVals L f hi ps) →
    coefQ L W σ y z ps (qVals L f hi ps) U = 0 ∧ A ≤ (agree L.dom (L.cand hi U) f).card

/-- **A transition's facts** on the tail's output: OOD separation of the next list, `TailBackP`, and the
verifier's values are the folded word minus the high part at the positions. -/
def TailFacts (f : Wd F n 0) (g : Wd F n' m') (W : Tup F 0 →ₗ[F] F) (σ : F) (A A' : ℕ)
    (o : TailOut F L.ko L.t n) : Prop :=
  OodOK L o.z g A' ∧ TailBackP L f g W σ o.y A A' o.hi o.z o.ps o.lam ∧ o.c = qVals L f o.hi o.ps

variable (I : ChalIface F) {εmax : ℝ≥0∞}

/-- **A level's interface, unconditionally**: from `i + 1` commitments, the tail returns with `i + 2` and
`TailFacts` for the folded word `cur` and the next word `nxt`; the OOD group's escape `eOod`, the query
group's `eQry` (`card_oodBad_le`, `card_tbad_le`: no doom). -/
noncomputable def tailSpecU (ht wd i gO gQ : ℕ) (hgO : gO ≤ I.gmax) (hgQ : gQ ≤ I.gmax)
    (vals : List F → (Fin L.t → Fin n) → List (List K) → Fin L.t → F)
    (cur : List (ℕ × ℕ × Word) → Wd F n 0) (nxt : List (ℕ × ℕ × Word) → Wd F n' m')
    (W : Tup F 0 →ₗ[F] F) (σ : F) (A A' : ℕ)
    (hread : ∀ h, (commits h).length = i + 2 → ∀ ps rows,
      answer h i (List.ofFn fun k ↦ (ps k : ℕ)) = some rows → ∀ hi,
        vals hi ps rows = fun k ↦ cur (commits h) lane0 (ps k) - (L.hp hi lane0).eval (L.dom (ps k)))
    (hgap : n' * L.d' < A' * A')
    (heO : eOod L gO (jl n' A' L.d') < 1) (heOT : eOod L gO (jl n' A' L.d') ≤ εmax)
    (heQ : eQry L gQ (jl n' A' L.d') A < 1) (heQT : eQry L gQ (jl n' A' L.d') A ≤ εmax) :
    Spec (tailP L I ht wd i gO gQ vals) (fun h ↦ (commits h).length = i + 1)
      (fun o h ↦ (commits h).length = i + 2 ∧
        TailFacts L (cur (commits h)) (nxt (commits h)) W σ A A' o) εmax 0 0 := by
  classical
  have h0 : (0 : ℝ≥0∞) ≤ εmax := by positivity
  have hq : Fintype.card F ≠ 0 := Fintype.card_ne_zero
  let D1 : List (ℕ × ℕ × Word) → Prop := fun cs ↦ cs.length = i + 2
  unfold tailP
  refine ((readFsSpec I (Inv := fun cs ↦ cs.length = i + 1) (T := 0) h0 h0 L.nh).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by split_ifs <;> simp) le_rfl).bind' fun hi ↦ ?_
  refine (Spec.commitP (Post := fun _ h ↦ D1 (commits h)) ht wd
    (fun h₀ word hP _ ↦ ?_) h0).bind' fun _ ↦ ?_
  · rw [commits_append_commit]
    simp [D1, hP]
  refine (I.sepSpec D1 εmax 0).bind' fun _ ↦ ?_
  refine ((I.grpSpec gO L.ko hgO D1 (fun u cs ↦ D1 cs ∧ OodOK L u (nxt cs) A')
    (eOod L gO (jl n' A' L.d')) heO fun cs hI ↦ ?_).mono (fun _ h ↦ h) (fun _ _ h ↦ h) heOT le_rfl
    le_rfl).bind' fun zv ↦ ?_
  · unfold grpE
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ gO * ((((jl n' A' L.d').choose 2 * L.δ : ℕ) : ℝ≥0∞) *
            (Fintype.card F : ℝ≥0∞) ^ L.ko) / (Fintype.card F : ℝ≥0∞) ^ (L.ko + 1) := by
          gcongr
          refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
            (t := univ.filter fun z ↦ ¬ OodOK L z (nxt cs) A') fun u hu ↦ ?_)) ?_
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            exact fun h ↦ hu ⟨hI, h⟩
          · exact_mod_cast card_oodBad_le L (nxt cs) A' hgap
      _ = eOod L gO (jl n' A' L.d') := by rw [← mul_assoc, ennr_div_pow _ hq, eOod]
  refine ((readFSpec I (Inv := fun cs ↦ D1 cs ∧ OodOK L (gv zv) (nxt cs) A') h0).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun y ↦ ?_
  refine ((I.grpSpec gQ (L.kq + 1) hgQ (fun cs ↦ D1 cs ∧ OodOK L (gv zv) (nxt cs) A')
    (fun u cs ↦ (D1 cs ∧ OodOK L (gv zv) (nxt cs) A') ∧ TailBack L (cur cs) (nxt cs) W σ y A A' hi (gv zv)
      (Fin.init u) (u (Fin.last (L.kq + 1)))) (eQry L gQ (jl n' A' L.d') A) heQ fun cs hI ↦ ?_).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) heQT le_rfl le_rfl).bind' fun qv ↦ ?_
  · unfold grpE
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ gQ * ((Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) *
            (((L.t + 1) * jl n' A' L.d' : ℕ) : ℝ≥0∞) + Fintype.card F *
              ((Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) * (((A - 1 : ℕ) : ℝ≥0∞) / n) ^ L.t)) /
            (Fintype.card F : ℝ≥0∞) ^ (L.kq + 1 + 1) := by
          gcongr
          refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
            (t := univ.filter fun u : Fin (L.kq + 2) → F ↦ ¬ TailBack L (cur cs) (nxt cs)
              W σ y A A' hi (gv zv) (Fin.init u) (u (Fin.last (L.kq + 1))))
            fun u hu ↦ ?_)) ?_
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            exact fun h ↦ hu ⟨hI, h⟩
          · exact card_tbad_le L (cur cs) (nxt cs) W σ y A A' hi (gv zv) hI.2 hgap
      _ = eQry L gQ (jl n' A' L.d') A := by
          rw [mul_div_assoc, ennr_div_pow' _ hq, eQry]
  let o : List (List K) → TailOut F L.ko L.t n := fun rows ↦
    ⟨hi, gv zv, y, qPos L qv, qLam L qv, vals hi (qPos L qv) rows⟩
  refine ((Spec.ofNoMove (p := queryOpenings i (List.ofFn fun k ↦ (qPos L qv k : ℕ)))
    (Pre := fun h ↦ (D1 (commits h) ∧ OodOK L (gv zv) (nxt (commits h)) A') ∧
      TailBack L (cur (commits h)) (nxt (commits h)) W σ y A A' hi (gv zv)
        (Fin.init (gv (k := L.kq + 2) qv)) (gv (k := L.kq + 2) qv (Fin.last (L.kq + 1))))
    (Post := fun rows h ↦ (commits h).length = i + 2 ∧
      TailFacts L (cur (commits h)) (nxt (commits h)) W σ A A' (o rows)) (T := 0)
    (noMv_queryP _ _).noMove (e := 0) (by norm_num) fun h₀ hP ↦ ?_).mono (fun _ h ↦ h)
    (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun rows ↦ ?_
  · unfold escRet
    rw [retExp_queryP]
    split
    · rename_i rows hans
      rw [List.append_nil] at hans
      have hv := hread h₀ hP.1.1 (qPos L qv) rows hans hi
      have hpost : (commits (h₀ ++ [] ++ [Ev.query rows])).length = i + 2 ∧
          TailFacts L (cur (commits (h₀ ++ [] ++ [Ev.query rows])))
            (nxt (commits (h₀ ++ [] ++ [Ev.query rows]))) W σ A A' (o rows) := by
        rw [List.append_nil, commits_append_query]
        exact ⟨hP.1.1, hP.1.2, hP.2, hv⟩
      simp only [List.append_nil] at hpost
      simp [hpost]
    · exact le_rfl
  · exact Spec.ret (Post := fun o h ↦ (commits h).length = i + 2 ∧
      TailFacts L (cur (commits h)) (nxt (commits h)) W σ A A' o) (o rows)

end Tail

/-! ## The ladder -/

section Ladder

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] (WI : WtIface F) (I : ChalIface F)

/-- **The opening's facts for the extractor** on its local events `l`, the final commitments `cs`, from the
first level's weight `w`, claim `σ` and start agreement `a`: per level, `l` splits into the runs of the level's
pieces with their values, and the facts hold on them (rounds `GoodRs`; mid: `TailFacts`; final: the final
polynomial's agreement with the folded word and, for an admitted weight, its claim). -/
def OpenSem : {n ℓ : ℕ} → Lad F WI n ℓ → WI.Wt (0 + ℓ) → F → ℕ → List (ℕ × ℕ × Word) → List Ev → Prop
  | _, ℓ, .fin V, w, σ, a, cs, l =>
    ∃ rs l₁ l₂, l = l₁ ++ l₂ ∧ (roundsP I V.g ℓ).after l₁ = some (.ret rs) ∧
      GoodRs V.Fv.dom (fun t ↦ (V.par t).A) V.Fv.d ℓ V.t₀ rs (V.word (cs.take (V.i + 1))) (WI.den w) σ ∧
      ∃ s l₃ l₄, l₂ = l₃ ++ l₄ ∧ (readFs I V.Fv.nf).after l₃ = some (.ret s) ∧
        aOut (fun t ↦ (V.par t).A) a V.t₀ ℓ ≤ (agree V.Fv.dom (V.Fv.fpoly s)
          (foldsQ V.Fv.dom ℓ rs (V.word (cs.take (V.i + 1))))).card ∧
        (V.WOK w → WI.den (wFolds WI ℓ rs w) (V.Fv.fpoly s) = foldsC ℓ rs σ)
  | _, ℓ, .mid M rest, w, σ, a, cs, l =>
    ∃ rs l₁ l₂, l = l₁ ++ l₂ ∧ (roundsP I M.g ℓ).after l₁ = some (.ret rs) ∧
      GoodRs M.L.dom (fun t ↦ (M.par t).A) M.L.d ℓ M.t₀ rs (M.word (cs.take (M.i + 1))) (WI.den w) σ ∧
      ∃ o l₃ l₄, l₂ = l₃ ++ l₄ ∧ (tailP M.L I M.ht M.wd M.i M.gO M.gQ (M.vals rs)).after l₃ = some (.ret o) ∧
        TailFacts M.L (foldsQ M.L.dom ℓ rs (M.word (cs.take (M.i + 1)))) (rest.word (cs.take (M.i + 2)))
          (WI.den (wFolds WI ℓ rs w)) (foldsC ℓ rs σ) (aOut (fun t ↦ (M.par t).A) a M.t₀ ℓ) M.A' o ∧
        OpenSem rest (M.wGlue (wFolds WI ℓ rs w) o) (gluedC (foldsC ℓ rs σ) o.y o.lam o.c) M.A' cs l₄

variable {WI I} {εmax : ℝ≥0∞}

theorem split_runs {α : Type} {p : VerifierProgram α} {N N' : ℕ} {a : α} {h : List Ev}
    (r : RunAt p N N' a h) :
    h.drop N = (h.drop N).take (N' - N) ++ h.drop N' ∧ p.after ((h.drop N).take (N' - N)) = some (.ret a) := by
  obtain ⟨h1, -, h3⟩ := r
  refine ⟨?_, h3⟩
  conv_lhs => rw [← List.take_append_drop (N' - N) (h.drop N)]
  rw [List.drop_drop, show N + (N' - N) = N' by omega]

/-- **The ladder, unconditionally** (W2): from `lad.i + 1` commitments at length `N`, on acceptance the
opening's facts `OpenSem` hold on the events from `N`; every group escapes within `εmax` (`LadOK`). -/
noncomputable def ladSpecU : {n ℓ : ℕ} → (lad : Lad F WI n ℓ) → (a : ℕ) → LadOK I εmax lad a →
    (w : WI.Wt (0 + ℓ)) → (σ : F) → (N : ℕ) →
    Spec (ladP I lad w σ) (fun h ↦ (commits h).length = lad.i + 1 ∧ h.length = N)
      (fun b h ↦ b = true → OpenSem WI I lad w σ a (commits h) (h.drop N)) εmax 0 0
  | _, ℓ, .fin V, a, hok, w, σ, N => by
    have h0 : (0 : ℝ≥0∞) ≤ εmax := by positivity
    have hq : Fintype.card F ≠ 0 := Fintype.card_ne_zero
    let A := aOut (fun t ↦ (V.par t).A) a V.t₀ ℓ
    let Qf := fun cs : List (ℕ × ℕ × Word) ↦ V.word (cs.take (V.i + 1))
    let Gd := fun (rs : List (Rnd F)) (cs : List (ℕ × ℕ × Word)) ↦
      GoodRs V.Fv.dom (fun t ↦ (V.par t).A) V.Fv.d ℓ V.t₀ rs (Qf cs) (WI.den w) σ
    refine (((roundsSpecU I V.Fv.dom (fun cs ↦ cs.length = V.i + 1) false V.g hok.hg V.par ℓ V.t₀ hok.hpar
      hok.he hok.heT hok.hchain Qf (WI.den w) σ a hok.ha (fun _ _ ↦ True)).runRec N).mono
      (fun _ hp ↦ ⟨⟨hp.1, fun hb ↦ absurd hb (by decide)⟩, hp.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl
      le_rfl).bind' fun rs ↦ Spec.atLen fun N₁ ↦ ?_
    let J1 : List Ev → Prop := fun h ↦ V.i + 1 ≤ (commits h).length ∧ Gd rs (commits h) ∧
      RunAt (roundsP I V.g ℓ) N N₁ rs h
    have hJ1 : ∀ h l, J1 h → J1 (h ++ l) := fun h l hj ↦ ⟨le_commits_append hj.1 l, by
      simp only [Gd, Qf, take_commits_append hj.1 l]; exact hj.2.1, hj.2.2.append l⟩
    refine (((((readFsSpec I (Inv := fun cs ↦ cs.length = V.i + 1) (T := 0) h0 h0 V.Fv.nf).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by split_ifs <;> simp) le_rfl).runRec N₁).frameAll J1
      hJ1).mono (fun h hp ↦ ⟨⟨hp.1.1.1, hp.2⟩, le_of_eq hp.1.1.1.symm, hp.1.1.2.2, by
        rw [← hp.2]; exact hp.1.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun s ↦
      Spec.atLen fun N₂ ↦ ?_
    let cur := fun cs : List (ℕ × ℕ × Word) ↦ foldsQ V.Fv.dom ℓ rs (Qf cs)
    let J2 : List Ev → Prop := fun h ↦ J1 h ∧ RunAt (readFs I V.Fv.nf) N₁ N₂ s h
    have hJ2 : ∀ h l, J2 h → J2 (h ++ l) := fun h l hj ↦ ⟨hJ1 h l hj.1, hj.2.append l⟩
    let Ag : List Ev → Prop := fun h ↦ V.i + 1 ≤ (commits h).length ∧
      A ≤ (agree V.Fv.dom (V.Fv.fpoly s) (cur (commits h))).card
    have hAg : ∀ h l, Ag h → Ag (h ++ l) := fun h l hj ↦ ⟨le_commits_append hj.1 l, by
      simp only [cur, Qf, take_commits_append hj.1 l]; exact hj.2⟩
    have hQ : ∀ cs : List (ℕ × ℕ × Word), cs.length = V.i + 1 → Qf cs = V.word cs := fun cs hl ↦ by
      simp only [Qf, List.take_of_length_le (le_of_eq hl)]
    have Rem : Spec (I.grp V.gq V.Fv.kq >>= fun qv ↦
        queryOpenings V.i (List.ofFn fun k ↦ (fPos V.Fv qv k : ℕ)) >>= fun rows ↦
        if ∀ k, V.fv rs (fPos V.Fv qv) rows k = (V.Fv.fpoly s lane0).eval (V.Fv.dom (fPos V.Fv qv k)) then
          V.chk (wFolds WI ℓ rs w) (foldsC ℓ rs σ) s
        else VerifierProgram.fail) (fun h ↦ (commits h).length = V.i + 1)
        (fun b h ↦ (b = true → V.WOK w → WI.den (wFolds WI ℓ rs w) (V.Fv.fpoly s) = foldsC ℓ rs σ) ∧ Ag h)
        εmax 0 0 := by
      classical
      refine ((I.grpSpec V.gq V.Fv.kq hok.hgq (fun cs ↦ cs.length = V.i + 1)
        (fun u cs ↦ cs.length = V.i + 1 ∧ PosOK V.Fv A (V.Fv.fpoly s) (cur cs) u)
        (eFin V.Fv V.gq A) hok.heF fun cs hI ↦ ?_).mono (fun _ h ↦ h) (fun _ _ h ↦ h) hok.heFT le_rfl
        le_rfl).bind' fun qv ↦ ?_
      · unfold grpE
        calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ V.gq * ((Fintype.card F : ℝ≥0∞) ^ (V.Fv.kq + 1) *
                (((A - 1 : ℕ) : ℝ≥0∞) / _) ^ V.Fv.t) / (Fintype.card F : ℝ≥0∞) ^ (V.Fv.kq + 1) := by
              gcongr
              refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
                (t := univ.filter fun u ↦ ¬ PosOK V.Fv A (V.Fv.fpoly s) (cur cs) u)
                fun u hu ↦ ?_)) (card_posBad_le V.Fv A _ _)
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
              exact fun h ↦ hu ⟨hI, h⟩
          _ = eFin V.Fv V.gq A := by
              have hQ0 : (Fintype.card F : ℝ≥0∞) ^ (V.Fv.kq + 1) ≠ 0 := pow_ne_zero _ (by simp [hq])
              have hQt : (Fintype.card F : ℝ≥0∞) ^ (V.Fv.kq + 1) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
              rw [mul_comm ((Fintype.card F : ℝ≥0∞) ^ (V.Fv.kq + 1)), ← mul_assoc,
                ENNReal.mul_div_cancel_right hQ0 hQt, eFin]
      let ps := fPos V.Fv qv
      let Post : List (List K) → List Ev → Prop := fun rows h ↦
        ((commits h).length = V.i + 1 ∧ PosOK V.Fv A (V.Fv.fpoly s) (cur (commits h)) (gv qv)) ∧
          V.fv rs ps rows = fun k ↦ cur (commits h) lane0 (ps k)
      refine ((Spec.ofNoMove (p := queryOpenings V.i (List.ofFn fun k ↦ (ps k : ℕ)))
        (Pre := fun h ↦ (commits h).length = V.i + 1 ∧ PosOK V.Fv A (V.Fv.fpoly s) (cur (commits h)) (gv qv))
        (Post := Post) (T := 0) (noMv_queryP _ _).noMove (e := 0) (by norm_num) fun h₀ hP ↦ ?_).mono
        (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun rows ↦ ?_
      · unfold escRet
        rw [retExp_queryP]
        split
        · rename_i rows hans
          rw [List.append_nil] at hans
          have hv := hok.hread h₀ hP.1 rs ps rows hans
          have hpost : Post rows (h₀ ++ [] ++ [Ev.query rows]) := by
            simp only [Post, List.append_nil, commits_append_query]
            refine ⟨hP, ?_⟩
            rw [hv]
            simp only [cur, hQ _ hP.1]
          rw [List.append_nil] at hpost
          simp [hpost]
        · exact le_rfl
      · refine Spec.ite (c := ∀ k, V.fv rs ps rows k = (V.Fv.fpoly s lane0).eval (V.Fv.dom (ps k)))
          (fun hc ↦ ((chkU (V.chk (wFolds WI ℓ rs w) (foldsC ℓ rs σ) s) (V.WOK w)
            (WI.den (wFolds WI ℓ rs w) (V.Fv.fpoly s) = foldsC ℓ rs σ)
            (fun hw ↦ ⟨(Classical.choice (hok.hchk w σ hw rs s)).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
              le_rfl le_rfl⟩)).frameAll Ag hAg).mono (fun h hp ↦ ⟨trivial, ?_⟩) (fun _ _ h ↦ h) le_rfl
              le_rfl le_rfl) (fun _ ↦ Spec.fail)
        obtain ⟨⟨hl, hpos⟩, hv⟩ := hp
        refine ⟨le_of_eq hl.symm, ?_⟩
        exact agree_of_posOK hpos fun k ↦ by rw [mem_agree0]; exact (hc k).symm.trans (congrFun hv k)
    refine (Rem.frameAll J2 hJ2).mono (fun h hp ↦ ⟨hp.1.1.1, hp.1.2, by rw [← hp.2]; exact hp.1.1.2⟩)
      (fun b h hp hb ↦ ?_) le_rfl le_rfl le_rfl
    obtain ⟨⟨hcl, -, hag⟩, ⟨-, hg1, hr1⟩, hr2⟩ := hp
    obtain ⟨e1, a1⟩ := split_runs hr1
    obtain ⟨e2, a2⟩ := split_runs hr2
    exact ⟨rs, _, _, e1, a1, hg1, s, _, _, e2, a2, hag, hcl hb⟩
  | _, ℓ, .mid M rest, a, hok, w, σ, N => by
    obtain ⟨h, hrest⟩ := hok
    let Qf := fun cs : List (ℕ × ℕ × Word) ↦ M.word (cs.take (M.i + 1))
    let Gd := fun (rs : List (Rnd F)) (cs : List (ℕ × ℕ × Word)) ↦
      GoodRs M.L.dom (fun t ↦ (M.par t).A) M.L.d ℓ M.t₀ rs (Qf cs) (WI.den w) σ
    refine (((roundsSpecU I M.L.dom (fun cs ↦ cs.length = M.i + 1) false M.g h.hg M.par ℓ M.t₀ h.hpar
      h.he h.heT h.hchain Qf (WI.den w) σ a h.ha (fun _ _ ↦ True)).runRec N).mono
      (fun _ hp ↦ ⟨⟨hp.1, fun hb ↦ absurd hb (by decide)⟩, hp.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl
      le_rfl).bind' fun rs ↦ Spec.atLen fun N₁ ↦ ?_
    let J1 : List Ev → Prop := fun h ↦ M.i + 1 ≤ (commits h).length ∧ Gd rs (commits h) ∧
      RunAt (roundsP I M.g ℓ) N N₁ rs h
    have hJ1 : ∀ h l, J1 h → J1 (h ++ l) := fun h l hj ↦ ⟨le_commits_append hj.1 l, by
      simp only [Gd, Qf, take_commits_append hj.1 l]; exact hj.2.1, hj.2.2.append l⟩
    let cur := fun cs : List (ℕ × ℕ × Word) ↦ foldsQ M.L.dom ℓ rs (Qf cs)
    let nxt := fun cs : List (ℕ × ℕ × Word) ↦ rest.word (cs.take (M.i + 2))
    let A := aOut (fun t ↦ (M.par t).A) a M.t₀ ℓ
    have hword : ∀ cs : List (ℕ × ℕ × Word), cs.length = M.i + 2 → M.word cs = Qf cs := fun cs hl ↦ by
      have hd : (cs.drop (M.i + 1)).length = 1 := by simp [hl]
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hd
      have e : cs = cs.take (M.i + 1) ++ [x] := by rw [← hx, List.take_append_drop]
      have hl1 : (cs.take (M.i + 1)).length = M.i + 1 := by rw [List.length_take, hl]; omega
      rw [e, h.hstab _ x hl1]
      simp only [Qf, List.take_append_of_le_length (le_of_eq hl1.symm), List.take_take, min_self]
    refine ((((tailSpecU M.L I M.ht M.wd M.i M.gO M.gQ h.hgO h.hgQ (M.vals rs) cur nxt
      (WI.den (wFolds WI ℓ rs w)) (foldsC ℓ rs σ) A M.A'
      (fun h' hl ps rows hans hi ↦ by
        rw [h.hread rs h' hl ps rows hans hi, hword _ hl]) h.hgap h.heO h.heOT h.heQ h.heQT).runRec N₁).frameAll
      J1 hJ1).mono (fun hh hp ↦ ⟨⟨hp.1.1.1, hp.2⟩, le_of_eq hp.1.1.1.symm, hp.1.1.2.2, by
        rw [← hp.2]; exact hp.1.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun o ↦
      Spec.atLen fun N₂ ↦ ?_
    let J2 : List Ev → Prop := fun hh ↦ J1 hh ∧ M.i + 2 ≤ (commits hh).length ∧
      TailFacts M.L (cur (commits hh)) (nxt (commits hh)) (WI.den (wFolds WI ℓ rs w)) (foldsC ℓ rs σ) A M.A' o ∧
      RunAt (tailP M.L I M.ht M.wd M.i M.gO M.gQ (M.vals rs)) N₁ N₂ o hh
    have hJ2 : ∀ hh l, J2 hh → J2 (hh ++ l) := fun hh l hj ↦ ⟨hJ1 hh l hj.1, le_commits_append hj.2.1 l, by
      simp only [cur, nxt, Qf, take_commits_append hj.2.1 l,
        take_commits_append (le_trans (Nat.le_succ _) hj.2.1) l]; exact hj.2.2.1, hj.2.2.2.append l⟩
    refine ((ladSpecU rest M.A' hrest (M.wGlue (wFolds WI ℓ rs w) o)
      (gluedC (foldsC ℓ rs σ) o.y o.lam o.c) N₂).frameAll J2 hJ2).mono
      (fun hh hp ↦ ⟨⟨by rw [hp.1.1.1.1, h.hi'], hp.2⟩, hp.1.2, le_of_eq hp.1.1.1.1.symm, hp.1.1.1.2, by
        rw [← hp.2]; exact hp.1.1.2⟩) (fun b hh hp hb ↦ ?_) le_rfl le_rfl le_rfl
    obtain ⟨hq, ⟨hl1, hg1, hr1⟩, -, htf, hr2⟩ := hp
    obtain ⟨e1, a1⟩ := split_runs hr1
    obtain ⟨e2, a2⟩ := split_runs hr2
    exact ⟨rs, _, _, e1, a1, hg1, o, _, _, e2, a2, htf, hq hb⟩

end Ladder

/-! ## The deployed instance -/

/-- **The extractor's facts at a shape** (ASM's `GW` of `Stmt.openGood6`): at `P17`'s opening constants, the
history splits at `N₀` after one commitment, the rest is an accepting run of `whirP cl` for some claim
`cl`, and `OpenSem` holds on it (level 0 from W1's start agreement `526656 − 6`); elsewhere `True`. -/
def GWD (sh : Shape) (h : List Ev) : Prop :=
  openKey sh = true → ∃ N₀ cl, (commits (h.take N₀)).length = 1 ∧
    (whirP cl).after (h.drop N₀) = some (.ret true) ∧
    OpenSem WtE chalE2 ladD (w₀ cl) cl.2 (526656 - 6) (commits h) (h.drop N₀)

/-- **`Stmt.openGood6 GWD (whirAt whirP)`** (unfolded; ASM's `Stmt.openGood6` is on `lvm6/W2-asm`): from
one commitment the deployed opening accepts only on histories with `GWD`, each group's escape at most `εI`. -/
theorem openGood_W1 : ∀ sh cl, Nonempty (Spec (whirAt whirP sh cl) (fun h ↦ (commits h).length = 1)
    (fun b h ↦ b = true → GWD sh h) Lvm6.εI 0 0) := by
  intro sh cl
  by_cases hk : openKey sh = true
  · have e : whirAt whirP sh cl = whirP cl := ite_eq_left hk
    rw [e]
    refine ⟨Spec.atLen fun N ↦ ?_⟩
    have hR : ∀ h₀ l b, ((commits h₀).length = ladD.i + 1 ∧ h₀.length = N) →
        (whirP cl).Reach h₀ l → (whirP cl).after l = some (.ret b) →
        (whirP cl).after ((h₀ ++ l).drop N) = some (.ret b) ∧ (commits ((h₀ ++ l).take N)).length = 1 :=
      fun h₀ l b hp _ ha ↦ by
        refine ⟨by rw [← hp.2]; simpa using ha, ?_⟩
        have hi : ladD.i + 1 = 1 := rfl
        rw [← hp.2]; simpa [hi] using hp.1
    exact (((ladSpecU ladD (526656 - 6) ladD_ok (w₀ cl) cl.2 N).mono (fun _ hp ↦ hp) (fun _ _ hp ↦ hp)
      le_rfl le_rfl le_rfl).traceAnd (fun b h ↦ (whirP cl).after (h.drop N) = some (.ret b) ∧
        (commits (h.take N)).length = 1) hR).mono (fun _ hp ↦ hp)
          (fun b h hp hb _ ↦ ⟨N, cl, hp.2.2, hb ▸ hp.2.1, hp.1 hb⟩) le_rfl le_rfl le_rfl
  · have e : whirAt whirP sh cl = .fail := ite_eq_right hk
    rw [e]
    exact ⟨Spec.fail⟩

/-- **`GWD` at a given claim** (RG's F-RG-1): the opening's facts for the claim `cl` it was run on, so that the
extractor can match them with the ring phase's batched claim (ASM's `Stmt.openGoodC`). -/
def GWDc (sh : Shape) (cl : StackClaim6) (h : List Ev) : Prop :=
  openKey sh = true → ∃ N₀, (commits (h.take N₀)).length = 1 ∧
    (whirP cl).after (h.drop N₀) = some (.ret true) ∧
    OpenSem WtE chalE2 ladD (w₀ cl) cl.2 (526656 - 6) (commits h) (h.drop N₀)

theorem GWDc.gwD {sh : Shape} {cl : StackClaim6} {h : List Ev} (hc : GWDc sh cl h) : GWD sh h :=
  fun hk ↦ let ⟨N, h1, h2, h3⟩ := hc hk; ⟨N, cl, h1, h2, h3⟩

/-- **`Stmt.openGoodC GWDc (whirAt whirP)`** (unfolded): `openGood_W1` with the claim as a parameter. -/
theorem openGood_W1C : ∀ sh cl, Nonempty (Spec (whirAt whirP sh cl) (fun h ↦ (commits h).length = 1)
    (fun b h ↦ b = true → GWDc sh cl h) Lvm6.εI 0 0) := by
  intro sh cl
  by_cases hk : openKey sh = true
  · have e : whirAt whirP sh cl = whirP cl := ite_eq_left hk
    rw [e]
    refine ⟨Spec.atLen fun N ↦ ?_⟩
    have hR : ∀ h₀ l b, ((commits h₀).length = ladD.i + 1 ∧ h₀.length = N) →
        (whirP cl).Reach h₀ l → (whirP cl).after l = some (.ret b) →
        (whirP cl).after ((h₀ ++ l).drop N) = some (.ret b) ∧ (commits ((h₀ ++ l).take N)).length = 1 :=
      fun h₀ l b hp _ ha ↦ by
        refine ⟨by rw [← hp.2]; simpa using ha, ?_⟩
        have hi : ladD.i + 1 = 1 := rfl
        rw [← hp.2]; simpa [hi] using hp.1
    exact (((ladSpecU ladD (526656 - 6) ladD_ok (w₀ cl) cl.2 N).mono (fun _ hp ↦ hp) (fun _ _ hp ↦ hp)
      le_rfl le_rfl le_rfl).traceAnd (fun b h ↦ (whirP cl).after (h.drop N) = some (.ret b) ∧
        (commits (h.take N)).length = 1) hR).mono (fun _ hp ↦ hp)
          (fun b h hp hb _ ↦ ⟨N, hp.2.2, hb ▸ hp.2.1, hp.1 hb⟩) le_rfl le_rfl le_rfl
  · have e : whirAt whirP sh cl = .fail := ite_eq_right hk
    rw [e]
    exact ⟨Spec.fail⟩

end Lvm6.Whir
