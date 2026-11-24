-- New for lvm6 (WP W1, second slice). The ladder of WHIR levels as one specification of the
-- verifier language, after leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Spec.lean`
-- (`LadderOK`, `whirLevelsG`, `levelsSpec`) @ fdb317982. Changed: the levels are a dependent
-- list (`Lad`: each level has its own column count, lane count and code facts `TailIface`), the
-- verifier's weight is data (`WtIface`) whose meaning the specification tracks, and the descent
-- predicate is `True` (the opening's precondition is doom over the whole level-0 ball).
import Lvm6WhirFinal
import LvmFrontMech

/-!
# The ladder of levels (W1)

* `MidLv F WI n ℓ n' ℓ'`: a level with a next one: its interface `L` (`TailIface`), grinds, round
  parameters, the commitment index `i`, the next threshold `A'`, the verifier's values `vals` and
  glue `wGlue`, the level's word `word` (read from the commitments) and the weights it admits
  (`WOK`). `FinLv F WI n ℓ`: the final level (`FinIface`, `fv`, `chk`).
* `Lad F WI n ℓ`: **the ladder**, a final level or a level followed by a ladder.
* `ladP I lad w σ`: the program: each level's rounds, then its interface (or the final tail), the
  weight and the claim carried as the verifier computes them (`wFolds`, `wGlue`, `foldsC`,
  `gluedC`).
* `MidOK`, `FinOK`, `LadOK`: the hypotheses, per level (rounds, groups' escapes, reads) and across
  levels (indices, the next domain and degree, the glued weight admitted by the next level).
* **`ladSpec`**: from the descent invariant (predicate `True`) at the first level's word, every
  group escapes within `εmax`, and the program rejects.
* **`openSpecL`**: the opening in doom form: if no decoding of a tuple of the first level's ball
  (degree `≤ d`, agreement `≥ a` with the level's word) satisfies the claim, the program rejects.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
  LeanVM.Protocol.Whir.AffineCombiner LeanVM.Protocol.EndToEnd.Front
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The levels -/

/-- **A level with a next one** (`n` columns, `ℓ` lane variables; the next `n'`, `ℓ'`). -/
structure MidLv (F : Type) [Field F] [Fintype F] [DecidableEq F] (WI : WtIface F)
    (n ℓ n' ℓ' : ℕ) where
  L : TailIface F n n' (0 + ℓ')
  /-- The grinds: fold pairs, the next level's OOD point (`g_ood[i+1]`), the query message. -/
  g : ℕ
  gO : ℕ
  gQ : ℕ
  /-- The next commitment's shape, this level's commitment index, the first round's index. -/
  ht : ℕ
  wd : ℕ
  i : ℕ
  t₀ : ℕ
  par : ℕ → RoundPar
  /-- The next level's threshold. -/
  A' : ℕ
  vals : List (Rnd F) → List F → (Fin L.t → Fin n) → List (List K) → Fin L.t → F
  /-- The verifier's glued weight. -/
  wGlue : WI.Wt 0 → TailOut F L.ko L.t n → WI.Wt (0 + ℓ')
  /-- The level's word, read from the commitments. -/
  word : List (ℕ × ℕ × Word) → Wd F n (0 + ℓ)
  /-- The weights (as the verifier holds them) the level admits. -/
  WOK : WI.Wt (0 + ℓ) → Prop

/-- **The final level** (`n` columns, `ℓ` lane variables). -/
structure FinLv (F : Type) [Field F] [Fintype F] [DecidableEq F] (WI : WtIface F) (n ℓ : ℕ) where
  Fv : FinIface F n
  g : ℕ
  gq : ℕ
  i : ℕ
  t₀ : ℕ
  par : ℕ → RoundPar
  fv : List (Rnd F) → (Fin Fv.t → Fin n) → List (List K) → Fin Fv.t → F
  chk : WI.Wt 0 → F → List F → VerifierProgram Bool
  word : List (ℕ × ℕ × Word) → Wd F n (0 + ℓ)
  WOK : WI.Wt (0 + ℓ) → Prop

/-- **The ladder of levels.** -/
inductive Lad (F : Type) [Field F] [Fintype F] [DecidableEq F] (WI : WtIface F) :
    ℕ → ℕ → Type 1 where
  | fin {n ℓ : ℕ} (V : FinLv F WI n ℓ) : Lad F WI n ℓ
  | mid {n ℓ n' ℓ' : ℕ} (M : MidLv F WI n ℓ n' ℓ') (rest : Lad F WI n' ℓ') : Lad F WI n ℓ

variable {WI : WtIface F}

namespace Lad

variable {n ℓ : ℕ}

/-- The first level's domain. -/
def dom : Lad F WI n ℓ → (Fin n ↪ F)
  | .fin V => V.Fv.dom
  | .mid M _ => M.L.dom

/-- The first level's degree. -/
def d : Lad F WI n ℓ → ℕ
  | .fin V => V.Fv.d
  | .mid M _ => M.L.d

/-- The first level's commitment index. -/
def i : Lad F WI n ℓ → ℕ
  | .fin V => V.i
  | .mid M _ => M.i

/-- The first level's word. -/
def word : Lad F WI n ℓ → List (ℕ × ℕ × Word) → Wd F n (0 + ℓ)
  | .fin V => V.word
  | .mid M _ => M.word

/-- The weights the first level admits. -/
def WOK : Lad F WI n ℓ → WI.Wt (0 + ℓ) → Prop
  | .fin V => V.WOK
  | .mid M _ => M.WOK

end Lad

variable (I : ChalIface F)

/-- **The ladder's program**: each level's rounds and interface, the weight and the claim as the
verifier computes them; the final level's tail. -/
def ladP : {n ℓ : ℕ} → Lad F WI n ℓ → WI.Wt (0 + ℓ) → F → VerifierProgram Bool
  | _, _, .fin V, w, σ => finP WI I V.Fv V.g V.gq V.i _ V.fv V.chk w σ
  | _, ℓ, .mid M rest, w, σ =>
    roundsP I M.g ℓ >>= fun rs ↦ tailP M.L I M.ht M.wd M.i M.gO M.gQ (M.vals rs) >>= fun o ↦
      ladP rest (M.wGlue (wFolds WI ℓ rs w) o) (gluedC (foldsC ℓ rs σ) o.y o.lam o.c)

/-! ## The hypotheses -/

variable (εmax : ℝ≥0∞)

/-- **A level's hypotheses**, from threshold `a`, the next level's index `i'`, domain `dom'`,
degree `d'`, word `word'` and admitted weights `WOK'`. -/
structure MidOK {n ℓ n' ℓ' : ℕ} (M : MidLv F WI n ℓ n' ℓ') (a i' : ℕ) (dom' : Fin n' ↪ F)
    (d' : ℕ) (WOK' : WI.Wt (0 + ℓ') → Prop) : Prop where
  hg : M.g ≤ I.gmax
  hgO : M.gO ≤ I.gmax
  hgQ : M.gQ ≤ I.gmax
  hpar : ∀ s, M.t₀ ≤ s → s < M.t₀ + ℓ → RoundOK (Fintype.card F) n M.L.d (M.par s)
  he : ∀ s, M.t₀ ≤ s → s < M.t₀ + ℓ → eRound F M.g (M.par s) < 1
  heT : ∀ s, M.t₀ ≤ s → s < M.t₀ + ℓ → eRound F M.g (M.par s) ≤ εmax
  hchain : ∀ s, M.t₀ ≤ s → s + 1 < M.t₀ + ℓ → (M.par s).A ≤ (M.par (s + 1)).A - 1
  ha : 0 < ℓ → a ≤ (M.par M.t₀).A - 1
  /-- The level's word survives the next commitment. -/
  hstab : ∀ cs c, cs.length = M.i + 1 → M.word (cs ++ [c]) = M.word cs
  /-- `vals` reads the folded word minus the high part at the queried columns. -/
  hread : ∀ rs h, (commits h).length = M.i + 2 → ∀ ps rows,
    answer h M.i (List.ofFn fun k ↦ (ps k : ℕ)) = some rows → ∀ hi,
      M.vals rs hi ps rows = fun k ↦ foldsQ M.L.dom ℓ rs (M.word (commits h)) lane0 (ps k) -
        (M.L.hp hi lane0).eval (M.L.dom (ps k))
  hgap : n' * M.L.d' < M.A' * M.A'
  heO : eOod M.L M.gO (jl n' M.A' M.L.d') < 1
  heOT : eOod M.L M.gO (jl n' M.A' M.L.d') ≤ εmax
  heQ : eQry M.L M.gQ (jl n' M.A' M.L.d') (aOut (fun s ↦ (M.par s).A) a M.t₀ ℓ) < 1
  heQT : eQry M.L M.gQ (jl n' M.A' M.L.d') (aOut (fun s ↦ (M.par s).A) a M.t₀ ℓ) ≤ εmax
  /-- The next level: index, domain, degree, word. -/
  hi' : i' = M.i + 1
  hdom' : dom' = M.L.dom'
  hd' : d' = M.L.d'
  /-- An admitted weight, folded, ignores the high part. -/
  hWH : ∀ w, M.WOK w → ∀ rs hi, WI.den (wFolds WI ℓ rs w) (M.L.hp hi) = 0
  /-- **The cross-level fact**: an admitted weight, folded and glued, is admitted by the next
  level (for the deployed code: it factors through the message, which kills the next high part). -/
  hglue : ∀ w, M.WOK w → ∀ rs (o : TailOut F M.L.ko M.L.t n), WOK' (M.wGlue (wFolds WI ℓ rs w) o)
  /-- The verifier's glue means `glued` on admitted weights. -/
  den_wGlue : ∀ w, M.WOK w → ∀ rs (o : TailOut F M.L.ko M.L.t n),
    WI.den (M.wGlue (wFolds WI ℓ rs w) o) = glued M.L (WI.den (wFolds WI ℓ rs w)) o.z o.lam o.ps

/-- **The final level's hypotheses**, from threshold `a`. -/
structure FinOK {n ℓ : ℕ} (V : FinLv F WI n ℓ) (a : ℕ) : Prop where
  hg : V.g ≤ I.gmax
  hgq : V.gq ≤ I.gmax
  hpar : ∀ s, V.t₀ ≤ s → s < V.t₀ + ℓ → RoundOK (Fintype.card F) n V.Fv.d (V.par s)
  he : ∀ s, V.t₀ ≤ s → s < V.t₀ + ℓ → eRound F V.g (V.par s) < 1
  heT : ∀ s, V.t₀ ≤ s → s < V.t₀ + ℓ → eRound F V.g (V.par s) ≤ εmax
  hchain : ∀ s, V.t₀ ≤ s → s + 1 < V.t₀ + ℓ → (V.par s).A ≤ (V.par (s + 1)).A - 1
  ha : 0 < ℓ → a ≤ (V.par V.t₀).A - 1
  /-- `fv` reads the level's word folded by the rounds. -/
  hread : ∀ h, (commits h).length = V.i + 1 → ∀ rs ps rows,
    answer h V.i (List.ofFn fun k ↦ (ps k : ℕ)) = some rows →
      V.fv rs ps rows = fun k ↦ foldsQ V.Fv.dom ℓ rs (V.word (commits h)) lane0 (ps k)
  /-- The terminal check rejects a final polynomial that violates the folded claim. -/
  hchk : ∀ w σ, V.WOK w → ∀ rs s, Nonempty (Spec (V.chk (wFolds WI ℓ rs w)
    (foldsC ℓ rs σ) s) (fun _ ↦ WI.den (wFolds WI ℓ rs w) (V.Fv.fpoly s) ≠ foldsC ℓ rs σ)
    (fun b _ ↦ b = false) εmax 0 0)
  heF : eFin V.Fv V.gq (aOut (fun s ↦ (V.par s).A) a V.t₀ ℓ) < 1
  heFT : eFin V.Fv V.gq (aOut (fun s ↦ (V.par s).A) a V.t₀ ℓ) ≤ εmax

/-- **The ladder's hypotheses** from threshold `a` at its first level. -/
def LadOK : {n ℓ : ℕ} → Lad F WI n ℓ → ℕ → Prop
  | _, _, .fin V, a => FinOK I εmax V a
  | _, _, .mid M rest, a => MidOK I εmax M a rest.i rest.dom rest.d rest.WOK ∧ LadOK rest M.A'

/-! ## The specification -/

variable {I εmax}

/-- **The ladder of WHIR levels, with the descent invariant** (BLUEPRINT T3, W1; leanVM
`levelsSpec`): from the descent invariant (predicate `True`) for the first level's word at `a`,
with an admitted weight, every group escapes within `εmax` and the program rejects. -/
noncomputable def ladSpec : {n ℓ : ℕ} → (lad : Lad F WI n ℓ) → (a : ℕ) → LadOK I εmax lad a →
    (w : WI.Wt (0 + ℓ)) → (σ : F) → lad.WOK w →
    Spec (ladP I lad w σ) (fun h ↦ (commits h).length = lad.i + 1 ∧
      TViol lad.dom (lad.word (commits h)) (WI.den w) σ a lad.d (fun _ ↦ True))
      (fun b _ ↦ b = false) εmax 0 0
  | _, ℓ, .fin V, a, hok, w, σ, hw =>
    finSpec WI I V.Fv V.g V.gq V.i ℓ V.t₀ hok.hg hok.hgq V.par hok.hpar hok.he hok.heT hok.hchain
      V.fv V.chk V.word hok.hread w σ a hok.ha (hok.hchk w σ hw) hok.heF hok.heFT
  | _, ℓ, .mid M rest, a, hok, w, σ, hw => by
    obtain ⟨h, hrest⟩ := hok
    refine ((roundsSpecJ I M.L.dom (fun cs ↦ cs.length = M.i + 1) M.g h.hg M.par ℓ M.t₀ h.hpar
      h.he h.heT h.hchain M.word (WI.den w) σ a h.ha (fun _ _ ↦ True)).mono (fun _ hp ↦ hp)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun rs ↦ ?_
    refine ((tailSpecJ M.L I M.ht M.wd M.i M.gO M.gQ h.hgO h.hgQ (M.vals rs) (fun _ ↦ True)
      (fun cs ↦ foldsQ M.L.dom ℓ rs (M.word cs)) rest.word (WI.den (wFolds WI ℓ rs w))
      (h.hWH w hw rs) (foldsC ℓ rs σ)
      (aOut (fun s ↦ (M.par s).A) a M.t₀ ℓ) M.A' (fun _ _ ↦ True)
      (fun cs c hl _ ↦ ⟨by rw [h.hstab cs c hl], rfl, trivial⟩)
      (fun h' hl _ ps rows hans hi ↦ h.hread rs h' hl ps rows hans hi) h.hgap h.heO h.heOT h.heQ
      h.heQT).mono (fun _ hp ↦ ⟨hp.1, trivial, by
        rw [den_wFolds]
        exact hp.2.mono le_rfl le_rfl fun U _ ↦ pulls_true M.L.dom _ _ _ _ _ _ _
          (fun _ ↦ trivial) U⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun o ↦ ?_
    refine (ladSpec rest M.A' hrest (M.wGlue (wFolds WI ℓ rs w) o)
      (gluedC (foldsC ℓ rs σ) o.y o.lam o.c) ?_).mono (fun hh hp ↦ ?_) (fun _ _ hp ↦ hp) le_rfl
      le_rfl le_rfl
    · exact h.hglue w hw rs o
    · obtain ⟨⟨hl, -⟩, hT⟩ := hp
      refine ⟨by rw [hl, h.hi'], ?_⟩
      rw [h.den_wGlue w hw rs o, h.hdom', h.hd']
      exact hT.mono le_rfl le_rfl fun _ _ _ ↦ trivial

/-! ## The opening in doom form -/

/-- **The first level's ball**: the objects decoded (`dec`, e.g. the stack a tuple's low part
reads) from the tuples of degree `≤ d` that agree with the first level's word (`lad.word`, read
from the history's commitments) on at least `a` columns. -/
def ball {Stk : Type} {n ℓ : ℕ} (lad : Lad F WI n ℓ) (dec : Tup F (0 + ℓ) → Stk) (a : ℕ)
    (h : List Ev) : Set Stk :=
  dec '' {U | DegLE lad.d U ∧ a ≤ (agree lad.dom U (lad.word (commits h))).card}

/-- **The opening in doom form** (S's `stackedSpec` shape with the ball as the candidates): if the
weight `w` and claim `σ` on a tuple of the ball imply `Holds` of its decoding (`hhold`), then from
"no object of the ball satisfies `Holds`" on a history whose commitments end at the first
level's, the program rejects. -/
theorem openSpecL {Stk : Type} {n ℓ : ℕ} (lad : Lad F WI n ℓ) (a : ℕ) (hok : LadOK I εmax lad a)
    (dec : Tup F (0 + ℓ) → Stk) (Holds : Stk → Prop) (w : WI.Wt (0 + ℓ)) (σ : F)
    (hw : lad.WOK w)
    (hhold : ∀ cs U, DegLE lad.d U → a ≤ (agree lad.dom U (lad.word cs)).card →
      WI.den w U = σ → Holds (dec U)) :
    Nonempty (Spec (ladP I lad w σ)
      (fun h ↦ (commits h).length = lad.i + 1 ∧ Doomed (ball lad dec a) Holds h)
      (fun b _ ↦ b = false) εmax 0 0) :=
  ⟨(ladSpec lad a hok w σ hw).mono (fun _ hp ↦ ⟨hp.1, fun U hU hag _ hWU ↦
    hp.2 (dec U) ⟨U, ⟨hU, hag⟩, rfl⟩ (hhold _ U hU hag hWU)⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl
    le_rfl⟩

end Lvm6.Whir
