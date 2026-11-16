-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/LevelMidSpec.lean` (formal rev 40f877dc) as
-- `LvmWhirLevelMidSpec` for lvm (WP-7). Changed for the unique-decoding regime: no out-of-domain group and no proof
-- of work (`hεO`, `hOlt`, `hεQ`'s `2^-17` go); the query group's escape is `eQueryUd`, its one candidate from the
-- next code's list bound `P'.listMax ≤ 1` (`MidHyp.hL'`); the predicates are read on the opening's view
-- `viewC c₀ n₀ (commits h)` and the opening is of commitment `cidx c₀ n₀ i`.
/-
  LeanVM.Protocol.Whir.Sound.LevelMidSpec

  The doom-calculus specification of a WHIR level with a next commitment, unique decoding.
-/
import LvmWhirProg
import LvmWhirGroupEscape

-- ===== merged from `LvmWhirGrind` (GOLF module merge: `LvmWhirGrind.lean` is now a stub importing `LvmWhirLevelMidSpec`) =====
section
-- New for lvm2 (WP PI-GRIND). The escape of a WHIR query group with in-answer grinding.
/-
  LeanVM.Protocol.Whir.Sound.Grind

  The proof of work before a level's positions (`powCheck g`, `LvmWhirProg`) divides the query
  group's escape probability by `2^g`.
-/

/-!
# The query group with a proof of work

With `g > 0` a WHIR level reads the nonce (a prover move, so the query group starts at the
boundary it ends) and then draws the PoW challenge `c`, rejecting unless its top `g` bits are zero
(`powOK g c`: `int(c) < 2^(192 − g)`). The PoW challenge, the positions, `λ` and the openings are
one group (no prover move between them), so the Fiat–Shamir compiler charges them as one event at
the nonce query (`LvmPotential`), and the group's escape is the joint one:

* `card_powOK`: exactly `2^(192 − g)` challenges pass (`int` is a bijection onto `[0, 2^192)`);
* `escRet_powCheck_le`: if the rest of the group escapes with probability at most `e` from every
  history with the same commitments, the group with the proof of work escapes with probability
  at most `2^-g · e` (the rest of the group does not read the PoW challenge);
* `escRet_queryFragG_le_ud`, `escRet_queryFragG_le_finViol`: the query groups of
  `LvmWhirGroupEscape` with the proof of work, at `2^-g · eQueryUd` and `2^-g · eQueryFinal`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier VerifierProgram Finset

section

/-- **The passing challenges**: `2^(192 − g)` of the `2^192`, for `g ≤ 192`. -/
theorem card_powOK (g : ℕ) (hg : g ≤ 192) :
    (univ.filter fun c : E ↦ powOK g c).card = 2 ^ (192 - g) := by
  have h1 : (univ.filter fun c : E ↦ powOK g c).card =
      (univ.filter fun x : Fin ((2 ^ 64) ^ 3) ↦ (x : ℕ) < 2 ^ (192 - g)).card := by
    rw [← Finset.card_map eNatEquiv.toEmbedding]
    congr 1
    ext x
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [powOK, ← eNatEquiv_val, Equiv.apply_symm_apply]
  rw [h1, Fin.card_filter_val_lt]
  refine min_eq_right ?_
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The fraction of passing challenges is `2^-g`. -/
theorem frac_powOK (g : ℕ) (hg : g ≤ 192) :
    (Fintype.card E : ENNReal)⁻¹ * ((univ.filter fun c : E ↦ powOK g c).card : ENNReal) =
      (2 : ENNReal)⁻¹ ^ g := by
  rw [card_powOK g hg, card_E]
  have h : (2 : ENNReal) ^ 192 = 2 ^ g * 2 ^ (192 - g) := by
    rw [← pow_add, Nat.add_sub_cancel' hg]
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, h, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

open Classical in
/-- **The proof of work divides a group's escape by `2^g`.** -/
theorem escRet_powCheck_le {α : Type} (g : ℕ) (hg : g ≤ 192) (Post : α → List Ev → Prop)
    (h₀ : List Ev) (q : VerifierProgram α) (e : ENNReal)
    (hq : ∀ h, commits h = commits h₀ → escRet Post h [] q ≤ e) :
    escRet Post h₀ [] ((powCheck g).bind fun _ ↦ q) ≤ (2 : ENNReal)⁻¹ ^ g * e := by
  by_cases g0 : g = 0
  · subst g0
    simpa [powCheck] using hq h₀ rfl
  simp only [powCheck, g0, ↓reduceIte]
  rw [VerifierProgram.bind_assoc]
  change retExp _ h₀ [] (VerifierProgram.sample fun c ↦
    ((VerifierProgram.require (powOK g c)).bind fun _ ↦ q)) ≤ _
  simp only [retExp, List.nil_append]
  have hc : ∀ c : E, retExp (fun a h ↦ if Post a h then 0 else 1) h₀ [Ev.sample c]
      ((VerifierProgram.require (powOK g c)).bind fun _ ↦ q) ≤ if powOK g c then e else 0 := by
    intro c
    by_cases hp : powOK g c
    · simp only [VerifierProgram.require, hp, ↓reduceIte, VerifierProgram.ret_bind]
      rw [show [Ev.sample c] = [Ev.sample c] ++ [] from rfl, retExp_shift]
      exact hq _ (commits_append_sample h₀ c)
    · simp [VerifierProgram.require, hp, VerifierProgram.bind, retExp]
  calc (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, _
      ≤ (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, (if powOK g c then e else 0) := by
        gcongr with c; exact hc c
    _ = (Fintype.card E : ENNReal)⁻¹ * ((univ.filter fun c : E ↦ powOK g c).card : ENNReal) * e := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_assoc]
    _ = (2 : ENNReal)⁻¹ ^ g * e := by rw [frac_powOK g hg]

/-! ## The query groups -/

/-- The query group with the proof of work. -/
def queryFragG (g per depth t i : ℕ) : VerifierProgram (List ℕ × E × List (List K)) :=
  (powCheck g).bind fun _ ↦ queryFrag per depth t i

theorem noMoves_powCheck (g : ℕ) : NoMoves (powCheck g) := by
  unfold powCheck
  split
  · exact NoMoves.ret ()
  · refine noMoves_sampleE.bind fun c ↦ ?_
    unfold VerifierProgram.require
    split
    · exact NoMoves.ret ()
    · exact NoMoves.fail

theorem noMoves_queryFragG (g per depth t i : ℕ) : NoMoves (queryFragG g per depth t i) :=
  (noMoves_powCheck g).bind fun _ ↦ noMoves_queryFrag per depth t i

open Classical in
/-- **The query group of a level with a next commitment, with the proof of work.** -/
theorem escRet_queryFragG_le_ud (g : ℕ) (hg : g ≤ 192) (P P' : LevelCode) {ℓ' : ℕ}
    (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hone : (iList P'.code P'.thr Q').card ≤ 1)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      Viol P' Q' (fun r ↦ Φ r + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFragG g per (P.κ + P.R) t c) ≤
      (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' t := by
  refine escRet_powCheck_le g hg _ h₀ _ _ fun h hh ↦ ?_
  rw [← hh] at hW
  refine escRet_queryFrag_le_ud P P' hκ per t c hper hpd h hW Q' C Φ σ hviol hone
    (fun g cs ↦ J g cs) fun qs lam hr hlen hv ↦ ?_
  rw [hh]
  exact hJ qs lam hr hlen hv

open Classical in
/-- **The query group of the final level, with the proof of work.** -/
theorem escRet_queryFragG_le_finViol (g : ℕ) (hg : g ≤ 192) (P : LevelCode) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (hD : FinViol P C Φ σ G)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      ∑ x, (Φ (bitsL x) + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length)
          (bitsL x)) * G x ≠
        σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k] →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFragG g per (P.κ + P.R) t c) ≤
      (2 : ENNReal)⁻¹ ^ g * eQueryFinal P t := by
  refine escRet_powCheck_le g hg _ h₀ _ _ fun h hh ↦ ?_
  rw [← hh] at hW
  refine escRet_queryFrag_le_finViol P per t c hper hpd h hW C Φ σ G hD
    (fun g cs ↦ J g cs) fun qs lam hr hlen hv ↦ ?_
  rw [hh]
  exact hJ qs lam hr hlen hv

/-! ## The moves before the proof of work, and the discount -/

/-- The discount `2^-g` only lowers an escape. -/
theorem grind_disc_le (g : ℕ) (x : ENNReal) : (2 : ENNReal)⁻¹ ^ g * x ≤ x :=
  mul_le_of_le_one_left' (pow_le_one₀ zero_le (by norm_num))

/-- **The separating challenge and the nonce keep a commitment invariant** (lead and follower's
allowance `T`; at `g = 0` there is nothing). -/
noncomputable def grindPreInv (I : CInv) (g : ℕ) {εmax T : ENNReal} (hT : T ≤ εmax) :
    Spec (grindPre g) (fun h ↦ I (commits h)) (fun _ h ↦ I (commits h)) εmax T T :=
  Spec.ite (fun _ ↦ (Spec.ret (Post := fun _ h ↦ I (commits h)) ()).congr
      (VerifierProgram.pure_eq ()).symm)
    (fun _ ↦ ((Spec.sampleE (Pre := fun h ↦ I (commits h)) (Post := fun _ h ↦ I (commits h))
        (T := 0) 0 fun h₀ hI ↦ by simp [hI]).bind' fun _ ↦
      (readInv I (T := T) hT).bind' fun _ ↦
        (Spec.ret (Post := fun _ h ↦ I (commits h)) ()).congr
          (VerifierProgram.pure_eq ()).symm).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
          (by simp) le_rfl)

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirGrind` =====

-- ===== merged from `LvmWhirLevelMid` (GOLF module merge: `LvmWhirLevelMid.lean` is now a stub importing `LvmWhirLevelMidSpec`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/LevelMid.lean` (formal rev 40f877dc) as
-- `LvmWhirLevelMid` for lvm (WP-7). Changed for the unique-decoding regime: the level is lvm's (`whirLevelsUd`: no
-- out-of-domain step, no proof of work, positions `per` per challenge, the opening of commitment `cidx c₀ n₀ i`),
-- so `OodC` is cut, the glue `glueLv` has one claim (leanVM's final-level `glueFin`, here for every level) and
-- `GlueC` follows `MidC` directly. The doom predicates are leanVM's, read on the opening's view of the commitments.
/-
  LeanVM.Protocol.Whir.Sound.LevelMid

  A WHIR level with a next commitment in the unique-decoding regime: the fold rounds, the
  commitment of the next oracle, the query group with `λ`, and the glued claim handed to the next
  level.
-/

/-!
# A level with a next commitment

`whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w i (level :: next :: rest) s` (lvm's loop body) is, definitionally,
`midProg`: the fold rounds, then `midTail` (commitment, the moves before the proof of work and the
proof of work (`grindPre g`, `powCheck g`; nothing at `g = 0`), positions, `λ`, opening, query intro
polynomial, glue, next level).

Doom along the level (all functions of the opening's view `cs` of the commitments and of the
values in scope):

* `AfterFold r cs`: `A(i, ℓ)` for the state and challenges `r` returned by the fold rounds;
* `MidC r cs`: after the commitment of the next oracle (`cs = cs₀ ++ [next word]`);
* `GlueC r g cs`: after the query group `g = (positions, λ, rows)`: every member of the next list
  violates the glued claim; with the query intro polynomial this is `LevelPre` of the next level
  (`levelPre_next`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-! ## The program -/

section Program

variable (μ ℓ₀ per c₀ n₀ g : ℕ) (dir : Bool) (w : List E → E) (i : ℕ) (level next : Whir.Level)
  (rest : List Whir.Level)

/-- The enforced sum of a level's opened rows. -/
def enfOf (lf : List E) (qs : List ℕ) (lam : E) (words : List (List K)) : E :=
  enforcedSum (if i = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow) lf
    (powers lam qs.length)

/-- The state glued at the end of a level: the batched consistency claims with `λ` (leanVM's
final-level glue; lvm glues it on every level). -/
def glueLv (r : WhirStateT × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) : WhirStateT :=
  glueT lam r.1 [(enfOf i r.2 qs lam words, hq,
    fun x ↦ Verifier.inducedWeight (μ - r.1.folds.length) qs (powers lam qs.length) x)]

/-- After the query group: the query intro polynomial, then the next level. -/
def midFinish (r : WhirStateT × List E) (qs : List ℕ) (lam : E) (words : List (List K)) :
    VerifierProgram Unit :=
  (sumcheckRoundPoly 3 (enfOf i r.2 qs lam words) none).bind fun hq ↦
    whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) (glueLv μ i r qs lam words hq)

/-- After the fold rounds. -/
def midTail (r : WhirStateT × List E) : VerifierProgram Unit :=
  (readCommitment (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)).bind
    fun _ ↦
  (grindPre g).bind fun _ ↦ (powCheck g).bind fun _ ↦
  (samplePositions per (μ - r.1.folds.length + level.logInvRate) level.queries).bind fun qs ↦
  sampleChallenge.bind fun lam ↦ (queryOpenings (cidx c₀ n₀ i) qs).bind fun words ↦
    midFinish μ ℓ₀ per c₀ n₀ g dir w i next rest r qs lam words

/-- The level, unfolded. -/
def midProg (s : WhirStateT) : VerifierProgram Unit :=
  (foldRoundsT level.fold s []).bind fun r ↦ midTail μ ℓ₀ per c₀ n₀ g dir w i level next rest r

/-- **`whirLevelsUd` on a level with a next commitment is `midProg`.** -/
theorem whirLevels_mid (s : WhirStateT) :
    whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w i (level :: next :: rest) s =
      midProg μ ℓ₀ per c₀ n₀ g dir w i level next rest s := rfl

/-- The query group as one fragment. -/
theorem query_bind (c d t : ℕ) (K : List ℕ → E → List (List K) → VerifierProgram Unit) :
    ((samplePositions per d t).bind fun qs ↦ sampleChallenge.bind fun lam ↦
      (queryOpenings c qs).bind fun words ↦ K qs lam words) =
      (queryFrag per d t c).bind fun g ↦ K g.1 g.2.1 g.2.2 := by
  simp only [queryFrag, bind_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-- The query group with the proof of work as one fragment. -/
theorem query_bindG (c d t : ℕ) (K : List ℕ → E → List (List K) → VerifierProgram Unit) :
    ((powCheck g).bind fun _ ↦ (samplePositions per d t).bind fun qs ↦
      sampleChallenge.bind fun lam ↦ (queryOpenings c qs).bind fun words ↦ K qs lam words) =
      (queryFragG g per d t c).bind fun gg ↦ K gg.1 gg.2.1 gg.2.2 := by
  simp only [queryFragG, queryFrag, bind_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

end Program

/-! ## Doom along the level -/

section Doom

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (ℓ ℓ' pre : ℕ)

/-- After the fold rounds. -/
def AfterFold (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (FoldInv μ ℓ₀ w i P ℓ pre r.1 r.2 cs ∧ ShapeOK i P ℓ cs) ∧ r.2.length = ℓ

/-- After the commitment of the next oracle. -/
def MidC (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ∃ cs₀ W', cs = cs₀ ++ [(P'.κ + P'.R, 3 * 2 ^ ℓ', W')] ∧ WellShaped (3 * 2 ^ ℓ') W' ∧
    AfterFold μ ℓ₀ w i P ℓ pre r cs₀

/-- After the query group: every member of the next list violates the glued claim. -/
def GlueC (r : WhirStateT × List E) (g : List ℕ × E × List (List K))
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidC μ ℓ₀ w i P P' ℓ ℓ' pre r cs ∧
    Viol P' (rowsOf ℓ' (laneO (i + 1) cs P'.n))
      (runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 []))
      (glueLv μ i r g.1 g.2.1 g.2.2 []).target

end Doom

/-! ## Bookkeeping lemmas -/

section Lemmas

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {ℓ ℓ' pre : ℕ}

theorem afterFold_len {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFold μ ℓ₀ w i P ℓ pre r cs) : r.1.folds.length = pre + ℓ := by
  obtain ⟨⟨⟨hl, -⟩, -⟩, hr⟩ := h
  omega

theorem afterFold_κ {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFold μ ℓ₀ w i P ℓ pre r cs) : μ - r.1.folds.length = P.κ := by
  have := afterFold_len h
  obtain ⟨⟨⟨-, -, hκ, -⟩, -⟩, -⟩ := h
  omega

/-- The glued state's weight. -/
theorem glueLv_runW (r : WhirStateT × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) :
    runW w ℓ₀ (glueLv μ i r qs lam words hq) = fun x ↦ runW w ℓ₀ r.1 x +
      1 * lam * Verifier.inducedWeight (μ - r.1.folds.length) qs (powers lam qs.length) x := by
  funext x
  rw [glueLv, glue_one]
  have := runW_glue w ℓ₀ r.1 [⟨1 * lam, r.1.folds.length, fun x ↦ Verifier.inducedWeight
    (μ - r.1.folds.length) qs (powers lam qs.length) x⟩] (by simp) x
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at this
  exact this

/-- The glued state's target. -/
theorem glueLv_target (r : WhirStateT × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) :
    (glueLv μ i r qs lam words hq).target = r.1.target + 1 * lam * enfOf i r.2 qs lam words := by
  rw [glueLv, glue_one]

/-- The glue keeps the folds. -/
theorem glueLv_folds (r : WhirStateT × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) : (glueLv μ i r qs lam words hq).folds = r.1.folds := by
  rw [glueLv, glue_one]

/-- The glued claims are well formed after the glue. -/
theorem gluedOK_glueLv {r : WhirStateT × List E} (hg : GluedOK μ r.1) (qs : List ℕ) (lam : E)
    (words : List (List K)) (hq : List E) : GluedOK μ (glueLv μ i r qs lam words hq) := by
  intro c hc
  rw [glueLv, glue_one] at hc ⊢
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with hc | rfl
  · exact hg c hc
  · exact ⟨le_rfl, isMultiaffine_inducedWeight _ _ _ (length_powers _ _)⟩

/-- The enforced sum of the rows of commitment `i` at in-range positions. -/
theorem enfOf_eq {cs : List (ℕ × ℕ × Word)} (hshape : ShapeOK i P ℓ cs) (lf : List E)
    (hlf : lf.length = ℓ) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n) (lam : E) :
    enfOf i lf qs lam (qs.map (wordOf cs i)) =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) *
        wordAt (fun v : Fin P.n ↦ foldsN lf (laneO i cs P.n) 0 v) qs[k] := by
  rw [enfOf, rows_eq]
  exact enforcedSum_eq i cs lf hlf qs hqs lam fun q _ ↦ length_wordOf hshape q

/-- **The next level's doom** from the glued doom and the query intro polynomial. -/
theorem levelPre_next (hP' : P'.κ + (pre + ℓ) + ℓ' = μ) (r : WhirStateT × List E)
    (g : List ℕ × E × List (List K)) (hq : List E) (cs : List (ℕ × ℕ × Word))
    (hglue : GlueC μ ℓ₀ w i P P' ℓ ℓ' pre r g cs)
    (hhq : QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2)) :
    LevelPre μ ℓ₀ w (i + 1) P' ℓ' (pre + ℓ) (glueLv μ i r g.1 g.2.1 g.2.2 hq) cs := by
  obtain ⟨⟨cs₀, W', rfl, hW', haf⟩, hviol⟩ := hglue
  have hlen := afterFold_len haf
  obtain ⟨⟨⟨-, -, -, hg, hquad, -⟩, hshape⟩, -⟩ := haf
  refine ⟨⟨?_, by simp, hP', gluedOK_glueLv hg _ _ _ _, ?_, ?_⟩, ?_⟩
  · rw [glueLv_folds]; simp [hlen]
  · rw [glueLv, glue_one]
    exact quadOK_zipWith hquad hhq _
  · have hr : runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 hq) =
        runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 []) := by
      rw [glueLv_runW, glueLv_runW]
    have ht : (glueLv μ i r g.1 g.2.1 g.2.2 hq).target =
        (glueLv μ i r g.1 g.2.1 g.2.2 []).target := by
      rw [glueLv_target, glueLv_target]
    simp only [List.length_nil, Nat.sub_zero, foldsN, List.foldl_nil, hr, ht]
    exact hviol
  · refine ⟨by simp [hshape.1], W', ?_, ?_⟩
    · rw [List.getElem?_append_right (by rw [hshape.1]), hshape.1, Nat.sub_self]
      simp [wdOf]
    · simpa [wdOf] using hW'

/-- After the commitment: the next oracle's word is appended. -/
theorem midC_of_commit {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)} {W : Word}
    (next : Whir.Level) (hℓ' : next.fold = ℓ') (hP' : P'.κ + (pre + ℓ) + ℓ' = μ)
    (hR' : P'.R = next.logInvRate) (h : AfterFold μ ℓ₀ w i P ℓ pre r cs)
    (hW : WellShaped (3 * 2 ^ next.fold) W) :
    MidC μ ℓ₀ w i P P' ℓ ℓ' pre r
      (cs ++ [(μ - r.1.folds.length - next.fold + next.logInvRate, 3 * 2 ^ next.fold, W)]) := by
  have hlen := afterFold_len h
  subst hℓ'
  refine ⟨cs, W, ?_, hW, h⟩
  congr 3
  omega

/-- The commitments after the next commitment, at index `i`. -/
theorem midC_word {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : MidC μ ℓ₀ w i P P' ℓ ℓ' pre r cs) :
    ∃ cs₀, cs[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs₀ i) ∧ wordOf cs i = wordOf cs₀ i ∧
      laneO i cs P.n = laneO i cs₀ P.n ∧ AfterFold μ ℓ₀ w i P ℓ pre r cs₀ := by
  obtain ⟨cs₀, W', rfl, -, haf⟩ := h
  have hsh := haf.1.2
  have hi : i < cs₀.length := by rw [hsh.1]; omega
  exact ⟨cs₀, shapeOK_append hsh _, wordOf_append _ _ hi, laneO_append _ _ hi _, haf⟩

/-- A level's word read through the view is the word of the commitment the level opens. -/
theorem commits_cidx {c₀ n₀ : ℕ} (hc : c₀ < n₀) {cs : List (ℕ × ℕ × Word)} {j ht wd : ℕ}
    {W : Word} (h : (viewC c₀ n₀ cs)[j]? = some (ht, wd, W)) :
    cs[cidx c₀ n₀ j]? = some (ht, wd, W) :=
  getElem?_viewC hc h

end Lemmas

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirLevelMid` =====

/-!
# The specification of a level with a next commitment

`midSpec`: from `LevelPre` of level `i` (`A(i, 0)` for the running claim against the list of the
level's oracle, on the opening's view of the commitments), the level's groups escape with
probability at most

* `eFold P ℓ` at each fold challenge,
* `eQueryUd P P' t` at the query group (positions, `λ`, openings),

and the level hands `LevelPre` of level `i + 1` to the next level's specification `K`. The
hypotheses `MidHyp` are the arithmetic of the levels (the level's code has the message variables
left after its folds, the next code those after the next level's), the positions' width
(`1 ≤ per`, `per · (κ + R) ≤ 192`), the root's index (`c₀ < n₀`) and the next code's list bound
`listMax ≤ 1` (unique decoding: the query step's one candidate).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-- The arithmetic of a level with a next level. -/
structure MidHyp (μ ℓ₀ per c₀ n₀ : ℕ) (w : List E → E) (P P' : LevelCode)
    (level next : Whir.Level) (pre : ℕ) : Prop where
  hw : IsMultiaffine μ w
  hℓ₀ : ℓ₀ ≤ μ
  hP : P.κ + pre + level.fold = μ
  hP' : P'.κ + (pre + level.fold) + next.fold = μ
  hR : P.R = level.logInvRate
  hR' : P'.R = next.logInvRate
  hc : c₀ < n₀
  hper : 1 ≤ per
  hpd : per * (P.κ + P.R) ≤ 192
  hL' : P'.listMax ≤ 1

/-- A view in shape has a commitment. -/
theorem ne_nil_of_shapeOK {i ℓ : ℕ} {P : LevelCode} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) : cs ≠ [] := by
  intro hc; have := h.1; rw [hc] at this; simp at this

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P P' : LevelCode}
  {level next : Whir.Level} {rest : List Whir.Level} {pre : ℕ} {εmax : ENNReal}

/-- The query group of a level with a next level, followed by the query intro polynomial and
the next level. -/
noncomputable def midQuerySpec (H : MidHyp μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hQlt : eQueryUd P P' level.queries < 1)
    (K : ∀ s', Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirStateT × List E) :
    Spec ((queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i)).bind fun gg ↦ midFinish μ ℓ₀ per c₀ n₀ g dir w i next rest r gg.1 gg.2.1 gg.2.2)
      (fun h ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax ((2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries) 0 :=
  ((Spec.ofNoMove (p := queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i))
      (Pre := fun h ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (viewC c₀ n₀ (commits h)))
      (Post := fun g h ↦ GlueC μ ℓ₀ w i P P' level.fold next.fold pre r g
        (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_queryFragG _ _ _ _ _).noMove
      ((grind_disc_le g _).trans_lt hQlt) fun h₀ hp ↦ by
        obtain ⟨cs₀, hW, -, -, haf⟩ := midC_word hp
        have hκm := afterFold_κ haf
        have hd : μ - r.1.folds.length + level.logInvRate = P.κ + P.R := by rw [hκm, H.hR]
        have hκ' : P.κ = next.fold + P'.κ := by have := H.hP; have := H.hP'; omega
        have hlf : r.2.length = level.fold := haf.2
        have hviol : Viol P (fun _ : Fin 0 → Bool ↦ fun v ↦ foldsN r.2 (laneO i cs₀ P.n) 0 v)
            (runW w ℓ₀ r.1) r.1.target := by
          have := haf.1.1.2.2.2.2.2
          rwa [hlf, Nat.sub_self, rowsOf_zero] at this
        have hW' := commits_cidx H.hc hW
        rw [hd]
        refine escRet_queryFragG_le_ud g hg P P' hκ' per level.queries (cidx c₀ n₀ i) H.hper H.hpd h₀
          hW' (rowsOf next.fold (laneO (i + 1) (viewC c₀ n₀ (commits h₀)) P'.n)) _
          (runW w ℓ₀ r.1) r.1.target hviol ((P'.card_iList_le _).trans H.hL')
          (fun g cs ↦ GlueC μ ℓ₀ w i P P' level.fold next.fold pre r g (viewC c₀ n₀ cs))
          fun qs lam hr hlen hv ↦ ⟨hp, ?_⟩
        rw [glueLv_runW, glueLv_target, enfOf_eq haf.1.2 r.2 hlf qs hr lam, hκm]
        exact hv).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun gg ↦
    (roundPolyInv (fun cs ↦ GlueC μ ℓ₀ w i P P' level.fold next.fold pre r gg (viewC c₀ n₀ cs))
        (enfOf i r.2 gg.1 gg.2.1 gg.2.2) (T := εmax) le_rfl).bind' fun hq ↦
      (K (glueLv μ i r gg.1 gg.2.1 gg.2.2 hq)).mono
        (fun h hp ↦ levelPre_next H.hP' r gg hq _ hp.2 hp.1) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl

/-- After the fold rounds of a level with a next level. -/
noncomputable def midTailSpec (H : MidHyp μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hQlt : eQueryUd P P' level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries ≤ εmax)
    (K : ∀ s', Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirStateT × List E) :
    Spec (midTail μ ℓ₀ per c₀ n₀ g dir w i level next rest r)
      (fun h ↦ AfterFold μ ℓ₀ w i P level.fold pre r (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax 0 0 :=
  (commitInv (fun cs ↦ AfterFold μ ℓ₀ w i P level.fold pre r (viewC c₀ n₀ cs))
      (fun cs ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (viewC c₀ n₀ cs))
      (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
      (fun cs W h hW ↦ by
        rw [viewC_append (le_length_of_viewC (ne_nil_of_shapeOK h.1.2))]
        exact midC_of_commit next rfl H.hP' H.hR' h hW)
      (T := (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries) hεQ).bind' fun _ ↦
  (grindPreInv (fun cs ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (viewC c₀ n₀ cs)) g
      hεQ).bind' fun _ ↦
  (midQuerySpec H hg hQlt K r).congr
    (query_bindG per g (cidx c₀ n₀ i) (μ - r.1.folds.length + level.logInvRate) level.queries
      fun qs lam words ↦ midFinish μ ℓ₀ per c₀ n₀ g dir w i next rest r qs lam words).symm

/-- **The specification of a level with a next level.** -/
noncomputable def midSpec (H : MidHyp μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hεF : eFold P level.fold ≤ εmax) (hQlt : eQueryUd P P' level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries ≤ εmax)
    (K : ∀ s', Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (s : WhirStateT) :
    Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w i (level :: next :: rest) s)
      (fun h ↦ LevelPre μ ℓ₀ w i P level.fold pre s (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0 :=
  (((foldRoundsSpec μ ℓ₀ w i P level.fold pre (viewC c₀ n₀)
      (fun cs ↦ ShapeOK i P level.fold (viewC c₀ n₀ cs)) H.hw H.hℓ₀ hεF level.fold s []).bind'
      fun r ↦ midTailSpec H hg hQlt hεQ K r).mono
    (fun _ hp ↦ ⟨⟨hp.1, hp.2⟩, by simp⟩) (fun _ _ h ↦ h) le_rfl hεF le_rfl).congr
    (whirLevels_mid μ ℓ₀ per c₀ n₀ g dir w i level next rest s).symm

end
end LeanVM.Protocol.Whir.Sound
