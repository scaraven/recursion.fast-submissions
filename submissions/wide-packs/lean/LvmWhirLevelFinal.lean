-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/LevelFinal.lean` (formal rev 40f877dc) as
-- `LvmWhirLevelFinal` for lvm (WP-7). Changed: the level is lvm's (no proof of work, positions `per` per challenge,
-- the opening of commitment `cidx c₀ n₀ i`, predicates on the opening's view); the glue is `glueLv`; and the doom
-- right after the residual is read is `ResC` — the residual's own doom `FinViol` (it violates the running claim, or
-- its encoding is not in the list of the folded word) — which leanVM's `AfterFold` implies and which the query step
-- needs (`exists_agreeSet_finViol`). `ResC` is the doom of a `Spec.ret` placed after the reads, so that an accepting
-- run that is not doomed there has `Enc(f) ∈ Λ(folded word)` (`LvmWhirDoom`, for the extractor).
/-
  LeanVM.Protocol.Whir.Sound.LevelFinal

  The specification of the final WHIR level: the fold rounds, the residual, the query group with
  `λ`, the tail rounds and the terminal check.
-/
import LvmWhirProg
import LvmWhirLevelMidSpec

-- ===== merged from `LvmWhirTail` (GOLF module merge: `LvmWhirTail.lean` is now a stub importing `LvmWhirLevelFinal`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Tail.lean` (formal rev 40f877dc) as `LvmWhirTail` for lvm (WP-7).
/-
  LeanVM.Protocol.Whir.Sound.Tail

  The final level's tail rounds and terminal check: the residual `f_final` violates the running
  claim, each tail round keeps it violated except at two challenges, and the terminal check
  rejects a violated claim.
-/

/-!
# The tail rounds

On the final level the prover sends the residual table `f_final` (`2^κ` entries), so no list is
involved: after the query group the verifier holds a claim about `f_final` itself, and the tail
(`LeanVM.Protocol.Verifier.tailRounds`, `crates/verifier/src/whir.rs:237-246` at leanVM
`40f877dc`) is a plain sumcheck on it.

* `tailMsg τ res n`: the residual folded by the tail challenges `τ` so far, as a message on `n`
  lane bits (the remaining variables) and no message bits.
* `TailInv`: the residual has `2^(|τ| + n)` entries, the running weight is multiaffine, the round
  polynomial sums to the target, and the folded residual violates the running claim.
* `tailSpec`: each tail round escapes with probability at most `eTail = 2/|E|`
  (`card_sumcheck_bad_le`), and the rounds return `TailDone`: the fully folded residual,
  `multilinear_eval(f_final, τ)`, times the running weight at `τ` differs from the final target.
* `tailDone_ne`: the terminal check `weight · multilinear_eval(residual, tail) = target` fails under
  `TailDone`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-- The residual table as an integer-indexed oracle. -/
def resO (res : List E) : ℕ → Unit → E := fun j _ ↦ res.getD j 0

/-- The residual folded by the tail challenges `τ`, on the `n` remaining variables. -/
def tailMsg (τ res : List E) (n : ℕ) : (Fin n → Bool) → (Fin 0 → Bool) → E :=
  fun u _ ↦ foldsN τ (resO res) (bitsToNat u) ()

variable (ℓ₀ : ℕ) (w : List E → E) (s : WhirStateT) (res : List E)

/-- **The tail invariant**: the folded residual violates the running claim. -/
def TailInv (τ : List E) (n : ℕ) (target : E) (quad : List E) : Prop :=
  res.length = 2 ^ (τ.length + n) ∧ IsMultiaffine (τ.length + n) (runW w ℓ₀ s) ∧
    QuadOK quad target ∧ claimSum (fun r ↦ runW w ℓ₀ s (τ ++ r)) (tailMsg τ res n) ≠ target

/-- After a tail challenge `c`. -/
def TailMid (τ : List E) (n : ℕ) (c : E) (quad : List E) : Prop :=
  res.length = 2 ^ (τ.length + 1 + n) ∧ IsMultiaffine (τ.length + 1 + n) (runW w ℓ₀ s) ∧
    claimSum (fun r ↦ runW w ℓ₀ s ((τ ++ [c]) ++ r)) (tailMsg (τ ++ [c]) res n) ≠ polyEval quad c

/-- At the end of the tail. -/
def TailDone (τ : List E) (t : E) : Prop :=
  res.length = 2 ^ τ.length ∧ claimSum (fun r ↦ runW w ℓ₀ s (τ ++ r)) (tailMsg τ res 0) ≠ t

variable {ℓ₀ w s res}

theorem foldRows_tailMsg (τ : List E) (n : ℕ) (c : E) :
    foldRows c (tailMsg τ res (n + 1)) = tailMsg (τ ++ [c]) res n := by
  funext u x
  simp [foldRows, tailMsg, bitsToNat_cons, foldsN, List.foldl_append, foldN, add_comm]

open Classical in
/-- A tail round escapes at at most two challenges. -/
theorem card_tailBad_le (τ : List E) (n : ℕ) (target : E) (quad : List E)
    (h : TailInv ℓ₀ w s res τ (n + 1) target quad) :
    (univ.filter fun c ↦ ¬ TailMid ℓ₀ w s res τ n c quad).card ≤ 2 := by
  obtain ⟨hlen, hma, ⟨c₀, c₁, c₂, rfl, hσ⟩, hviol⟩ := h
  have hΦ : IsMultiaffine (n + 1 + 0) fun r ↦ runW w ℓ₀ s (τ ++ r) := hma.append τ rfl
  have hc := card_sumcheck_bad_le _ hΦ (tailMsg τ res (n + 1)) target c₀ c₁ c₂ hσ hviol
  refine (Finset.card_le_card fun c hc' ↦ ?_).trans hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, TailMid, not_and, not_not] at hc' ⊢
  have := hc' (by rw [hlen]; congr 1; omega) (by
    rw [show τ.length + 1 + n = τ.length + (n + 1) by omega]; exact hma)
  rw [← this, foldRows_tailMsg]
  simp

variable (ℓ₀ w s res)

/-- **The tail rounds' specification.** -/
noncomputable def tailSpec {εmax : ENNReal} (hεT : eTail ≤ εmax) :
    (n : ℕ) → (τ : List E) → (target : E) → (quad : List E) →
      Spec (tailRoundsT n target quad) (fun _ ↦ TailInv ℓ₀ w s res τ n target quad)
        (fun x _ ↦ TailDone ℓ₀ w s res (τ ++ x.1) x.2) εmax eTail 0
  | 0, τ, target, quad => (Spec.ret ([], target)).mono
      (fun _ h ↦ ⟨by simpa using h.1, by simpa using h.2.2.2⟩) (fun _ _ h ↦ h) le_rfl zero_le
      le_rfl
  | n + 1, τ, target, quad =>
    ((Spec.sampleE (Pre := fun _ ↦ TailInv ℓ₀ w s res τ (n + 1) target quad)
        (Post := fun c _ ↦ TailMid ℓ₀ w s res τ n c quad) (εmax := εmax) (T := 0) eTail
        fun _ hp ↦ by
          rw [eTail, ENNReal.div_eq_inv_mul]
          gcongr
          exact_mod_cast card_tailBad_le τ n target quad hp).bind' fun c ↦
      Spec.ite (c := n = 0)
        (fun hn ↦ (Spec.ret ([c], polyEval quad c)).mono (fun _ h ↦ by
          subst hn
          exact ⟨by simpa using h.1, by simpa using h.2.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
        (fun _ ↦ (roundPolyInv (fun _ ↦ TailMid ℓ₀ w s res τ n c quad) (polyEval quad c)
            (T := eTail) hεT).bind' fun quad' ↦
          ((tailSpec hεT n (τ ++ [c]) (polyEval quad c) quad').mono
            (fun _ h ↦ ⟨by simpa using h.2.1, by simpa using h.2.2.1, h.1, by
              simpa using h.2.2.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun x ↦
            (Spec.ret (c :: x.1, x.2)).mono (fun _ h ↦ by simpa using h) (fun _ _ h ↦ h) le_rfl
              le_rfl le_rfl)).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl

/-- **The terminal check fails** at the end of the tail. -/
theorem tailDone_ne {τ : List E} {t : E} (h : TailDone ℓ₀ w s res τ t) :
    ¬ runW w ℓ₀ s τ * multilinearEval res τ = t := by
  obtain ⟨hlen, hviol⟩ := h
  rw [claimSum_zero] at hviol
  rw [multilinearEval_eq_foldsN res τ hlen]
  intro heq
  apply hviol
  rw [Fintype.sum_unique]
  simp only [bitsL_zero, List.append_nil, tailMsg]
  have hb : bitsToNat (Fin.elim0 : Fin 0 → Bool) = 0 := by simp [bitsToNat]
  rw [hb]
  exact heq

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirTail` =====

/-!
# The final level

`whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w i [level] s` is, definitionally, `finProg`: the fold rounds, the
residual `f_final` (`2^κ` scalars), positions, `λ`, opening, the query intro polynomial, the glue
(`λ^(1+q)` for the consistency claims), with `dir` the direct check of the opened positions
against `Enc(f_final)` (a `require`: doom is kept), the tail rounds and the terminal check
`weight · multilinear_eval(f_final, tail) = target` (leanVM `crates/verifier/src/whir.rs:167-260`
at `40f877dc`, without the proof of work).

Doom: `AfterFold` after the fold rounds (`A(r−1, ℓ)`); after the residual `ResC`: the bookkeeping
(`FinBook`) and `FinViol` of the residual; after the query group `GlueFinC`: `f_final` violates the
glued claim (`escRet_queryFrag_le_finViol`); then the tail invariant (`TailInv`, `tailSpec`) and
the failing terminal check (`tailDone_ne`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

section Program

variable (μ ℓ₀ per c₀ n₀ g : ℕ) (dir : Bool) (w : List E → E) (i : ℕ) (level : Whir.Level)

/-- After the query group of the final level. -/
def finFinish (r : WhirStateT × List E) (residual : List E) (qs : List ℕ) (lam : E)
    (words : List (List K)) : VerifierProgram Unit :=
  (sumcheckRoundPoly 3 (enfOf i r.2 qs lam words) none).bind fun hq ↦
    (if dir then VerifierProgram.require (directOK (μ - r.1.folds.length) level.logInvRate residual
        qs (if i = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow) r.2)
      else pure ()).bind fun _ ↦
    (tailRoundsT (μ - r.1.folds.length) (glueLv μ i r qs lam words hq).target
      (glueLv μ i r qs lam words hq).quad).bind fun x ↦
      VerifierProgram.require (runW w ℓ₀ (glueLv μ i r qs lam words hq) x.1 *
        multilinearEval residual x.1 = x.2)

/-- After the fold rounds of the final level. -/
def finTail (r : WhirStateT × List E) : VerifierProgram Unit :=
  (readScalars (2 ^ (μ - r.1.folds.length))).bind fun residual ↦
  (grindPre g).bind fun _ ↦ (powCheck g).bind fun _ ↦
  (samplePositions per (μ - r.1.folds.length + level.logInvRate) level.queries).bind fun qs ↦
  sampleChallenge.bind fun lam ↦ (queryOpenings (cidx c₀ n₀ i) qs).bind fun words ↦
    finFinish μ ℓ₀ dir w i level r residual qs lam words

/-- The final level, unfolded. -/
def finProg (s : WhirStateT) : VerifierProgram Unit :=
  (foldRoundsT level.fold s []).bind fun r ↦ finTail μ ℓ₀ per c₀ n₀ g dir w i level r

/-- **`whirLevelsUd` on the final level is `finProg`.** -/
theorem whirLevels_fin (s : WhirStateT) :
    whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w i [level] s = finProg μ ℓ₀ per c₀ n₀ g dir w i level s := rfl

end Program

section Doom

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (ℓ pre : ℕ)

/-- `AfterFold` without its violation: the bookkeeping after the fold rounds. -/
def FinBook (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (r.1.folds.length = pre + r.2.length ∧ r.2.length ≤ ℓ ∧ P.κ + pre + ℓ = μ ∧ GluedOK μ r.1 ∧
    QuadOK r.1.quad r.1.target) ∧ ShapeOK i P ℓ cs ∧ r.2.length = ℓ

/-- The level's word folded by all its challenges. -/
def foldedW (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Fin P.n → E :=
  fun v ↦ foldsN r.2 (laneO i cs P.n) 0 v

/-- **After the residual** `res`: the bookkeeping and the residual's doom `FinViol` (it violates
the running claim, or its encoding is not in the list of the folded word). -/
def ResC (r : WhirStateT × List E) (res : List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (res.length = 2 ^ (μ - r.1.folds.length) ∧ FinBook μ i P ℓ pre r cs) ∧
    FinViol P (foldedW i P r cs) (runW w ℓ₀ r.1) r.1.target (resMsg res)

/-- After the query group of the final level: the residual violates the glued claim. -/
def GlueFinC (r : WhirStateT × List E) (res : List E) (g : List ℕ × E × List (List K))
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  (res.length = 2 ^ (μ - r.1.folds.length) ∧ FinBook μ i P ℓ pre r cs) ∧
    ∑ x : Fin P.κ → Bool, runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 []) (bitsL x) * resMsg res x ≠
      (glueLv μ i r g.1 g.2.1 g.2.2 []).target

end Doom

section Lemmas

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P : LevelCode} {ℓ pre : ℕ}

theorem finBook_κ {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : FinBook μ i P ℓ pre r cs) : μ - r.1.folds.length = P.κ := by
  obtain ⟨⟨hl, -, hκ, -⟩, -, hr⟩ := h
  omega

/-- **The residual's doom from the fold rounds' doom.** -/
theorem resC_of_afterFold {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)} {res : List E}
    (h : AfterFold μ ℓ₀ w i P ℓ pre r cs) (hres : res.length = 2 ^ (μ - r.1.folds.length)) :
    ResC μ ℓ₀ w i P ℓ pre r res cs := by
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, hviol⟩, hsh⟩, hlf⟩ := h
  refine ⟨⟨hres, ⟨h1, h2, h3, h4, h5⟩, hsh, hlf⟩, finViol_of_viol P _ _ _ ?_ _⟩
  rwa [hlf, Nat.sub_self, rowsOf_zero] at hviol

/-- The tail's starting claim is the residual's inner product on the message cube. -/
theorem claimSum_tailMsg_nil {n κ : ℕ} (h : n = κ) (Φ : List E → E) (res : List E) :
    claimSum (fun r ↦ Φ ([] ++ r)) (tailMsg [] res n) =
      ∑ x : Fin κ → Bool, Φ (bitsL x) * resMsg res x := by
  subst h
  simp only [claimSum, List.nil_append, Fintype.sum_unique, bitsL_zero, List.append_nil]
  rfl

/-- **The tail invariant at the start of the tail.** -/
theorem tailInv_start (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (r : WhirStateT × List E)
    (res : List E) (g : List ℕ × E × List (List K)) (hq : List E) (cs : List (ℕ × ℕ × Word))
    (hglue : GlueFinC μ ℓ₀ w i P ℓ pre r res g cs)
    (hhq : QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2)) :
    TailInv ℓ₀ w (glueLv μ i r g.1 g.2.1 g.2.2 hq) res [] (μ - r.1.folds.length)
      (glueLv μ i r g.1 g.2.1 g.2.2 hq).target (glueLv μ i r g.1 g.2.1 g.2.2 hq).quad := by
  obtain ⟨⟨hres, hbook⟩, hviol⟩ := hglue
  have hκm := finBook_κ hbook
  obtain ⟨⟨h1, -, h3, hg, hquad⟩, -, hlf⟩ := hbook
  have hgl : GluedOK μ (glueLv μ i r g.1 g.2.1 g.2.2 hq) := gluedOK_glueLv hg _ _ _ _
  have hfl : (glueLv μ i r g.1 g.2.1 g.2.2 hq).folds = r.1.folds := glueLv_folds _ _ _ _ _
  refine ⟨by simpa using hres, ?_, ?_, ?_⟩
  · have := isMultiaffine_runW hw hℓ₀ _ (by rw [hfl, h1, hlf]; (clear * - hκm h3; omega)) hgl
    rw [hfl, List.length_nil, Nat.zero_add] at *; assumption
  · rw [glueLv, glue_one]
    exact quadOK_zipWith hquad hhq _
  · rw [claimSum_tailMsg_nil hκm]
    have hr : runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 hq) =
        runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 []) := by rw [glueLv_runW, glueLv_runW]
    have ht : (glueLv μ i r g.1 g.2.1 g.2.2 hq).target =
        (glueLv μ i r g.1 g.2.1 g.2.2 []).target := by rw [glueLv_target, glueLv_target]
    rw [hr, ht]
    exact hviol

end Lemmas

/-! ## The specification -/

/-- The arithmetic of the final level. -/
structure FinHyp (μ ℓ₀ per c₀ n₀ : ℕ) (w : List E → E) (P : LevelCode) (level : Whir.Level)
    (pre : ℕ) : Prop where
  hw : IsMultiaffine μ w
  hℓ₀ : ℓ₀ ≤ μ
  hP : P.κ + pre + level.fold = μ
  hR : P.R = level.logInvRate
  hc : c₀ < n₀
  hper : 1 ≤ per
  hpd : per * (P.κ + P.R) ≤ 192

/-- `n + 1` scalars keep a commitment invariant, with lead `0` (leanVM `readNInv` at `n + 1`,
before its lead is raised to the follower's). -/
noncomputable def readNInvSucc (I : CInv) {εmax T : ENNReal} (hT : T ≤ εmax) (n : ℕ) :
    Spec (readScalars (n + 1)) (fun h ↦ I (commits h))
      (fun xs h ↦ xs.length = n + 1 ∧ I (commits h)) εmax 0 T :=
  (readInv I (T := T) hT).bind' fun x ↦
    (readNInv I hT n).bind' fun xs ↦
      (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P : LevelCode} {level : Whir.Level}
  {pre : ℕ} {εmax : ENNReal}

/-- The query group of the final level, the tail and the terminal check, from the residual's
doom. -/
noncomputable def finQuerySpec (H : FinHyp μ ℓ₀ per c₀ n₀ w P level pre) (hg : g ≤ 192)
    (hQlt : eQueryFinal P level.queries < 1) (hεT : eTail ≤ εmax)
    (r : WhirStateT × List E) (res : List E) :
    Spec ((queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i)).bind fun g ↦ finFinish μ ℓ₀ dir w i level r res g.1 g.2.1 g.2.2)
      (fun h ↦ ResC μ ℓ₀ w i P level.fold pre r res (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax ((2 : ENNReal)⁻¹ ^ g * eQueryFinal P level.queries) 0 :=
  ((Spec.ofNoMove (p := queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i))
      (Pre := fun h ↦ ResC μ ℓ₀ w i P level.fold pre r res (viewC c₀ n₀ (commits h)))
      (Post := fun g h ↦ GlueFinC μ ℓ₀ w i P level.fold pre r res g (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_queryFragG _ _ _ _ _).noMove
      ((grind_disc_le g _).trans_lt hQlt) fun h₀ hp ↦ by
        obtain ⟨⟨hres, hbook⟩, hD⟩ := hp
        have hκm := finBook_κ hbook
        have hd : μ - r.1.folds.length + level.logInvRate = P.κ + P.R := by rw [hκm, H.hR]
        have hlf : r.2.length = level.fold := hbook.2.2
        have hW' := commits_cidx H.hc (shapeOK_word hbook.2.1).1
        rw [hd]
        refine escRet_queryFragG_le_finViol g hg P per level.queries (cidx c₀ n₀ i) H.hper H.hpd h₀ hW'
          _ (runW w ℓ₀ r.1) r.1.target (resMsg res) hD
          (fun g cs ↦ GlueFinC μ ℓ₀ w i P level.fold pre r res g (viewC c₀ n₀ cs))
          fun qs lam hr hlen hv ↦ ⟨⟨hres, hbook⟩, ?_⟩
        rw [glueLv_runW, glueLv_target, enfOf_eq hbook.2.1 r.2 hlf qs hr lam, hκm]
        exact hv).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun g ↦
    (roundPolyInv (fun cs ↦ GlueFinC μ ℓ₀ w i P level.fold pre r res g (viewC c₀ n₀ cs))
        (enfOf i r.2 g.1 g.2.1 g.2.2) (T := eTail) hεT).bind' fun hq ↦
      (Spec.ite (c := dir = true)
          (fun _ ↦ Spec.require (Post := fun _ h ↦ QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2) ∧
              GlueFinC μ ℓ₀ w i P level.fold pre r res g (viewC c₀ n₀ (commits h)))
            fun _ hp _ ↦ hp)
          (fun _ ↦ (Spec.ret (Post := fun _ h ↦ QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2) ∧
              GlueFinC μ ℓ₀ w i P level.fold pre r res g (viewC c₀ n₀ (commits h))) ()).congr
            (VerifierProgram.pure_eq ()).symm)).bind' fun _ ↦
      ((tailSpec ℓ₀ w (glueLv μ i r g.1 g.2.1 g.2.2 hq) res hεT (μ - r.1.folds.length) []
          (glueLv μ i r g.1 g.2.1 g.2.2 hq).target (glueLv μ i r g.1 g.2.1 g.2.2 hq).quad).mono
        (fun h hp ↦ tailInv_start H.hw H.hℓ₀ r res g hq _ hp.2 hp.1)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun x ↦
        Spec.require fun _ hd hc ↦ tailDone_ne ℓ₀ w _ res (by simpa using hd) hc

/-- After the fold rounds of the final level: the residual (whose doom `ResC` is the doom of the
boundary after its last scalar), then the query group. -/
noncomputable def finTailSpec (H : FinHyp μ ℓ₀ per c₀ n₀ w P level pre) (hg : g ≤ 192)
    (hQlt : eQueryFinal P level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQueryFinal P level.queries ≤ εmax)
    (hεT : eTail ≤ εmax) (r : WhirStateT × List E) :
    Spec (finTail μ ℓ₀ per c₀ n₀ g dir w i level r)
      (fun h ↦ AfterFold μ ℓ₀ w i P level.fold pre r (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax 0 0 :=
  Spec.congr (p := (readScalars (2 ^ (μ - r.1.folds.length) - 1 + 1)).bind fun res ↦
      (VerifierProgram.ret res).bind fun res ↦ (grindPre g).bind fun _ ↦
        (queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
          (cidx c₀ n₀ i)).bind fun g ↦ finFinish μ ℓ₀ dir w i level r res g.1 g.2.1 g.2.2)
    (by
      rw [Nat.sub_add_cancel Nat.one_le_two_pow]
      simp only [finTail, VerifierProgram.ret_bind]
      congr 1
      funext res
      congr 1
      funext _
      exact (query_bindG per g (cidx c₀ n₀ i) _ _ _).symm)
    ((readNInvSucc (fun cs ↦ AfterFold μ ℓ₀ w i P level.fold pre r (viewC c₀ n₀ cs))
        (T := (2 : ENNReal)⁻¹ ^ g * eQueryFinal P level.queries) hεQ
        (2 ^ (μ - r.1.folds.length) - 1)).bind fun res ↦
      ((Spec.ret (Post := fun res h ↦ ResC μ ℓ₀ w i P level.fold pre r res
          (viewC c₀ n₀ (commits h))) (εmax := εmax)
          (T := (2 : ENNReal)⁻¹ ^ g * eQueryFinal P level.queries) res).mono
        (fun _ hp ↦ resC_of_afterFold hp.2 (by
          rw [hp.1, Nat.sub_add_cancel Nat.one_le_two_pow])) (fun _ _ h ↦ h) le_rfl le_rfl
          le_rfl).bind fun res ↦
        (grindPreInv (fun cs ↦ ResC μ ℓ₀ w i P level.fold pre r res (viewC c₀ n₀ cs)) g
          hεQ).bind fun _ ↦ finQuerySpec H hg hQlt hεT r res)

/-- **The specification of the final level.** -/
noncomputable def finSpec (H : FinHyp μ ℓ₀ per c₀ n₀ w P level pre) (hg : g ≤ 192)
    (hεF : eFold P level.fold ≤ εmax) (hQlt : eQueryFinal P level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQueryFinal P level.queries ≤ εmax) (hεT : eTail ≤ εmax)
    (s : WhirStateT) :
    Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w i [level] s)
      (fun h ↦ LevelPre μ ℓ₀ w i P level.fold pre s (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0 :=
  (((foldRoundsSpec μ ℓ₀ w i P level.fold pre (viewC c₀ n₀)
      (fun cs ↦ ShapeOK i P level.fold (viewC c₀ n₀ cs)) H.hw H.hℓ₀ hεF level.fold s []).bind'
      fun r ↦ finTailSpec H hg hQlt hεQ hεT r).mono
    (fun _ hp ↦ ⟨⟨hp.1, hp.2⟩, by simp⟩) (fun _ _ h ↦ h) le_rfl hεF le_rfl).congr
    (whirLevels_fin μ ℓ₀ per c₀ n₀ g dir w i level s).symm

end
end LeanVM.Protocol.Whir.Sound
