-- WP-14 (ASM), adapted for lvm2 S4 (X-REC2-CERT): the extraction map of the `S` branch (DEC's
-- level-1 decoder `decodeRec1` then WP-13b's level-0 decoder `decodeRec`, on `C_rec`'s two words,
-- fold challenges and final residual read off the history), its correctness at an accepted history
-- outside doom and luck, and the knowledge certificate of `schemeS` with the middle phases abstract.
import LvmCertSLuck
import LvmXDecUd
import LvmXDec1Ud
import LvmWhirDoom2
import LvmCertSRes

-- ===== merged from `LvmWhir2Mid` (GOLF module merge: `LvmWhir2Mid.lean` is now a stub importing `LvmCertSExt`) =====
section
-- New for lvm2 (X-REC2-CERT, stage S4): the doom of a WHIR level's next commitment created at that
-- commitment. Adapted from WP-7's `LvmWhirEscape` (`exists_agreeSet_ud`), `LvmWhirGroupEscape`
-- (`escRet_queryFrag_le_ud`) and `LvmWhirLevelMidSpec` (`midQuerySpec`, `midTailSpec`): the proofs
-- are theirs with the level's own doom (`Viol` of the folded word) replaced by the weaker `FarU`.

/-!
# The next commitment's doom

WP-7's query step (`exists_agreeSet_ud`) uses the level's doom (every member of the folded word's
list violates the running claim) only through one consequence: **every member `V` of the next
oracle's list that meets the running claim has a level-`i` encoding that agrees with the folded word
on fewer than `thr` columns** (`FarU`). Both the level's doom (`farU_of_viol`) and the level-1
commitment's doom of the extractor (`MidDoomUd`, `farU_of_midDoom`) imply it.

* `exists_agreeSet_far`, `escRet_queryFrag_le_far`: the query step and the query group's escape
  `eQueryUd` from `FarU`.
* `FarC`: after the commitment of the next oracle, the bookkeeping of the fold rounds (`FinBook`)
  and `FarU` of the next oracle's rows against the folded word. `GlueFarC`: after the query group,
  every member of the next list violates the glued claim; with the query intro polynomial it is
  `LevelPre` of the next level (`levelPre_next_far`).
* `midQuerySpecFar`: WP-7's `midQuerySpec` from `FarC`.
* **`midTailFarSpec`**: after the fold rounds, from no doom: the doom is created at the next
  commitment iff `FarC` holds (`Spec.commitP`), then the query group and the next level.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-! ## The query step from `FarU` -/

/-- **Every member of the next list that meets the running claim is far** from the folded word
`C`: its level-`i` encoding agrees with `C` on fewer than `thr` columns. -/
def FarU (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E) : Prop :=
  ∀ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) = σ →
    (univ.filter fun x ↦ enc P.κ P.R (joinMsg hκ (decode P' V)) x = C x).card < P.thr

/-- The level's doom implies `FarU`. -/
theorem farU_of_viol (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) : FarU P P' hκ Q' C Φ σ := by
  intro V _ hclaim
  by_contra hlt
  exact viol_of_close P C Φ σ hviol _ (not_lt.mp hlt) (by rw [sum_joinMsg]; exact hclaim)

/-- The extractor's level-1 commitment doom implies `FarU`. -/
theorem farU_of_midDoom (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hD : MidDoomUd (R₀ := P.R) P.thr P' hκ C Q') : FarU P P' hκ Q' C Φ σ :=
  fun V hV _ ↦ hD V hV

/-- **The query step from `FarU`** (WP-7's `exists_agreeSet_ud`, same proof). -/
theorem exists_agreeSet_far (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hfar : FarU P P' hκ Q' C Φ σ) (hone : (iList P'.code P'.thr Q').card ≤ 1) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodUd P P' hκ Q' C Φ σ qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hex : ∃ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) = σ
  · obtain ⟨V₀, hV₀, hclaim⟩ := hex
    set G := joinMsg hκ (decode P' V₀)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · exact Nat.succ_le_of_lt (hfar V₀ hV₀ hclaim)
    · intro hlt
      simp only [QueryGoodUd, not_forall, not_or, not_not, exists_prop, not_exists,
        not_and] at hqs
      obtain ⟨V, hV, -, hall⟩ := hqs
      have hVV : V = V₀ := Finset.card_le_one.mp hone _ hV _ hV₀
      subst hVV
      have h := hall q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd ?_ hqs⟩
    intro V hV
    exact Or.inl fun h ↦ hex ⟨V, hV, h⟩

open Classical in
/-- **The query group's escape from `FarU`** (WP-7's `escRet_queryFrag_le_ud`, same proof). -/
theorem escRet_queryFrag_le_far (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hfar : FarU P P' hκ Q' C Φ σ)
    (hone : (iList P'.code P'.thr Q').card ≤ 1)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      Viol P' Q' (fun r ↦ Φ r + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag per (P.κ + P.R) t c) ≤
      eQueryUd P P' t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet_far P P' hκ Q' C Φ σ hfar hone
  refine (retExp_queryFrag_le per (P.κ + P.R) t c hper hpd h₀ hW _
    (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A)
    (((t * P'.listMax : ℕ) : ENNReal) / Fintype.card E) ?_).trans ?_
  · intro qs hr hlen
    by_cases hall : ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A
    · have : allIn (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) qs = 1 := by
        unfold allIn
        split_ifs with h
        · rfl
        · exact absurd hall h
      rw [this]
      exact (avg_le_one _ fun _ ↦ by split_ifs <;> simp).trans le_self_add
    · have hgood : QueryGoodUd P P' hκ Q' C Φ σ qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le_ud P P' hκ Q' C Φ σ qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦ ¬ Viol P' Q'
          (fun r ↦ Φ r + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
          (σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])) fun lam hlam ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        exact fun hv ↦ hlam (hJ qs lam hr hlen hv)
      rw [← hlen]
      exact_mod_cast hsub.trans hcard
  · rw [card_filter_mem, eQueryUd]
    exact add_le_add (pow_frac_le P A hA t) le_rfl

open Classical in
/-- **The query group's escape from `FarU`, with the proof of work** (S2J's PI-GRIND:
`escRet_queryFragG_le_ud`'s argument): `2^-g · eQueryUd`. -/
theorem escRet_queryFragG_le_far (g : ℕ) (hg : g ≤ 192) (P P' : LevelCode) {ℓ' : ℕ}
    (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ) (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hfar : FarU P P' hκ Q' C Φ σ)
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
  refine escRet_queryFrag_le_far P P' hκ per t c hper hpd h hW Q' C Φ σ hfar hone
    (fun g cs ↦ J g cs) fun qs lam hr hlen hv ↦ ?_
  rw [hh]
  exact hJ qs lam hr hlen hv

/-! ## The doom after the next commitment -/

section Doom

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (ℓ ℓ' pre : ℕ)
  (hκ : P.κ = ℓ' + P'.κ)

/-- **After the commitment of the next oracle**: the fold rounds' bookkeeping and `FarU` of the
next oracle's rows against the folded word. -/
def FarC (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ∃ cs₀ W', cs = cs₀ ++ [(P'.κ + P'.R, 3 * 2 ^ ℓ', W')] ∧ WellShaped (3 * 2 ^ ℓ') W' ∧
    FinBook μ i P ℓ pre r cs₀ ∧
    FarU P P' hκ (rowsOf ℓ' (laneO (i + 1) cs P'.n)) (foldedW i P r cs₀) (runW w ℓ₀ r.1)
      r.1.target

/-- After the query group: `FarC`, and every member of the next list violates the glued claim. -/
def GlueFarC (r : WhirStateT × List E) (g : List ℕ × E × List (List K))
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  FarC μ ℓ₀ w i P P' ℓ ℓ' pre hκ r cs ∧
    Viol P' (rowsOf ℓ' (laneO (i + 1) cs P'.n))
      (runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 []))
      (glueLv μ i r g.1 g.2.1 g.2.2 []).target

end Doom

section Lemmas

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {ℓ ℓ' pre : ℕ}
  {hκ : P.κ = ℓ' + P'.κ}

/-- The commitments after the next commitment, at index `i`. -/
theorem farC_word {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : FarC μ ℓ₀ w i P P' ℓ ℓ' pre hκ r cs) :
    ∃ cs₀, cs[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs₀ i) ∧ FinBook μ i P ℓ pre r cs₀ := by
  obtain ⟨cs₀, W', rfl, -, hb, -⟩ := h
  exact ⟨cs₀, shapeOK_append hb.2.1 _, hb⟩

/-- **The next level's doom** from the glued doom and the query intro polynomial (WP-7's
`levelPre_next`, from the bookkeeping only). -/
theorem levelPre_next_far (hP' : P'.κ + (pre + ℓ) + ℓ' = μ) (r : WhirStateT × List E)
    (g : List ℕ × E × List (List K)) (hq : List E) (cs : List (ℕ × ℕ × Word))
    (hglue : GlueFarC μ ℓ₀ w i P P' ℓ ℓ' pre hκ r g cs)
    (hhq : QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2)) :
    LevelPre μ ℓ₀ w (i + 1) P' ℓ' (pre + ℓ) (glueLv μ i r g.1 g.2.1 g.2.2 hq) cs := by
  obtain ⟨⟨cs₀, W', rfl, hW', ⟨⟨hl, -, -, hg, hquad⟩, hshape, hlf⟩, -⟩, hviol⟩ := hglue
  have hlen : r.1.folds.length = pre + ℓ := by omega
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

end Lemmas

/-! ## The specifications -/

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P P' : LevelCode}
  {level next : Whir.Level} {rest : List Whir.Level} {pre : ℕ} {εmax : ENNReal}

/-- The query group of a level with a next level, from `FarC` (WP-7's `midQuerySpec`, with S2J's
proof of work). -/
noncomputable def midQuerySpecFar (H : MidHyp μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hκ : P.κ = next.fold + P'.κ) (hQlt : eQueryUd P P' level.queries < 1)
    (K : ∀ s', Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirStateT × List E) :
    Spec ((queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i)).bind fun gg ↦
          midFinish μ ℓ₀ per c₀ n₀ g dir w i next rest r gg.1 gg.2.1 gg.2.2)
      (fun h ↦ FarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax ((2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries) 0 :=
  ((Spec.ofNoMove (p := queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i))
      (Pre := fun h ↦ FarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r (viewC c₀ n₀ (commits h)))
      (Post := fun gg h ↦ GlueFarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r gg
        (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_queryFragG _ _ _ _ _).noMove
      ((grind_disc_le g _).trans_lt hQlt) fun h₀ hp ↦ by
        have hp' := hp
        obtain ⟨cs₀, W₁, hcs, -, hb, hfar⟩ := hp'
        have hW : (viewC c₀ n₀ (commits h₀))[i]? = some (P.κ + P.R, wdOf i level.fold,
            wordOf cs₀ i) := by rw [hcs]; exact shapeOK_append hb.2.1 _
        have hκm := finBook_κ hb
        have hd : μ - r.1.folds.length + level.logInvRate = P.κ + P.R := by rw [hκm, H.hR]
        have hlf : r.2.length = level.fold := hb.2.2
        have hW' := commits_cidx H.hc hW
        rw [hd]
        refine escRet_queryFragG_le_far g hg P P' hκ per level.queries (cidx c₀ n₀ i) H.hper H.hpd
          h₀ hW' (rowsOf next.fold (laneO (i + 1) (viewC c₀ n₀ (commits h₀)) P'.n)) _
          (runW w ℓ₀ r.1) r.1.target hfar ((P'.card_iList_le _).trans H.hL')
          (fun gg cs ↦ GlueFarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r gg (viewC c₀ n₀ cs))
          fun qs lam hr hlen hv ↦ ⟨hp, ?_⟩
        rw [glueLv_runW, glueLv_target, enfOf_eq hb.2.1 r.2 hlf qs hr lam, hκm]
        exact hv).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun gg ↦
    (roundPolyInv (fun cs ↦ GlueFarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r gg
        (viewC c₀ n₀ cs))
        (enfOf i r.2 gg.1 gg.2.1 gg.2.2) (T := εmax) le_rfl).bind' fun hq ↦
      (K (glueLv μ i r gg.1 gg.2.1 gg.2.2 hq)).mono
        (fun h hp ↦ levelPre_next_far H.hP' r gg hq _ hp.2 hp.1) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl

/-- **After the fold rounds of a level with a next level, from no doom**: the doom is created at
the next commitment iff `FarC` holds; then the moves before the proof of work (S2J's `grindPre`),
the query group with the proof of work and the next level (`K`). -/
noncomputable def midTailFarSpec (H : MidHyp μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hκ : P.κ = next.fold + P'.κ) (hQlt : eQueryUd P P' level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries ≤ εmax)
    (K : ∀ s', Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirStateT × List E) :
    Spec (midTail μ ℓ₀ per c₀ n₀ g dir w i level next rest r) (fun _ ↦ False)
      (fun _ _ ↦ False) εmax 0 0 :=
  (Spec.commitP (Pre := fun _ ↦ False)
      (Post := fun _ h ↦ FarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r
        (viewC c₀ n₀ (commits h)))
      (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
      (fun _ _ h _ ↦ h.elim) hεQ).bind' fun _ ↦
  (grindPreInv (fun cs ↦ FarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r (viewC c₀ n₀ cs)) g
      hεQ).bind' fun _ ↦
  (midQuerySpecFar H hg hκ hQlt K r).congr
    (query_bindG per g (cidx c₀ n₀ i) (μ - r.1.folds.length + level.logInvRate) level.queries
      fun qs lam words ↦ midFinish μ ℓ₀ per c₀ n₀ g dir w i next rest r qs lam words).symm

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhir2Mid` =====

-- ===== merged from `LvmCertS2Mid` (GOLF module merge: `LvmCertS2Mid.lean` is now a stub importing `LvmCertSExt`) =====
section
-- New for lvm2 (X-REC2-CERT, stage S4): the doom of `C_rec`'s level-1 commitment in `P_S` (the third
-- part of the certificate's doom, joined to `psSpec` and `resSpec` by `Spec.or`). It creates the doom
-- at the commitment of `C_rec`'s level-1 oracle (`LvmWhir2Mid.midTailFarSpec`, `Spec.commitP`) and
-- reuses WP-7's final-level specification (`finSpec`) at level 1 after the level-0 query group.

/-!
# The level-1 commitment's doom

`psSpec`'s doom gives a good candidate `q` of `C_rec`'s root and `resSpec`'s gives `Enc₁(f₂)` in the
list of the level-1 word folded by `α₁`, but nothing ties the level-1 word to `q`. The extractor's
facts (`ud_extract_rec20`, `LvmWhirDoom2`) need **`¬ MidDoomUd`**: some member of the level-1 list
has a level-0 encoding close to the root word folded by `α₀`. This module adds that doom:

* `recMid2Spec`: a two-level stacked opening from no doom; the batching challenge, the first round
  polynomial and the level-0 fold rounds are dead; at the level-1 commitment the doom `FarC` is
  created (bookkeeping of the level-0 folds and `FarU`: every level-1 list member meeting the running
  claim is far from the folded root word), then the level-0 query group escapes with probability
  at most `eQueryUd` into `LevelPre` of level 1, and WP-7's `finSpec` (level 1) rejects except with
  its groups' probabilities (fold `eFold P₁ 4`, queries `eQueryFinal P₁ 156`, tail).
* `midSpec1`: `P_S` from no doom: roots and middle phases dead, `C_rec`'s opening by `recMid2Spec`
  (dead when the claims are not multiaffine), `C_main`'s opening dead.
* `midSpec1_D`: at the boundary right after the level-1 commitment, `FarC` is doom; `MidDoomUd`
  with the bookkeeping gives `FarC` (`farU_of_midDoom`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound
open scoped ENNReal

/-- The doom of `Spec.commitP` right after the commitment. -/
theorem commitP_D_one {Pre : List Ev → Prop} {Post : Unit → List Ev → Prop} {εmax T : ℝ≥0∞}
    (ht w : ℕ) (h : ∀ h₀ word, Pre h₀ → WellShaped w word → Post () (h₀ ++ [Ev.commit ht w word]))
    (hT : T ≤ εmax) (h₀ : List Ev) (e : Ev) :
    (Spec.commitP (Pre := Pre) (Post := Post) ht w h hT).D h₀ [e] ↔ Post () (h₀ ++ [e]) :=
  Iff.rfl

/-- A completed commitment is one commitment event. -/
theorem readCommitment_after {ht w : ℕ} {l : List Ev}
    (h : (readCommitment ht w).after l = some (.ret ())) : ∃ W, l = [Ev.commit ht w W] := by
  rcases l with _ | ⟨e, _ | ⟨e', es⟩⟩
  · simp [readCommitment, VerifierProgram.after] at h
  · cases e <;> simp [readCommitment, VerifierProgram.after] at h
    rename_i h' w' W
    exact ⟨W, by simp_all⟩
  · cases e <;> simp [readCommitment, VerifierProgram.after] at h

/-! ## A two-level stacked opening, doom at the level-1 commitment -/

section Mid2

variable (cfg : UdConfig) (level next : LeanVM.Parameters.Whir.Level)
  (hc : cfg.levels = [level, next]) (P₀ P₁ : LevelCode)
  (cl : List LeanVM.Protocol.Verifier.StackClaim) {εmax : ℝ≥0∞}
  (H : ∀ ρ, MidHyp cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ (batW cl ρ) P₀ P₁ level next 0)
  (hg : cfg.grind ≤ 192) (hκ : P₀.κ = next.fold + P₁.κ)
  (hQlt : eQueryUd P₀ P₁ level.queries < 1)
  (hεQ : (2 : ℝ≥0∞)⁻¹ ^ cfg.grind * eQueryUd P₀ P₁ level.queries ≤ εmax)
  (K : ∀ ρ s', Spec (whirLevelsUd cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ cfg.grind cfg.direct
      (batW cl ρ)
      (0 + 1) [next] s')
    (fun h ↦ LevelPre cfg.μ level.fold (batW cl ρ) (0 + 1) P₁ next.fold (0 + level.fold) s'
      (viewC cfg.c₀ cfg.n₀ (commits h)))
    (fun _ _ ↦ False) εmax εmax 0)

/-- **A two-level stacked opening from no doom**, doom created at the level-1 commitment. -/
noncomputable def recMid2Spec :
    Spec (verifyStackedUd cfg cl) (fun _ ↦ False) (fun _ _ ↦ False) εmax 0 0 :=
  Spec.congr (stacked_two_eq cfg level next hc cl).symm
    ((Spec.dead (p := sampleChallenge) (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun ρ ↦
      (Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun quad ↦
        (Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun r ↦
          midTailFarSpec (H ρ) hg hκ hQlt hεQ (K ρ) r)

/-- **The doom right after the level-1 commitment** is `FarC`. -/
theorem recMid2Spec_D {h₀ lq lf lc : List Ev} {ρ : E} {quad : List E} {r : WhirStateT × List E}
    (hq : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl ρ) none).after lq =
      some (.ret quad))
    (hf : (foldRoundsT level.fold ⟨batT cl ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (cfg.μ - r.1.folds.length - next.fold + next.logInvRate)
      (3 * 2 ^ next.fold)).after lc = some (.ret ())) :
    (recMid2Spec cfg level next hc P₀ P₁ cl H hg hκ hQlt hεQ K).D h₀
        ([Ev.sample ρ] ++ (lq ++ (lf ++ lc))) ↔
      FarC cfg.μ level.fold (batW cl ρ) 0 P₀ P₁ level.fold next.fold 0 hκ r
        (viewC cfg.c₀ cfg.n₀ (commits (h₀ ++ [Ev.sample ρ] ++ lq ++ lf ++ lc))) := by
  obtain ⟨W, rfl⟩ := readCommitment_after hcm
  rw [recMid2Spec, Spec.congr_D, bind_D_after _ _ (rfl : sampleChallenge.after [Ev.sample ρ] = _)
    (by simp), bind_D_after _ _ hq (by simp), bind_D_after _ _ hf (by simp), midTailFarSpec,
    show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_ret _ _ hcm, commitP_D_one]
  constructor
  · exact fun h ↦ by simpa only [List.append_assoc] using h.1
  · intro h
    have h' : FarC cfg.μ level.fold (batW cl ρ) 0 P₀ P₁ level.fold next.fold 0 hκ r
        (viewC cfg.c₀ cfg.n₀ (commits (h₀ ++ [Ev.sample ρ] ++ lq ++ lf ++
          [Ev.commit (cfg.μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
            W]))) := h
    simp only [List.append_assoc] at h' ⊢
    exact ⟨h', Spec.start_D _ _ (by simpa only [List.append_nil] using h')⟩

end Mid2

/-! ## P20 -/

theorem midHyp0_rec20 (cl : List LeanVM.Protocol.Verifier.StackClaim)
    (hcl : ∀ c ∈ cl, IsMultiaffine 19 c.1) (ρ : E) :
    MidHyp cfgRec20G.μ recLevel0.fold cfgRec20G.per cfgRec20G.c₀ cfgRec20G.n₀ (batW cl ρ)
      (codesRec20 0) (codesRec20 1) recLevel0 recLevel1 0 :=
  ⟨isMultiaffine_batched cl hcl ρ, by decide, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    le_rfl⟩

/-- `C_rec`'s level-0 message variables: the level-1 fold and the level-1 code's. -/
theorem hκ_rec20 : (codesRec20 0).κ = recLevel1.fold + (codesRec20 1).κ := rfl

theorem hQlt0_20 : eQueryUd (codesRec20 0) (codesRec20 1) recLevel0.queries < 1 :=
  eQuery_rec20G.1.trans_lt (inv_two_pow_lt_one (by norm_num))

theorem hεQ0_20 :
    (2 : ℝ≥0∞)⁻¹ ^ cfgRec20G.grind * eQueryUd (codesRec20 0) (codesRec20 1) recLevel0.queries ≤ εS :=
  (disc_le 14 eQuery_rec20G.1).trans pow129_le_εS

theorem hεF1_20 : eFold (codesRec20 1) recLevel1.fold ≤ εS :=
  (eFold_rec20_1.trans (inv_two_pow_anti (by norm_num))).trans pow129_le_εS

section Concrete

attribute [local irreducible] verifyStackedUd verifyStackedJ recMid2Spec midTailFarSpec finSpec

/-- WP-7's final-level specification at `C_rec`'s level 1 (P20). -/
noncomputable def fin1_20 (cl : List LeanVM.Protocol.Verifier.StackClaim)
    (hcl : ∀ c ∈ cl, IsMultiaffine 19 c.1) (ρ : E) (s' : WhirStateT) :
    Spec (whirLevelsUd cfgRec20G.μ recLevel0.fold cfgRec20G.per cfgRec20G.c₀ cfgRec20G.n₀
        cfgRec20G.grind cfgRec20G.direct (batW cl ρ) (0 + 1) [recLevel1] s')
      (fun h ↦ LevelPre cfgRec20G.μ recLevel0.fold (batW cl ρ) (0 + 1) (codesRec20 1)
        recLevel1.fold (0 + recLevel0.fold) s' (viewC cfgRec20G.c₀ cfgRec20G.n₀ (commits h)))
      (fun _ _ ↦ False) εS εS 0 :=
  finSpec (finHyp1_rec20 cl hcl ρ) hg20 hεF1_20 hQlt1_20 hεQ1_20 hεT20 s'

end Concrete

end Lvm.ASM
end
-- ===== end of `LvmCertS2Mid` =====

/-!
# The extraction and the knowledge certificate of the `S` branch (two-level `C_rec`)

* `accept_split`: an accepted history of `P_S` is the roots, the middle phases, `C_rec`'s batching
  challenge, first round polynomial, level-0 fold rounds, level-1 commitment, level-0 query group,
  query intro polynomial, level-1 fold rounds and final residual, then the rest.
* `recData2 mid x h`: `C_rec`'s level-0 fold state `r₀` (`α₀ = r₀.2`), level-1 fold state `r₁`
  (`α₁ = r₁.2`) and final residual, read off `h` by the same splits; `WrOf h`, `Wr1Of h`: `C_rec`'s
  root word (commitment 1) and level-1 word (commitment 2).
* `SPS`: the certificate's doom `psSpec ∨ resSpec ∨ midSpec1` (statement, final residual, level-1
  commitment).
* **`decodeFacts_S`**: at an accepted history, not lucky and outside doom at every boundary, a good
  pair `(qm, qr)` and the decoders' hypotheses on the history's values: `¬ CommitDoomUd`,
  `¬ MidDoomUd`, `¬ FinalDoomL`, no fold luck at either level, well-shaped words.
* **`extS`**, `decode_S`, `extract_S`: level 1 is decoded first (`decodeRec1` on `Wr1Of h`, `α₁`,
  `f₂`), its output is the level-0 residual input of `decodeRec` (on `WrOf h`, `α₀`); with
  `ud_extract_rec20` the result is the good candidate's words.
* **`kcertS`**: `KCert (schemeS vk (PSWith mid)) (Rel (accV VS vk))` with `ε = 2^-129`,
  `εB = 2^-130` (so `εFS ≤ 2^-128`), from `MidSpec`, `MidShape` and `NodeSound`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud
open scoped NNReal ENNReal

variable {α β : Type}

/-! ## Facts about runs -/

theorem MovesOnly.after_samples {p q : VerifierProgram α} (hp : p.MovesOnly) {l : List Ev}
    (h : p.after l = some q) : l.filterMap sampleOf = [] := by
  induction l generalizing p with
  | nil => rfl
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | exact ih (hp _) h
      | exact (hp : False).elim
      | (refine ih ?_ h; exact hp)
      | (split_ifs at h; refine ih ?_ h; exact hp)

theorem NoCommit.after_commits {p q : VerifierProgram α} (hp : p.NoCommit) {l : List Ev}
    (h : p.after l = some q) : commits l = [] := by
  induction l generalizing p with
  | nil => rfl
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | exact ih (hp _) h
      | exact (hp : False).elim
      | (refine ih ?_ h; exact hp)
      | (split_ifs at h; refine ih ?_ h; exact hp)

theorem readScalars_after_len : ∀ (n : ℕ) {l : List Ev} {xs : List E},
    (readScalars n).after l = some (.ret xs) → xs.length = n
  | 0, l, xs, h => by
    cases l with
    | nil => simp [readScalars, VerifierProgram.after] at h; subst h; rfl
    | cons e es => cases e <;> simp [readScalars, VerifierProgram.after] at h
  | n + 1, l, xs, h => by
    obtain ⟨y, l₁, l₂, rfl, -, h2⟩ := after_bind_ret (p := readScalar) h
    obtain ⟨ys, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
    have := readScalars_after_len n h3
    cases m₂ with
    | nil => simp [VerifierProgram.after] at h4; subst h4; simp [this]
    | cons e es => cases e <;> simp [VerifierProgram.after] at h4

theorem sample_after {l : List Ev} {c : E} (h : sampleChallenge.after l = some (.ret c)) :
    l = [Ev.sample c] := by
  rcases l with _ | ⟨e, _ | ⟨e', es⟩⟩
  · simp [sampleChallenge, VerifierProgram.after] at h
  · cases e <;> simp [sampleChallenge, VerifierProgram.after] at h; subst h; rfl
  · cases e <;> cases e' <;> simp [sampleChallenge, VerifierProgram.after] at h

theorem movesOnly_ret (a : α) : (VerifierProgram.ret a).MovesOnly := trivial

theorem movesOnly_roundPoly (t : E) :
    (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 t none).MovesOnly := by
  unfold LeanVM.Protocol.Verifier.sumcheckRoundPoly
  exact MovesOnly.bind (p := readScalar) (fun _ ↦ trivial) fun _ ↦
    MovesOnly.bind (movesOnly_readScalars _) fun _ ↦ movesOnly_ret _

/-- The plain round polynomial of three coefficients meets its claim. -/
theorem roundPoly_after {t : E} {l : List Ev} {q : List E}
    (h : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 t none).after l = some (.ret q)) :
    QuadOK q t := by
  unfold LeanVM.Protocol.Verifier.sumcheckRoundPoly at h
  obtain ⟨c₀, l₁, l₂, rfl, -, h2⟩ := after_bind_ret (p := readScalar) h
  obtain ⟨tl, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
  have hl := readScalars_after_len _ h3
  cases m₂ with
  | nil =>
    simp [VerifierProgram.after] at h4; subst h4
    obtain ⟨c₂, rfl⟩ : ∃ c₂, tl = [c₂] := by
      rcases tl with _ | ⟨a, _ | ⟨b, t'⟩⟩ <;> simp at hl ⊢
    exact quadOK_roundPoly t c₀ c₂
  | cons e es => cases e <;> simp [VerifierProgram.after] at h4

/-- **The fold rounds' state**: the challenges are the samples of the run. -/
theorem foldRoundsT_after : ∀ (n : ℕ) (s : WhirStateT) (lf : List E) {l : List Ev}
    {r : WhirStateT × List E}, (foldRoundsT n s lf).after l = some (.ret r) →
      r.2 = lf ++ l.filterMap sampleOf ∧ (l.filterMap sampleOf).length = n ∧
        r.1.folds = s.folds ++ l.filterMap sampleOf ∧ r.1.glued = s.glued ∧
        (0 < n → QuadOK r.1.quad r.1.target)
  | 0, s, lf, l, r, h => by
    cases l with
    | nil => simp [foldRoundsT, VerifierProgram.after] at h; subst h; simp
    | cons e es => cases e <;> simp [foldRoundsT, VerifierProgram.after] at h
  | n + 1, s, lf, l, r, h => by
    unfold foldRoundsT at h
    obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
    obtain rfl := sample_after h1
    obtain ⟨quad, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
    have hs3 := MovesOnly.after_samples (movesOnly_roundPoly _) h3
    obtain ⟨e1, e2, e3, e4, e5⟩ := foldRoundsT_after n _ _ h4
    simp only [List.filterMap_append, hs3, List.nil_append] at e1 e2 e3 ⊢
    refine ⟨by rw [e1]; simp [sampleOf], by simp [sampleOf, e2], by rw [e3]; simp [sampleOf],
      e4, fun _ ↦ ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · cases m₂ with
      | nil =>
        simp [foldRoundsT, VerifierProgram.after] at h4; subst h4
        exact roundPoly_after h3
      | cons e es => cases e <;> simp [foldRoundsT, VerifierProgram.after] at h4
    · exact e5 hn

theorem roots_after {l : List Ev} (h : rootsProg.after l = some (.ret ())) :
    ∃ W₁ W₂, l = [Ev.commit 19 64 W₁, Ev.commit 15 64 W₂] := by
  rcases l with _ | ⟨e₁, _ | ⟨e₂, _ | ⟨e₃, es⟩⟩⟩
  · simp [rootsProg, commitRootUd, cfgMain24G, cfgRec20G, VerifierProgram.readCommitment,
      VerifierProgram.bind, VerifierProgram.after] at h
  · cases e₁ <;> simp [rootsProg, commitRootUd, cfgMain24G, cfgRec20G, VerifierProgram.readCommitment,
      VerifierProgram.bind, VerifierProgram.after] at h
  · cases e₁ <;> cases e₂ <;> simp [rootsProg, commitRootUd, cfgMain24G, cfgRec20G,
      VerifierProgram.readCommitment, VerifierProgram.bind, VerifierProgram.after] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    exact ⟨_, _, rfl⟩
  · cases e₁ <;> cases e₂ <;> cases e₃ <;> simp [rootsProg, commitRootUd, cfgMain24G, cfgRec20G,
      VerifierProgram.readCommitment, VerifierProgram.bind, VerifierProgram.after] at h

/-- The words a reachable history commits are well shaped. -/
theorem reachable_commit_ws {p : VerifierProgram α} {h : List Ev} (hr : p.Reachable h) :
    ∀ ht w W, Ev.commit ht w W ∈ h → WellShaped w W := by
  induction hr with
  | nil => simp
  | read x _ _ ih | sample x _ _ ih =>
    intro ht w W hm; rcases List.mem_append.1 hm with hm | hm
    · exact ih _ _ _ hm
    · simp at hm
  | grind _ _ ih | query _ _ _ ih =>
    intro ht w W hm; rcases List.mem_append.1 hm with hm | hm
    · exact ih _ _ _ hm
    · simp at hm
  | commit word _ ha hw ih =>
    intro ht w W hm; rcases List.mem_append.1 hm with hm | hm
    · exact ih _ _ _ hm
    · simp only [List.mem_singleton, Ev.commit.injEq] at hm
      obtain ⟨-, rfl, rfl⟩ := hm
      exact hw

/-- A run of a program of scalar reads only is scalar reads. -/
theorem reads_of_after {p q : VerifierProgram α} (hm : p.MovesOnly) (hc : p.NoCommit)
    (hg : p.NoGrind) {l : List Ev} (h : p.after l = some q) : ∀ e ∈ l, ∃ y, e = Ev.read y := by
  induction l generalizing p with
  | nil => simp
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | (intro e' he'
         rcases List.mem_cons.1 he' with rfl | he'
         · exact ⟨_, rfl⟩
         · exact ih (hm _) (hc _) (hg _) h e' he')
      | exact (hm : False).elim
      | exact (hc : False).elim
      | exact (hg : False).elim

theorem readScalars_reads (n : ℕ) {l : List Ev} {q : VerifierProgram (List E)}
    (h : (readScalars n).after l = some q) : ∀ e ∈ l, ∃ y, e = Ev.read y :=
  reads_of_after (movesOnly_readScalars n) (nc_readScalars n) (ng_readScalars n) h

theorem queryOpenings_after {i : ℕ} {ps : List ℕ} {l : List Ev} {w : List (List K)}
    (h : (queryOpenings i ps).after l = some (.ret w)) : l = [Ev.query w] := by
  rcases l with _ | ⟨e, _ | ⟨e', es⟩⟩
  · simp [queryOpenings, VerifierProgram.after] at h
  · cases e <;> simp [queryOpenings, VerifierProgram.after] at h; subst h; rfl
  · cases e <;> cases e' <;> simp [queryOpenings, VerifierProgram.after] at h

/-- The challenges of a completed run of the positions: one per `per` positions. -/
def posCount (per : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, rem => if rem = 0 then 0 else posCount per fuel (rem - min per rem) + 1

theorem samplePositionsAux_after (per depth : ℕ) : ∀ (fuel rem : ℕ) {l : List Ev} {qs : List ℕ},
    (samplePositionsAux per depth fuel rem).after l = some (.ret qs) →
      (l.filterMap sampleOf).length = posCount per fuel rem
  | 0, rem, l, qs, h => by
    cases l with
    | nil => rfl
    | cons e es => cases e <;> simp [samplePositionsAux, VerifierProgram.after] at h
  | fuel + 1, rem, l, qs, h => by
    unfold samplePositionsAux at h
    by_cases hr : rem = 0
    · rw [if_pos hr] at h
      cases l with
      | nil => simp [posCount, hr]
      | cons e es => cases e <;> simp [VerifierProgram.after] at h
    · rw [if_neg hr] at h
      obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
      obtain rfl := sample_after h1
      obtain ⟨rest, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
      have := samplePositionsAux_after per depth fuel _ h3
      cases m₂ with
      | nil => simp [posCount, hr, List.filterMap_append, this, sampleOf]
      | cons e es => cases e <;> simp [VerifierProgram.after] at h4

/-- **The query group's challenges**: the positions' and `λ`. -/
theorem queryFrag_after_samples {per d t c : ℕ} {l : List Ev} {g : List ℕ × E × List (List K)}
    (h : (queryFrag per d t c).after l = some (.ret g)) :
    (l.filterMap sampleOf).length = posCount per t t + 1 := by
  unfold queryFrag at h
  obtain ⟨qs, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret h
  obtain ⟨lam, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
  obtain rfl := sample_after h3
  obtain ⟨w, n₁, n₂, rfl, h5, h6⟩ := after_bind_ret h4
  obtain rfl := queryOpenings_after h5
  have := samplePositionsAux_after per d t t h1
  cases n₂ with
  | nil => simp [List.filterMap_append, this, sampleOf]
  | cons e es => cases e <;> simp [VerifierProgram.after] at h6

theorem nc_queryFrag (per d t c : ℕ) : (queryFrag per d t c).NoCommit :=
  NoCommit.bind (nc_samplePositions _ _ _) fun _ ↦ NoCommit.bind nc_sample fun _ ↦
    NoCommit.bind (nc_query _ _) fun _ ↦ nc_ret _

theorem require_after {c : Prop} [Decidable c] {l : List Ev}
    (h : (VerifierProgram.require c).after l = some (.ret ())) : l = [] := by
  unfold VerifierProgram.require at h
  split at h
  · cases l with
    | nil => rfl
    | cons e es => cases e <;> simp [VerifierProgram.after] at h
  · cases l with
    | nil => simp [VerifierProgram.after] at h
    | cons e es => cases e <;> simp [VerifierProgram.after] at h

/-- **The query group with the proof of work** (S2J, `g ≠ 0`): the PoW challenge, the positions'
challenges and `λ`. -/
theorem queryFragG_after_samples {g per d t c : ℕ} (hg : g ≠ 0) {l : List Ev}
    {gg : List ℕ × E × List (List K)} (h : (queryFragG g per d t c).after l = some (.ret gg)) :
    (l.filterMap sampleOf).length = posCount per t t + 2 := by
  unfold queryFragG powCheck at h
  rw [if_neg hg, VerifierProgram.bind_assoc] at h
  obtain ⟨c', l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
  obtain rfl := sample_after h1
  obtain ⟨_, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
  obtain rfl := require_after h3
  have := queryFrag_after_samples h4
  simp only [List.filterMap_append, this, List.nil_append, List.length_append]
  simp [sampleOf]
  omega

/-- **The moves before the proof of work** (S2J, `g ≠ 0`): the separating challenge and the nonce. -/
theorem grindPre_after_samples {g : ℕ} (hg : g ≠ 0) {l : List Ev}
    (h : (grindPre g).after l = some (.ret ())) : (l.filterMap sampleOf).length = 1 := by
  unfold grindPre at h
  rw [if_neg hg] at h
  obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
  obtain rfl := sample_after h1
  obtain ⟨y, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret (p := readScalar) h2
  have := MovesOnly.after_samples (p := readScalar) (fun _ ↦ trivial) h3
  cases m₂ with
  | nil => simp [List.filterMap_append, this, sampleOf]
  | cons e es => cases e <;> simp [VerifierProgram.after, pure] at h4

/-- The level-0 query group of `C_rec` with the proof of work (S2J P20, `g = 14`): `25` challenges
(separating, PoW, `22` positions' challenges for `170` positions, `λ`). -/
theorem qgRec_after_samples {d c : ℕ} {l : List Ev} {gg : List ℕ × E × List (List K)}
    (h : ((grindPre 14).bind fun _ ↦ queryFragG 14 8 d 170 c).after l = some (.ret gg)) :
    (l.filterMap sampleOf).length = 25 := by
  obtain ⟨_, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret h
  rw [List.filterMap_append, List.length_append, grindPre_after_samples (by decide) h1,
    queryFragG_after_samples (by decide) h2]
  rfl

theorem nc_qgRec (d c : ℕ) : ((grindPre 14).bind fun _ ↦ queryFragG 14 8 d 170 c).NoCommit :=
  NoCommit.bind (nc_grindPre _) fun _ ↦ NoCommit.bind (nc_powCheck _) fun _ ↦ nc_queryFrag _ _ _ _

/-- The first commitment after a commitment-free prefix. -/
theorem splitCommit_of_noCommit : ∀ (pre : List Ev), commits pre = [] → ∀ ht w W b,
    splitCommit (pre ++ Ev.commit ht w W :: b) = some (W, b)
  | [], _, _, _, _, _ => rfl
  | e :: pre, h, ht, w, W, b => by
    cases e with
    | commit => simp [commits] at h
    | _ =>
      simp only [List.cons_append, splitCommit]
      exact splitCommit_of_noCommit pre (by simpa [commits] using h) ht w W b

theorem gluedOK_of_folds {μ : ℕ} {s s' : WhirStateT} (hg : GluedOK μ s) (hgl : s'.glued = s.glued)
    (hfl : s.folds.length ≤ s'.folds.length) : GluedOK μ s' := by
  intro c hc
  rw [hgl] at hc
  exact ⟨(hg c hc).1.trans hfl, (hg c hc).2⟩

/-! ## The history's values -/

/-- **`C_rec`'s fold states and final residual**, read off a history (the splits of
`accept_split`): the level-0 fold state `r₀` (`α₀ = r₀.2`), the level-1 fold state `r₁`
(`α₁ = r₁.2`) and the residual. -/
def recData2 (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    Option ((WhirStateT × List E) × (WhirStateT × List E) × List E) :=
  match rootsProg.retSplit h with
  | none => none
  | some (_, _, l₂) => match (mid x).retSplit l₂ with
    | none => none
    | some (cl, _, l₃) => match sampleChallenge.retSplit l₃ with
      | none => none
      | some (ρ, _, l₄) =>
        match (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).retSplit l₄ with
        | none => none
        | some (quad, _, l₅) =>
          match (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).retSplit l₅ with
          | none => none
          | some (r, _, l₆) =>
            match (readCommitment (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4)).retSplit l₆ with
            | none => none
            | some (_, _, l₇) =>
              match ((grindPre 14).bind fun _ ↦ queryFragG 14 8 (19 - r.1.folds.length + 2) 170 (cidx 1 2 0)).retSplit l₇ with
              | none => none
              | some (g, _, l₈) => match (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3
                  (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).retSplit l₈ with
                | none => none
                | some (hq, _, l₉) =>
                  match (foldRoundsT 4 (glueLv 19 0 r g.1 g.2.1 g.2.2 hq) []).retSplit l₉ with
                  | none => none
                  | some (r₁, _, l₁₀) =>
                    match (readScalars (2 ^ (19 - r₁.1.folds.length))).retSplit l₁₀ with
                    | none => none
                    | some (res, _, _) => some (r, r₁, res)

/-- **`C_rec`'s level-1 word** (commitment `2`). -/
def Wr1Of (h : List Ev) : Compile.Word := wordOf (commits h) 2

section Split

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}
  {hr lm lq lf lc lg lhq lf1 lres rest : List Ev} {cl : OpenClaims} {ρ : E} {quad hq res : List E}
  {r r₁ : WhirStateT × List E} {g : List ℕ × E × List (List K)}
  (h1 : rootsProg.after hr = some (.ret ())) (h3 : (mid x).after lm = some (.ret cl))
  (h8 : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq =
    some (.ret quad))
  (h10 : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
  (hcm : (readCommitment (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4)).after lc = some (.ret ()))
  (hg : ((grindPre 14).bind fun _ ↦ queryFragG 14 8 (19 - r.1.folds.length + 2) 170 (cidx 1 2 0)).after lg = some (.ret g))
  (hh : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).after
    lhq = some (.ret hq))
  (hf1 : (foldRoundsT 4 (glueLv 19 0 r g.1 g.2.1 g.2.2 hq) []).after lf1 = some (.ret r₁))
  (hres : (readScalars (2 ^ (19 - r₁.1.folds.length))).after lres = some (.ret res))
include h1 h3 h8 h10 hcm hg hh hf1 hres

theorem recData2_split :
    recData2 mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
      (lres ++ rest)))))))))) = some (r, r₁, res) := by
  unfold recData2
  rw [retSplit_of_after _ _ _ h1]
  dsimp only
  rw [retSplit_of_after _ _ _ h3]
  dsimp only
  rw [retSplit_of_after sampleChallenge [Ev.sample ρ] _ rfl]
  dsimp only
  rw [retSplit_of_after _ _ _ h8]
  dsimp only
  rw [retSplit_of_after _ _ _ h10]
  dsimp only
  rw [retSplit_of_after _ _ _ hcm]
  dsimp only
  rw [retSplit_of_after _ _ _ hg]
  dsimp only
  rw [retSplit_of_after _ _ _ hh]
  dsimp only
  rw [retSplit_of_after _ _ _ hf1]
  dsimp only
  rw [retSplit_of_after _ _ _ hres]

omit h3 h8 h10 hcm hg hh hf1 hres in
theorem rootsOf_split (l : List Ev) : rootsOf (hr ++ l) = hr := by
  unfold rootsOf
  rw [retSplit_of_after _ _ _ h1]

/-- **The level-0 fold challenges read by the luck are the run's.** -/
theorem foldChal_split :
    foldChal mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
      (lres ++ rest)))))))))) = r.2 := by
  obtain ⟨e1, e2, -⟩ := foldRoundsT_after 6 _ [] h10
  rw [List.nil_append] at e1
  have hq := MovesOnly.after_samples (movesOnly_roundPoly _) h8
  unfold foldChal afterMid
  rw [retSplit_of_after _ _ _ h1]
  dsimp only
  rw [retSplit_of_after _ _ _ h3]
  dsimp only
  simp only [List.filterMap_append, hq, ← e1, List.nil_append]
  rw [show [Ev.sample ρ].filterMap sampleOf = [ρ] from rfl, List.singleton_append, List.drop_one,
    List.tail_cons, List.take_append_of_le_length (by rw [e1, e2]),
    List.take_of_length_le (by rw [e1, e2])]

/-- **`C_rec`'s level-1 commitment as the luck reads it** is the run's. -/
theorem rec1Of_split {W : Compile.Word} {ht w : ℕ} (hlc : lc = [Ev.commit ht w W]) :
    rec1Of mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
      (lres ++ rest)))))))))) = some (W, lg ++ (lhq ++ (lf1 ++ (lres ++ rest)))) := by
  have hcq := NoCommit.after_commits (nc_roundPoly _ _ _) h8
  have hcf := NoCommit.after_commits (nc_foldRoundsT _ _ _) h10
  unfold rec1Of afterMid
  rw [retSplit_of_after _ _ _ h1]
  dsimp only
  rw [retSplit_of_after _ _ _ h3]
  dsimp only
  subst hlc
  have := splitCommit_of_noCommit ([Ev.sample ρ] ++ lq ++ lf) (by
    simp only [commits_append, hcq, hcf]; rfl) ht w W (lg ++ (lhq ++ (lf1 ++ (lres ++ rest))))
  simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using this

/-- **The level-1 fold challenges read by the luck are the run's.** -/
theorem foldChal1_split {W : Compile.Word} {ht w : ℕ} (hlc : lc = [Ev.commit ht w W]) :
    foldChal1 mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
      (lres ++ rest)))))))))) = r₁.2 := by
  obtain ⟨e1, e2, -⟩ := foldRoundsT_after 4 _ [] hf1
  rw [List.nil_append] at e1
  have hgs := qgRec_after_samples hg
  have hhs := MovesOnly.after_samples (movesOnly_roundPoly _) hh
  have hrs := MovesOnly.after_samples (movesOnly_readScalars _) hres
  unfold foldChal1
  rw [rec1Of_split h1 h3 h8 h10 hcm hg hh hf1 hres hlc]
  dsimp only
  have h25 : (lg.filterMap sampleOf).length = 25 := hgs
  simp only [List.filterMap_append, hhs, hrs, ← e1, List.nil_append]
  rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
    List.nil_append, List.take_append_of_le_length (by rw [e1, e2]),
    List.take_of_length_le (by rw [e1, e2])]

/-- The level-1 word read by the luck is the run's. -/
theorem W1L_split {W : Compile.Word} {ht w : ℕ} (hlc : lc = [Ev.commit ht w W]) :
    W1L mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
      (lres ++ rest)))))))))) = W :=
  W1L_of_rec1Of (rec1Of_split h1 h3 h8 h10 hcm hg hh hf1 hres hlc)

end Split

theorem boundary_of_last_read {h : List Ev} {y : E} (hy : h.getLast? = some (Ev.read y)) :
    Boundary h := by
  cases h with
  | nil => simp at hy
  | cons e es =>
    unfold Boundary
    simp only [hy]

theorem boundary_of_last_commit {h : List Ev} {ht w : ℕ} {W : Compile.Word}
    (hy : h.getLast? = some (Ev.commit ht w W)) : Boundary h := by
  cases h with
  | nil => simp at hy
  | cons e es =>
    unfold Boundary
    simp only [hy]

/-! ## The extraction map (O11) -/

/-- The column of a decoded word list (zero when decoding fails). -/
def colOf (o : Option (List K)) : Column 19 := ⟨Vector.ofFn fun i ↦ (o.getD []).getD i 0⟩

theorem colOf_msgOf (q : Column 19) :
    colOf (some ((List.range (2 ^ 19)).map (Lvm.X.msgOf q))) = q := by
  rcases q with ⟨v⟩
  unfold colOf
  rw [Option.getD_some]
  refine congrArg Column.mk (Vector.ext fun i hi ↦ ?_)
  rw [Vector.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi)]
  rw [List.getElem_map, List.getElem_range]
  unfold Lvm.X.msgOf
  show Vector.getD v i 0 = v[i]
  unfold Vector.getD
  rw [Array.getD_eq_getD_getElem?]
  simp only [Vector.getElem?_toArray]
  rw [Vector.getElem?_eq_getElem hi]
  rfl

/-! ## The doom after the roots, and at the start -/

theorem rootsProg_after_roots (W₁ W₂ : Compile.Word) :
    rootsProg.after [Ev.commit 19 64 W₁, Ev.commit 15 64 W₂] = some (.ret ()) := by
  simp [rootsProg, commitRootUd, cfgMain24G, cfgRec20G, VerifierProgram.readCommitment,
    VerifierProgram.bind, VerifierProgram.after]

theorem rootsProg_ne_ret (a : Unit) : rootsProg ≠ .ret a := by
  simp [rootsProg, commitRootUd, cfgMain24G, VerifierProgram.readCommitment, VerifierProgram.bind]

theorem after_nil' (p : VerifierProgram α) : p.after [] = some p := by simp [VerifierProgram.after]

/-! ## The decoders' hypotheses from the doom (P20) -/

/-- The level-0 folded word of `C_rec`'s opening is the fold of the root's lane rows. -/
theorem foldedW0_eq {r : WhirStateT × List E} (hlen : r.2.length = EndToEnd.laneBits) (W₀ : Compile.Word)
    (rest : List (ℕ × ℕ × Compile.Word)) :
    foldedW 0 (codesRec20 0) r ((15, 64, W₀) :: rest) =
      foldAll (fun i : Fin EndToEnd.laneBits ↦ r.2.getD i 0) (laneRows 19 2 W₀) Fin.elim0 := by
  have h1 := rowsOf_foldsN_eq_foldAll EndToEnd.laneBits r.2 hlen
    (laneO 0 ((15, 64, W₀) :: rest) (2 ^ (19 - EndToEnd.laneBits + 2)))
  rw [rowsOf_laneO_zero 19 2, rowsOf_zero] at h1
  exact congrFun h1 Fin.elim0

/-- The level-1 folded word of `C_rec`'s opening is the fold of the level-1 rows. -/
theorem foldedW1_eq {r₁ : WhirStateT × List E} (hlen : r₁.2.length = 4)
    (cs : List (ℕ × ℕ × Compile.Word)) :
    (fun _ : Fin 0 → Bool ↦ foldedW 1 (codesRec20 1) r₁ cs) =
      foldAll (fun i : Fin 4 ↦ r₁.2.getD i 0) (rows1 4 (codesRec20 1).n (wordOf cs 1)) := by
  have h1 := rowsOf_foldsN_eq_foldAll 4 r₁.2 hlen (laneO 1 cs (codesRec20 1).n)
  rw [rowsOf_zero] at h1
  exact h1

/-- **The level-1 commitment's doom from the extractor's**: with the level-0 bookkeeping,
`MidDoomUd` of the history's words is `FarC` of the opening's view. -/
theorem farC_of_midDoom20 {w : List E → E} {r : WhirStateT × List E} {W₀ W₁ : Compile.Word} {ht : ℕ}
    (hlen : r.2.length = 6) (hfl : r.1.folds.length = 6) (hgl : r.1.glued = [])
    (hquad : QuadOK r.1.quad r.1.target) (hW₀ : WellShaped 64 W₀) (hW₁ : WellShaped (3 * 2 ^ 4) W₁)
    (hht : ht = 12)
    (hD : MidDoomUd (udThr 13 2) (codesRec20 1) (by rfl : 19 - EndToEnd.laneBits = 4 + (codesRec20 1).κ)
      (foldAll (fun i : Fin EndToEnd.laneBits ↦ r.2.getD i 0) (laneRows 19 2 W₀) Fin.elim0)
      (rows1 4 (codesRec20 1).n W₁)) :
    FarC 19 6 w 0 (codesRec20 0) (codesRec20 1) 6 4 0 hκ_rec20 r
      [(15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)] := by
  subst hht
  refine ⟨[(15, 64, W₀)], W₁, rfl, hW₁, ⟨⟨by rw [hfl, hlen], by rw [hlen], rfl, ?_, hquad⟩,
    ⟨rfl, W₀, rfl, hW₀⟩, hlen⟩, ?_⟩
  · intro c hc; rw [hgl] at hc; simp at hc
  · rw [foldedW0_eq hlen W₀ []]
    exact farU_of_midDoom _ _ _ _ _ _ _ hD

/-- `FinalDoomL` from the final level's `FinViol` (generic in the code). -/
theorem not_finalDoomL_of_not_finViol {P : LevelCode} {ℓ : ℕ} {Q' : (Fin ℓ → Bool) → Fin P.n → E}
    {α : Fin ℓ → E} {C : Fin P.n → E} {Φ : List E → E} {σ : E} {f : (Fin P.κ → Bool) → E}
    (hC : (fun _ : Fin 0 → Bool ↦ C) = foldAll α Q') (h : ¬ FinViol P C Φ σ f) :
    ¬ FinalDoomL P Q' α f := by
  simp only [FinViol, not_or, not_not] at h
  rw [hC] at h
  exact not_not.mpr h.2

/-- **The final residual's doom from the specification's** at `C_rec`'s level 1: with the
bookkeeping, not `ResC` gives not `FinalDoomL`. -/
theorem not_finalDoomL20 {w : List E → E} {r₁ : WhirStateT × List E} {res : List E} {W₀ W₁ : Compile.Word}
    {ht : ℕ} (hlen : r₁.2.length = 4) (hfl : r₁.1.folds.length = 10) (hgl : GluedOK 19 r₁.1)
    (hquad : QuadOK r₁.1.quad r₁.1.target) (hW₁ : WellShaped (3 * 2 ^ 4) W₁) (hht : ht = 12)
    (hres : res.length = 2 ^ (19 - r₁.1.folds.length))
    (hn : ¬ ResC 19 6 w 1 (codesRec20 1) 4 6 r₁ res [(15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)]) :
    ¬ FinalDoomL (codesRec20 1) (rows1 4 (codesRec20 1).n W₁) (fun i : Fin 4 ↦ r₁.2.getD i 0)
      (resMsg res) := by
  subst hht
  have hbook : res.length = 2 ^ (19 - r₁.1.folds.length) ∧
      FinBook 19 1 (codesRec20 1) 4 6 r₁ [(15, 64, W₀), (12, 3 * 2 ^ 4, W₁)] :=
    ⟨hres, ⟨by rw [hfl, hlen], by rw [hlen], rfl, hgl, hquad⟩, ⟨rfl, W₁, rfl, hW₁⟩, hlen⟩
  have hnv := not_finViol_of_not_resC hbook hn
  have e := foldedW1_eq hlen [(15, 64, W₀), (12, 3 * 2 ^ 4, W₁)]
  have hw1 : wordOf [(15, 64, W₀), (12, 3 * 2 ^ 4, W₁)] 1 = W₁ := rfl
  rw [hw1] at e
  exact not_finalDoomL_of_not_finViol e hnv

/-- No fold luck of a list from no luck by rounds (four rounds). -/
theorem not_foldAllLuck_of_not_rounds {ι : Type} [Fintype ι]
    {L : Finset ((Fin 4 → Bool) → ι → E)} {O : (Fin 4 → Bool) → ι → E} {α : List E}
    (hl : α.length = 4) (h : ¬ ∃ V ∈ L, RoundsLuck 4 α O V) :
    ∀ V ∈ L, ¬ FoldAllLuck (fun i : Fin 4 ↦ α.getD i 0) O V :=
  fun V hV hF ↦ h ⟨V, hV, roundsLuck_of_foldAllLuck 4 α O V hl hF⟩

/-! ## The decoder facts -/

/-- **The middle phases' shape** (structural facts of the concrete phases): no commitment, no
proof of work, and the claims on `C_rec` they return are multiaffine. -/
structure MidShape (mid : List UInt8 → VerifierProgram OpenClaims) : Prop where
  noCommit : ∀ x, (mid x).NoCommit
  noGrind : ∀ x, (mid x).NoGrind
  recAffine : ∀ x l cl, (mid x).after l = some (.ret cl) → ∀ c ∈ cl.1, IsMultiaffine 19 c.1


/-! ## The knowledge certificate of the `S` branch (O5a, `mid` abstract) -/

section KCert

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}

theorem coe_εS : ((7 * (2 : ℝ≥0)⁻¹ ^ 131 : ℝ≥0) : ℝ≥0∞) = εS := by
  rw [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat, ENNReal.coe_ofNat]

theorem coe_εB : (((2 : ℝ≥0)⁻¹ ^ 132 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ ^ 132 := by
  rw [ENNReal.coe_pow, ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]

end KCert

end Lvm.ASM
