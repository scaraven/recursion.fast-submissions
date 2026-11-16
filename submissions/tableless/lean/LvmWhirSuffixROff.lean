/- `LvmWhirSuffixROff` (GOLF2 off-path move, group 13 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmWhirCode, LvmWhirLevelMidSpec, LvmWhirSpec, LvmWhirParams, LvmWhirParams24, LvmWhirParamsG, LvmWhirParamsJ, LvmWhirSuffixR,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmWhirCode
import LvmWhirLevelMidSpec
import LvmWhirSpec
import LvmWhirParams
import LvmWhirParams24
import LvmWhirParamsG
import LvmWhirParamsJ
import LvmWhirSuffixR
import LvmNodeSoundTOff
import LvmJBMutual
import LvmMlListLemmas

-- ===== from `LvmWhirCode` =====

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset
section
namespace LevelCode
variable (P : LevelCode)

theorem two_pow_κ_eq : 2 ^ P.κ = P.D + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm

theorem one_le_D : 1 ≤ P.D := by
  have : 2 ≤ 2 ^ P.κ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ P.κ := Nat.pow_le_pow_right (by norm_num) P.hκ
  simp only [D]; omega

theorem D_le : P.D ≤ P.n - 2 := by
  have : 2 * 2 ^ P.κ ≤ 2 ^ (P.κ + P.R) := by
    rw [pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ P.R := Nat.pow_le_pow_right (by norm_num) P.hR)
  have := P.one_le_D
  simp only [D, n] at *; omega

theorem D_lt_n : P.D < P.n := by
  have := P.D_le; have := P.one_le_D; omega

end LevelCode
end
end LeanVM.Protocol.Whir.Sound
end

-- ===== from `LvmWhirLevelMidSpec` =====

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier VerifierProgram Finset
section

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

end
end LeanVM.Protocol.Whir.Sound
end
end

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset
section
section Program
variable (μ ℓ₀ per c₀ n₀ g : ℕ) (dir : Bool) (w : List E → E) (i : ℕ) (level next : Whir.Level)
  (rest : List Whir.Level)

/-- The query group as one fragment. -/
theorem query_bind (c d t : ℕ) (K : List ℕ → E → List (List K) → VerifierProgram Unit) :
    ((samplePositions per d t).bind fun qs ↦ sampleChallenge.bind fun lam ↦
      (queryOpenings c qs).bind fun words ↦ K qs lam words) =
      (queryFrag per d t c).bind fun g ↦ K g.1 g.2.1 g.2.2 := by
  simp only [queryFrag, bind_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

end Program
end
end LeanVM.Protocol.Whir.Sound
end
end

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset
section
section Doom
variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (ℓ ℓ' pre : ℕ)

/-- After the query group: every member of the next list violates the glued claim. -/
def GlueC (r : WhirStateT × List E) (g : List ℕ × E × List (List K))
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidC μ ℓ₀ w i P P' ℓ ℓ' pre r cs ∧
    Viol P' (rowsOf ℓ' (laneO (i + 1) cs P'.n))
      (runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 []))
      (glueLv μ i r g.1 g.2.1 g.2.2 []).target

end Doom
end
end LeanVM.Protocol.Whir.Sound
end
end

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset
section
section Lemmas
variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {ℓ ℓ' pre : ℕ}

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

end Lemmas
end
end LeanVM.Protocol.Whir.Sound
end
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset
section
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
end

-- ===== from `LvmWhirSpec` =====

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
section
section Eps
variable (codes : ℕ → LevelCode) (g : ℕ)

/-- **The `εmax` of the WHIR opening.** -/
noncomputable def whirEpsUd (levels : List Whir.Level) : ENNReal := levelEpsUd codes g 0 levels

end Eps
end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
section
variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {codes : ℕ → LevelCode} {εmax : ENNReal}

/-- **The levels' specification.** -/
noncomputable def levelsSpec (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (hc : c₀ < n₀)
    (hper : 1 ≤ per) (hg : g ≤ 192) :
    (levels : List Whir.Level) → (i pre : ℕ) → LadderArithUd μ per codes i pre levels →
      levelEpsUd codes g i levels ≤ εmax → (s : WhirStateT) →
      Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w i levels s)
        (fun h ↦ LevelPreL μ codes ℓ₀ w i pre levels s (viewC c₀ n₀ (commits h)))
        (fun _ _ ↦ False) εmax εmax 0
  | [], i, pre, _, _, s => (Spec.fail (Pre := fun h ↦ LevelPreL μ codes ℓ₀ w i pre [] s
        (viewC c₀ n₀ (commits h))) (Post := fun _ _ ↦ False)).mono (fun _ h ↦ h)
        (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  | [level], i, pre, hA, hε, s =>
    finSpec ⟨hw, hℓ₀, hA.1, hA.2.1, hc, hper, hA.2.2.2⟩ hg ((le_max_left _ _).trans hε) hA.2.2.1
      ((le_max_left _ _).trans ((le_max_right _ _).trans hε))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hε)) s
  | level :: next :: rest, i, pre, hA, hε, s =>
    midSpec ⟨hw, hℓ₀, hA.1, by
        have := hA.2.2.2.2.2
        cases rest <;> exact this.1, hA.2.1, by
        have := hA.2.2.2.2.2
        cases rest <;> exact this.2.1, hc, hper, hA.2.2.2.1, hA.2.2.2.2.1⟩ hg
      ((le_max_left _ _).trans ((le_max_left _ _).trans hε)) hA.2.2.1
      ((le_max_right _ _).trans ((le_max_left _ _).trans hε))
      (fun s' ↦ levelsSpec hw hℓ₀ hc hper hg (next :: rest) (i + 1) (pre + level.fold)
        hA.2.2.2.2.2 ((le_max_right _ _).trans hε) s') s

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
section
variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {codes : ℕ → LevelCode} {εmax : ENNReal}

/-- **The specification of the unique-decoding WHIR opening.** From `WhirPreUd` (the history has the
`n₀` commitments the opening starts with, its root `c₀` is shaped as level `0`, and every
candidate of the root's word violates `(w, t)`), the opening's groups escape with probability at
most `εmax ≥ whirEpsUd codes cfg.levels` each, and it never returns in doom. -/
noncomputable def whirUdSpec {cfg : UdConfig} {t : E} {level : Whir.Level}
    {rest : List Whir.Level} (hc : cfg.levels = level :: rest) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ cfg.μ) (hκ₀ : (codes 0).κ = cfg.μ - laneBits) (hcn : cfg.c₀ < cfg.n₀)
    (hper : 1 ≤ cfg.per) (hg : cfg.grind ≤ 192) (hw : IsMultiaffine cfg.μ w)
    (hA : LadderArithUd cfg.μ cfg.per codes 0 0 (level :: rest))
    (hε : whirEpsUd codes cfg.grind (level :: rest) ≤ εmax) (T : ENNReal) :
    Spec (verifyWhirUd cfg t w) (fun h ↦ WhirPreUd cfg (codes 0) w t (commits h))
      (fun _ _ ↦ False) εmax 0 T :=
  anyT (Spec.congr (p' := verifyWhirUd cfg t w) (by rw [verifyWhirUd_eq hc, hℓ]; rfl)
    ((roundPolyInv (WhirPreUd cfg (codes 0) w t) t (T := εmax) le_rfl).bind' fun quad ↦
      (levelsSpec (ℓ₀ := laneBits) hw hμ hcn hper hg (level :: rest) 0 0 hA hε
          ⟨t, quad, [], []⟩).mono
        (fun h hp ↦ by
          show LevelPre cfg.μ laneBits w 0 (codes 0) level.fold 0 _ _
          rw [hℓ]
          exact levelPre_zero (codes 0) hκ₀ rfl hμ w t quad _ (whirPre_of_ud hp.2) hp.1)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)) T

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
section
variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {codes : ℕ → LevelCode} {εmax : ENNReal}

open Classical in
/-- **The specification of the stacked opening** (unique decoding). From `StackedPreUd` (every
candidate of the root violates one of the `J` claims), the batching challenge escapes with
probability at most `eBatch J P₀ = (J − 1)·L₀/|E|` and the opening (`whirUdSpec`) follows. -/
noncomputable def stackedUdSpec {cfg : UdConfig} {level : Whir.Level} {rest : List Whir.Level}
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine cfg.μ c.1)
    (hc : cfg.levels = level :: rest) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ cfg.μ) (hκ₀ : (codes 0).κ = cfg.μ - laneBits) (hcn : cfg.c₀ < cfg.n₀)
    (hper : 1 ≤ cfg.per) (hg : cfg.grind ≤ 192)
    (hA : LadderArithUd cfg.μ cfg.per codes 0 0 (level :: rest))
    (hε : whirEpsUd codes cfg.grind (level :: rest) ≤ εmax) (T : ENNReal) :
    Spec (verifyStackedUd cfg claims)
      (fun h ↦ StackedPreUd cfg (codes 0) claims (commits h)) (fun _ _ ↦ False) εmax
      (eBatch claims.length (codes 0)) T :=
  by
  have S0 : Spec VerifierProgram.sampleChallenge (fun h ↦ StackedPreUd cfg (codes 0) claims
      (commits h))
      (fun ρ h ↦ WhirPreUd cfg (codes 0)
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
        (dot (powers ρ claims.length) (claims.map (·.2))) (commits h)) εmax
      (eBatch claims.length (codes 0) + 0) 0 :=
    Spec.sampleE (eBatch claims.length (codes 0)) fun h₀ hp ↦ by
      have hb := card_batch_bad_le (codes 0) hκ₀ rfl hμ claims _ hp.2.2.2
      rw [eBatch, ENNReal.div_eq_inv_mul]
      refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((Finset.card_le_card fun ρ hρ ↦ ?_).trans
        (hb.trans (le_of_eq (mul_comm _ _)))))
      rw [Finset.mem_filter] at hρ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hρ2 := hρ.2
      simp only [commits_sample] at hρ2
      by_contra hno
      exact hρ2 ⟨hp.1, hp.2.1, hp.2.2.1, fun q hq hh ↦ hno ⟨q, hq, hh⟩⟩
  have F0 := fun ρ : E ↦
    whirUdSpec (w := fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
      (t := dot (powers ρ claims.length) (claims.map (·.2))) hc hℓ hμ hκ₀ hcn hper hg
      (isMultiaffine_batched claims hcl ρ) hA hε 0
  have S1 := Spec.bind S0 F0
  exact anyT (Spec.congr (p' := verifyStackedUd cfg claims)
    (verifyStackedUd_eq cfg claims).symm
    (S1.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl)) T

end
end LeanVM.Protocol.Whir.Sound
end

-- ===== from `LvmWhirParams` =====

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **The positions alone** of a UD level: `((udThr − 1)/n)^t ≤ 2^-c` from `(udThr − 1)^t·2^c ≤ n^t`. -/
theorem positions_ud_le {κ R : ℕ} {h64 hκ hR} (t c : ℕ)
    (h : (udThr κ R - 1) ^ t * 2 ^ c ≤ (2 ^ (κ + R)) ^ t) :
    ((((LevelCode.ud κ R h64 hκ hR).thr - 1 : ℕ) : ENNReal) / (LevelCode.ud κ R h64 hκ hR).n) ^ t ≤
      (2 : ENNReal)⁻¹ ^ c := by
  simp only [LevelCode.ud_thr, LevelCode.n, LevelCode.ud_κ, LevelCode.ud_R]
  rw [natCast_div_pow]
  exact natCast_div_le_inv_pow (by positivity) h

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **The batching challenge** of a UD root: `eBatch J = (J − 1)/|E|`, at most `2^-c` when
`(J − 1)·2^c ≤ 2^192`. -/
theorem eBatch_ud_le {κ R : ℕ} {h64 hκ hR} (J c : ℕ) (h : (J - 1) * 2 ^ c ≤ 2 ^ 192) :
    eBatch J (LevelCode.ud κ R h64 hκ hR) ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eBatch, LevelCode.ud_listMax, mul_one, card_E_ennreal,
    ← two_pow_cast 192]
  exact natCast_div_le_inv_pow (by positivity) h

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- `C_rec` at P8: `μ = 17`, one level `(6,2,30)`, final `2^11` scalars, root `1` of `2`. -/
def cfgRec8 : UdConfig := ⟨17, [⟨6, 2, 30⟩], 8, 1, 2, false, 0⟩

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **Fold, per challenge** (A13): `C_main` levels `≤ 2^-147, 2^-156, 2^-163, 2^-170`, `C_rec`
`≤ 2^-160`. -/
theorem eFold_P20 :
    eFold (codesMain20 0) 6 ≤ (2 : ENNReal)⁻¹ ^ 147 ∧ eFold (codesMain20 1) 4 ≤ (2 : ENNReal)⁻¹ ^ 156 ∧
      eFold (codesMain20 2) 4 ≤ (2 : ENNReal)⁻¹ ^ 163 ∧
      eFold (codesMain20 3) 4 ≤ (2 : ENNReal)⁻¹ ^ 170 ∧
      eFold (codesRec20 0) 6 ≤ (2 : ENNReal)⁻¹ ^ 160 := by
  refine ⟨eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_,
    eFold_ud_le _ _ ?_⟩ <;> simp only [udMca, mcaUd, udThr] <;> norm_num

/-- **Positions** (A13): `((A_i − 1)/n_i)^{t_i} ≤ 2^-129` at every level of both openings. -/
theorem positions_P20 :
    ((((codesMain20 0).thr - 1 : ℕ) : ENNReal) / (codesMain20 0).n) ^ 311 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesMain20 1).thr - 1 : ℕ) : ENNReal) / (codesMain20 1).n) ^ 191 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesMain20 2).thr - 1 : ℕ) : ENNReal) / (codesMain20 2).n) ^ 156 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesMain20 3).thr - 1 : ℕ) : ENNReal) / (codesMain20 3).n) ^ 142 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesRec20 0).thr - 1 : ℕ) : ENNReal) / (codesRec20 0).n) ^ 191 ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  refine ⟨positions_ud_le _ _ ?_, positions_ud_le _ _ ?_, positions_ud_le _ _ ?_,
    positions_ud_le _ _ ?_, positions_ud_le _ _ ?_⟩ <;> simp only [udThr] <;> norm_num

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`εmax` of `C_main` at P20**: every group escape is at most `2^-129`. -/
theorem whirEps_main20 : whirEpsUd codesMain20 cfgMain20.grind cfgMain20.levels ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  obtain ⟨f0, f1, f2, f3, -⟩ := eFold_P20
  obtain ⟨q0, q1, q2, q3⟩ := eQuery_main20
  simp only [whirEpsUd, cfgMain20, levelEpsUd, max_le_iff, pow_zero, one_mul]
  exact ⟨⟨f0.trans (inv_two_pow_anti (by norm_num)), q0⟩,
    ⟨f1.trans (inv_two_pow_anti (by norm_num)), q1⟩,
    ⟨f2.trans (inv_two_pow_anti (by norm_num)), q2⟩,
    f3.trans (inv_two_pow_anti (by norm_num)), q3, eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

/-- **`εmax` of `C_rec` at P20.** -/
theorem whirEps_rec20 : whirEpsUd codesRec20 cfgRec20.grind cfgRec20.levels ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  obtain ⟨-, -, -, -, f⟩ := eFold_P20
  simp only [whirEpsUd, cfgRec20, levelEpsUd, max_le_iff, pow_zero, one_mul]
  exact ⟨f.trans (inv_two_pow_anti (by norm_num)), eQuery_rec20,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`εmax` of `C_main` at P8**: every group escape is at most `2^-20`. -/
theorem whirEps_main8 : whirEpsUd codesMain8 cfgMain8.grind cfgMain8.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  simp only [whirEpsUd, cfgMain8, levelEpsUd, max_le_iff, pow_zero, one_mul]
  refine ⟨⟨eFold_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_⟩, ⟨eFold_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_⟩,
    ⟨eFold_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_⟩, eFold_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;> simp only [udMca, mcaUd, udThr] <;>
    norm_num

/-- **`εmax` of `C_rec` at P8.** -/
theorem whirEps_rec8 : whirEpsUd codesRec8 cfgRec8.grind cfgRec8.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  simp only [whirEpsUd, cfgRec8, levelEpsUd, max_le_iff, pow_zero, one_mul]
  refine ⟨eFold_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;> simp only [udMca, mcaUd, udThr] <;>
    norm_num

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **The levels' arithmetic of `C_rec` at P8.** -/
theorem ladderArith_rec8 :
    LadderArithUd cfgRec8.μ cfgRec8.per codesRec8 0 0 cfgRec8.levels :=
  ⟨rfl, rfl, eQuery_P8.2.2.2.2.trans_lt (inv_two_pow_lt_one (by norm_num)),
    by norm_num [cfgRec8, codesRec8]⟩

/-- **`C_main`'s stacked opening at P20**: groups escape at most `2^-129`, the batching challenge
`(J − 1)/|E|`. -/
noncomputable def stackedMain20Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain20.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain20 claims)
      (fun h ↦ StackedPreUd cfgMain20 (codesMain20 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 129) (eBatch claims.length (codesMain20 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain20]) rfl (by norm_num [cfgMain20])
    (by norm_num [cfgMain20]) (by norm_num [cfgMain20]) ladderArith_main20 whirEps_main20 T

/-- **`C_rec`'s stacked opening at P20.** -/
noncomputable def stackedRec20Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgRec20 claims)
      (fun h ↦ StackedPreUd cfgRec20 (codesRec20 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 129) (eBatch claims.length (codesRec20 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgRec20]) rfl (by norm_num [cfgRec20])
    (by norm_num [cfgRec20]) (by norm_num [cfgRec20]) ladderArith_rec20 whirEps_rec20 T

/-- **`C_main`'s stacked opening at P8.** -/
noncomputable def stackedMain8Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain8.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain8 claims)
      (fun h ↦ StackedPreUd cfgMain8 (codesMain8 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesMain8 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain8]) rfl (by norm_num [cfgMain8])
    (by norm_num [cfgMain8]) (by norm_num [cfgMain8]) ladderArith_main8 whirEps_main8 T

/-- **`C_rec`'s stacked opening at P8.** -/
noncomputable def stackedRec8Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec8.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgRec8 claims)
      (fun h ↦ StackedPreUd cfgRec8 (codesRec8 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesRec8 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgRec8]) rfl (by norm_num [cfgRec8])
    (by norm_num [cfgRec8]) (by norm_num [cfgRec8]) ladderArith_rec8 whirEps_rec8 T

/-- The batching challenge at the roots: at most `2^-129` for `J ≤ 2^63` claims. -/
theorem eBatch_P20 (J : ℕ) (hJ : J ≤ 2 ^ 63) :
    eBatch J (codesMain20 0) ≤ (2 : ENNReal)⁻¹ ^ 129 ∧ eBatch J (codesRec20 0) ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  have h : (J - 1) * 2 ^ 129 ≤ 2 ^ 192 :=
    (Nat.mul_le_mul_right _ ((Nat.sub_le J 1).trans hJ)).trans (by norm_num)
  exact ⟨eBatch_ud_le _ _ h, eBatch_ud_le _ _ h⟩

end
end LeanVM.Protocol.Whir.Sound
end

-- ===== from `LvmWhirParams24` =====

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **Fold, per challenge** (A13): `C_main` levels `≤ 2^-151, 2^-160, 2^-167`. -/
theorem eFold_main24 :
    eFold (codesMain24 0) 6 ≤ (2 : ENNReal)⁻¹ ^ 151 ∧ eFold (codesMain24 1) 4 ≤ (2 : ENNReal)⁻¹ ^ 160 ∧
      eFold (codesMain24 2) 4 ≤ (2 : ENNReal)⁻¹ ^ 167 := by
  refine ⟨eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_⟩ <;>
    simp only [udMca, mcaUd, udThr] <;> norm_num

/-- **Positions** (A13): `((A_i − 1)/n_i)^{t_i} ≤ 2^-129` at every level of `C_main`. -/
theorem positions_main24 :
    ((((codesMain24 0).thr - 1 : ℕ) : ENNReal) / (codesMain24 0).n) ^ 311 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesMain24 1).thr - 1 : ℕ) : ENNReal) / (codesMain24 1).n) ^ 191 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesMain24 2).thr - 1 : ℕ) : ENNReal) / (codesMain24 2).n) ^ 156 ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  refine ⟨positions_ud_le _ _ ?_, positions_ud_le _ _ ?_, positions_ud_le _ _ ?_⟩ <;>
    simp only [udThr] <;> norm_num

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`εmax` of `C_main` at S2 P20**: every group escape is at most `2^-129`. -/
theorem whirEps_main24 : whirEpsUd codesMain24 cfgMain24.grind cfgMain24.levels ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  obtain ⟨f0, f1, f2⟩ := eFold_main24
  obtain ⟨q0, q1, q2⟩ := eQuery_main24
  simp only [whirEpsUd, cfgMain24, levelEpsUd, max_le_iff, pow_zero, one_mul]
  exact ⟨⟨f0.trans (inv_two_pow_anti (by norm_num)), q0⟩,
    ⟨f1.trans (inv_two_pow_anti (by norm_num)), q1⟩,
    f2.trans (inv_two_pow_anti (by norm_num)), q2, eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`εmax` of `C_main` at S2 P8**: every group escape is at most `2^-20`. -/
theorem whirEps_main23 : whirEpsUd codesMain23 cfgMain23.grind cfgMain23.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  simp only [whirEpsUd, cfgMain23, levelEpsUd, max_le_iff, pow_zero, one_mul]
  refine ⟨⟨eFold_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_⟩, ⟨eFold_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_⟩,
    eFold_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;> simp only [udMca, mcaUd, udThr] <;>
    norm_num

/-- **`εmax` of `C_rec` at S2 P8.** -/
theorem whirEps_rec18 : whirEpsUd codesRec18 cfgRec18.grind cfgRec18.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  simp only [whirEpsUd, cfgRec18, levelEpsUd, max_le_iff, pow_zero, one_mul]
  refine ⟨eFold_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;> simp only [udMca, mcaUd, udThr] <;>
    norm_num

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`C_main`'s stacked opening at S2 P20**: groups escape at most `2^-129`, the batching challenge
`(J − 1)/|E|`. -/
noncomputable def stackedMain24Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain24.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain24 claims)
      (fun h ↦ StackedPreUd cfgMain24 (codesMain24 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 129) (eBatch claims.length (codesMain24 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain24]) rfl (by norm_num [cfgMain24])
    (by norm_num [cfgMain24]) (by norm_num [cfgMain24]) ladderArith_main24 whirEps_main24 T

/-- **`C_main`'s stacked opening at S2 P8.** -/
noncomputable def stackedMain23Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain23.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain23 claims)
      (fun h ↦ StackedPreUd cfgMain23 (codesMain23 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesMain23 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain23]) rfl (by norm_num [cfgMain23])
    (by norm_num [cfgMain23]) (by norm_num [cfgMain23]) ladderArith_main23 whirEps_main23 T

/-- **`C_rec`'s stacked opening at S2 P8.** -/
noncomputable def stackedRec18Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec18.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgRec18 claims)
      (fun h ↦ StackedPreUd cfgRec18 (codesRec18 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesRec18 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgRec18]) rfl (by norm_num [cfgRec18])
    (by norm_num [cfgRec18]) (by norm_num [cfgRec18]) ladderArith_rec18 whirEps_rec18 T

/-- The batching challenge at `C_main`'s S2 root: at most `2^-129` for `J ≤ 2^63` claims. -/
theorem eBatch_main24 (J : ℕ) (hJ : J ≤ 2 ^ 63) :
    eBatch J (codesMain24 0) ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  have h : (J - 1) * 2 ^ 129 ≤ 2 ^ 192 :=
    (Nat.mul_le_mul_right _ ((Nat.sub_le J 1).trans hJ)).trans (by norm_num)
  exact eBatch_ud_le _ _ h

end
end LeanVM.Protocol.Whir.Sound
end

-- ===== from `LvmWhirParamsG` =====

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`εmax` of `C_main` at S2 P20 with grinding**: every group escape is at most `2^-129`. -/
theorem whirEps_main24G :
    whirEpsUd codesMain24 cfgMain24G.grind cfgMain24G.levels ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  obtain ⟨f0, f1, f2⟩ := eFold_main24
  obtain ⟨q0, q1, q2, -⟩ := eQuery_main24G
  simp only [whirEpsUd, cfgMain24G, levelEpsUd, max_le_iff]
  exact ⟨⟨f0.trans (inv_two_pow_anti (by norm_num)), disc_le 14 q0⟩,
    ⟨f1.trans (inv_two_pow_anti (by norm_num)), disc_le 14 q1⟩,
    f2.trans (inv_two_pow_anti (by norm_num)), disc_le 14 q2,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`εmax` of `C_rec` at P20 with grinding** (S4: two levels). -/
theorem whirEps_rec20G :
    whirEpsUd codesRec20 cfgRec20G.grind cfgRec20G.levels ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  obtain ⟨-, -, -, -, f⟩ := eFold_P20
  obtain ⟨q0, q1⟩ := eQuery_rec20G
  simp only [whirEpsUd, cfgRec20G, levelEpsUd, max_le_iff]
  exact ⟨⟨f.trans (inv_two_pow_anti (by norm_num)), disc_le 14 q0⟩,
    eFold_rec20_1.trans (inv_two_pow_anti (by norm_num)), disc_le 14 q1,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`εmax` of `C_main` at S2 P8 with grinding**: every group escape is at most `2^-20`. -/
theorem whirEps_main23G :
    whirEpsUd codesMain23 cfgMain23G.grind cfgMain23G.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  obtain ⟨q0, q1, q2, -⟩ := eQuery_P8G
  simp only [whirEpsUd, cfgMain23G, levelEpsUd, max_le_iff]
  refine ⟨⟨eFold_ud_le _ _ ?_, disc_le 4 q0⟩, ⟨eFold_ud_le _ _ ?_, disc_le 4 q1⟩,
    eFold_ud_le _ _ ?_, disc_le 4 q2, eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;>
    simp only [udMca, mcaUd, udThr] <;> norm_num

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`εmax` of `C_rec` at S2 P8 with grinding** (S4: two levels). -/
theorem whirEps_rec18G :
    whirEpsUd codesRec18 cfgRec18G.grind cfgRec18G.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  obtain ⟨q0, q1⟩ := eQuery_rec18G
  simp only [whirEpsUd, cfgRec18G, levelEpsUd, max_le_iff]
  refine ⟨⟨eFold_ud_le _ _ ?_, disc_le 4 q0⟩, eFold_ud_le _ _ ?_, disc_le 4 q1,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;> simp only [udMca, mcaUd, udThr] <;> norm_num

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`C_main`'s stacked opening at S2 P20 with grinding**: groups escape at most `2^-129`. -/
noncomputable def stackedMain24GSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain24G.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain24G claims)
      (fun h ↦ StackedPreUd cfgMain24G (codesMain24 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 129) (eBatch claims.length (codesMain24 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain24G]) rfl (by norm_num [cfgMain24G])
    (by norm_num [cfgMain24G]) (by norm_num [cfgMain24G]) ladderArith_main24G whirEps_main24G T

/-- **`C_rec`'s stacked opening at P20 with grinding.** -/
noncomputable def stackedRec20GSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20G.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgRec20G claims)
      (fun h ↦ StackedPreUd cfgRec20G (codesRec20 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 129) (eBatch claims.length (codesRec20 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgRec20G]) rfl (by norm_num [cfgRec20G])
    (by norm_num [cfgRec20G]) (by norm_num [cfgRec20G]) ladderArith_rec20G whirEps_rec20G T

/-- **`C_main`'s stacked opening at S2 P8 with grinding.** -/
noncomputable def stackedMain23GSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain23G.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain23G claims)
      (fun h ↦ StackedPreUd cfgMain23G (codesMain23 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesMain23 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain23G]) rfl (by norm_num [cfgMain23G])
    (by norm_num [cfgMain23G]) (by norm_num [cfgMain23G]) ladderArith_main23G whirEps_main23G T

/-- **`C_rec`'s stacked opening at S2 P8 with grinding.** -/
noncomputable def stackedRec18GSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec18G.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgRec18G claims)
      (fun h ↦ StackedPreUd cfgRec18G (codesRec18 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesRec18 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgRec18G]) rfl (by norm_num [cfgRec18G])
    (by norm_num [cfgRec18G]) (by norm_num [cfgRec18G]) ladderArith_rec18G whirEps_rec18G T

end
end LeanVM.Protocol.Whir.Sound
end

-- ===== from `LvmWhirParamsJ` =====

section
section
namespace JB.CodingTheory
section Support
variable {F : Type*} [Zero F] [DecidableEq F]

theorem supportOn_subset {n : ℕ} (U : Finset (Fin n)) (w : Word F n) :
    supportOn U w ⊆ U := by
  intro i hi
  exact (mem_supportOn U w i).mp hi |>.1

end Support
end JB.CodingTheory
end
end

section
section
namespace JB.CodingTheory
section Support
variable {F : Type*} [Zero F] [DecidableEq F]

/-- The union of the supports of two words. -/
def jointSupport {n : ℕ} (x y : Word F n) : Finset (Fin n) :=
  supportOn Finset.univ x ∪ supportOn Finset.univ y

/-- A word's total weight is bounded by its support in a selected region plus
all coordinates outside that region. -/
theorem weight_le_supportOn_add_complement {n : ℕ}
    (U : Finset (Fin n)) (x : Word F n) :
    weight x ≤ (supportOn U x).card + (Finset.univ \ U).card := by
  have hsubset : supportOn Finset.univ x ⊆
      supportOn U x ∪ (Finset.univ \ U) := by
    intro i hi
    by_cases hU : i ∈ U
    · exact Finset.mem_union_left _
        ((mem_supportOn U x i).mpr
          ⟨hU, (mem_supportOn Finset.univ x i).mp hi |>.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hU⟩)
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)

end Support
end JB.CodingTheory
end
end

section
section
namespace JB.CodingTheory
section SemiringSupport
variable {F : Type*} [Semiring F] [DecidableEq F]

theorem supportOn_add_subset {n : ℕ} (U : Finset (Fin n)) (x y : Word F n) :
    supportOn U (x + y) ⊆ supportOn U x ∪ supportOn U y := by
  intro i hi
  have hiparts := (mem_supportOn U (x + y) i).mp hi
  by_cases hx : x i = 0
  · apply Finset.mem_union_right
    exact (mem_supportOn U y i).mpr
      ⟨hiparts.1, fun hy ↦ hiparts.2 (by simp [hx, hy])⟩
  · exact Finset.mem_union_left _
      ((mem_supportOn U x i).mpr ⟨hiparts.1, hx⟩)

theorem supportOn_add_card_le {n : ℕ} (U : Finset (Fin n)) (x y : Word F n) :
    (supportOn U (x + y)).card ≤
      (supportOn U x).card + (supportOn U y).card :=
  (Finset.card_le_card (supportOn_add_subset U x y)).trans
    (Finset.card_union_le _ _)

theorem weight_add_le {n : ℕ} (x y : Word F n) :
    weight (x + y) ≤ weight x + weight y :=
  supportOn_add_card_le Finset.univ x y

theorem supportOn_smul_subset {n : ℕ} (U : Finset (Fin n))
    (a : F) (x : Word F n) : supportOn U (a • x) ⊆ supportOn U x := by
  intro i hi
  have hiparts := (mem_supportOn U (a • x) i).mp hi
  apply (mem_supportOn U x i).mpr
  refine ⟨hiparts.1, ?_⟩
  intro hx
  exact hiparts.2 (by simp [hx])

theorem supportOn_smul_card_le {n : ℕ} (U : Finset (Fin n))
    (a : F) (x : Word F n) :
    (supportOn U (a • x)).card ≤ (supportOn U x).card :=
  Finset.card_le_card (supportOn_smul_subset U a x)

theorem weight_smul_le {n : ℕ} (a : F) (x : Word F n) :
    weight (a • x) ≤ weight x :=
  supportOn_smul_card_le Finset.univ a x

/-- A nonzero codeword has at least the minimum distance many nonzero
coordinates. -/
theorem eq_zero_of_weight_lt_distance {n d : ℕ} {C : LinearCode F n}
    (hmin : HasMinimumDistanceAtLeast C d)
    {c : Word F n} (hc : c ∈ C) (hweight : weight c < d) : c = 0 := by
  exact not_ne_iff.mp fun hne ↦
    (Nat.not_le_of_lt hweight) (hmin.weight_ge_distance c hc hne)

end SemiringSupport
end JB.CodingTheory
end
end

section
section
namespace JB.CodingTheory
variable {F : Type*} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- A word lies within Hamming radius `e` of some codeword. -/
def WithinRadius (C : LinearCode F n) (e : ℕ) (received : Word F n) : Prop :=
  ∃ codeword, codeword ∈ C ∧ weight (received - codeword) ≤ e

/-- Linear combination of the rows of a finite word matrix. -/
def wordCombination {Row : Type*} [Fintype Row]
    (rows : Row → Word F n) (weights : Row → F) : Word F n :=
  ∑ row, weights row • rows row

/-- Standard basis vector selecting one matrix row. -/
def rowBasis {Row : Type*} [DecidableEq Row] (pivot : Row) : Row → F :=
  fun row ↦ if row = pivot then 1 else 0

omit [DecidableEq F] in
theorem wordCombination_apply {Row : Type*} [Fintype Row]
    (rows : Row → Word F n) (weights : Row → F) (j : Fin n) :
    wordCombination rows weights j = ∑ row, weights row * rows row j := by
  classical
  unfold wordCombination
  change (Pi.evalAddMonoidHom (fun _ : Fin n ↦ F) j)
      (∑ row, weights row • rows row) = _
  rw [map_sum]
  rfl

omit [DecidableEq F] in
theorem wordCombination_add_smul {Row : Type*} [Fintype Row]
    (rows : Row → Word F n) (first direction : Row → F) (scalar : F) :
    wordCombination rows (first + scalar • direction) =
      wordCombination rows first + scalar • wordCombination rows direction := by
  classical
  funext j
  simp only [wordCombination_apply, Pi.add_apply, Pi.smul_apply]
  simp only [add_mul, smul_eq_mul, mul_assoc]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

omit [DecidableEq F] in
theorem wordCombination_rowBasis {Row : Type*} [Fintype Row]
    [DecidableEq Row] (rows : Row → Word F n) (pivot : Row) :
    wordCombination rows (rowBasis pivot) = rows pivot := by
  funext coordinate
  rw [wordCombination_apply]
  simp [rowBasis]

private def transverseCoordinates {Row : Type*}
    (direction : Row → F) (pivot : Row) (weights : Row → F) :
    { row : Row // row ≠ pivot } → F :=
  fun row ↦ weights row.1 -
    weights pivot * (direction row.1 / direction pivot)

omit [DecidableEq F] in
/-- A line-wise subsingleton predicate occupies at most one point in every
fiber parallel to a nonzero direction. -/
theorem card_filter_univ_le_pow_of_line_subsingleton
    {Row : Type*} [Fintype Row] [DecidableEq Row] [Fintype F]
    (property : (Row → F) → Prop) [DecidablePred property]
    (direction : Row → F) (hnonzero : direction ≠ 0)
    (hline : ∀ base,
      { scalar : F | property (base + scalar • direction) }.Subsingleton) :
    (Finset.univ.filter property).card ≤
      Fintype.card F ^ (Fintype.card Row - 1) := by
  classical
  obtain ⟨pivot, hpivot⟩ : ∃ row, direction row ≠ 0 := by
    simpa [Function.ne_iff] using hnonzero
  let Other := { row : Row // row ≠ pivot }
  let Good := ↥(Finset.univ.filter property)
  let project : Good → Other → F := fun weights ↦
    transverseCoordinates direction pivot weights.1
  have hprojectInjective : Function.Injective project := by
    intro first second hproject
    let scalar := (first.1 pivot - second.1 pivot) / direction pivot
    have hcoefficients : first.1 = second.1 + scalar • direction := by
      funext row
      by_cases hrow : row = pivot
      · subst row
        dsimp [scalar]
        field_simp [hpivot]
        ring
      · have hcoordinate := congrFun hproject (⟨row, hrow⟩ : Other)
        dsimp [project, transverseCoordinates] at hcoordinate
        dsimp [scalar]
        field_simp [hpivot] at hcoordinate ⊢
        linear_combination hcoordinate
    have hfirstProperty : property first.1 :=
      (Finset.mem_filter.mp first.2).2
    have hsecondProperty : property second.1 :=
      (Finset.mem_filter.mp second.2).2
    have hscalarZero : scalar = 0 :=
      hline second.1 (by simpa [hcoefficients] using hfirstProperty)
        (by simpa using hsecondProperty)
    apply Subtype.ext
    rw [hcoefficients, hscalarZero]
    simp
  calc
    (Finset.univ.filter property).card = Fintype.card Good :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Other → F) :=
      Fintype.card_le_of_injective project hprojectInjective
    _ = Fintype.card F ^ (Fintype.card Row - 1) := by
      simp [Other, Fintype.card_subtype_compl]

/-- Challenges whose affine matrix combination is close to the code. -/
noncomputable def closeCombinationChallenges {Row : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype F]
    (C : LinearCode F n) (e : ℕ)
    (rows : Row → Word F n) (offset : Word F n) : Finset (Row → F) := by
  classical
  exact Finset.univ.filter fun weights ↦
    WithinRadius C e (offset + wordCombination rows weights)

end JB.CodingTheory
end
end

section
section
namespace JB.CodingTheory
variable {F : Type*} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- Interleaved proximity: all rows have codeword representatives whose union
of error columns has size at most `e`. -/
def InterleavedWithinRadius {Row : Type*} [Fintype Row]
    (C : LinearCode F n) (e : ℕ) (rows : Row → Word F n) : Prop :=
  ∃ decodedRows : Row → Word F n,
    (∀ row, decodedRows row ∈ C) ∧
    (matrixErrorCoordinates rows decodedRows).card ≤ e

end JB.CodingTheory
end
end

section
section
namespace JB.CodingTheory
open scoped BigOperators

/-- Two large agreement sets cannot coexist past the unique-list threshold. -/
theorem uniformFamilyBound_one_of_two_mul_gt {n w lam : ℕ}
    (h : n + lam < 2 * w) : UniformFamilyBound n w lam 1 := by
  classical
  intro family hcard hinter
  rw [Finset.card_le_one_iff]
  intro A B hA hB
  by_contra hne
  have hmeet := hinter A hA B hB hne
  have hunion : (A ∪ B).card ≤ n := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have heq := Finset.card_union_add_card_inter A B
  rw [hcard A hA, hcard B hB] at heq
  omega

/-- Bonferroni's three-set inequality gives an integer list bound of two.
It can improve the real-valued second-moment Johnson bound after flooring. -/
theorem uniformFamilyBound_two_of_three_mul_gt {n w lam : ℕ}
    (h : n + 3 * lam < 3 * w) : UniformFamilyBound n w lam 2 := by
  classical
  intro family hcard hinter
  by_contra hlarge
  obtain ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < family.card)
  have hABmeet := hinter A hA B hB hAB
  have hACmeet := hinter A hA C hC hAC
  have hBCmeet := hinter B hB C hC hBC
  have hfirst := Finset.card_union_add_card_inter A B
  have hsecond := Finset.card_union_add_card_inter (A ∪ B) C
  have hsplit : ((A ∪ B) ∩ C).card ≤ (A ∩ C).card + (B ∩ C).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  have hunion : ((A ∪ B) ∪ C).card ≤ n := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  rw [hcard A hA, hcard B hB] at hfirst
  rw [hcard C hC] at hsecond
  omega

/-- A bound for `w`-uniform families also bounds families of larger sets:
shrinking every member to `w` points keeps distinct members distinct, because
two members sharing a `w`-subset would meet in `w > lam` points. -/
theorem UniformFamilyBound.of_le_size {n w w' lam L : ℕ}
    (h : UniformFamilyBound n w lam L) (hww' : w ≤ w') (hlam : lam < w) :
    UniformFamilyBound n w' lam L := by
  classical
  intro family hcard hinter
  have hsub : ∀ A ∈ family, ∃ B ⊆ A, B.card = w := fun A hA ↦
    Finset.exists_subset_card_eq (by rw [hcard A hA]; exact hww')
  choose! shrink hshrinkSub hshrinkCard using hsub
  have hinj : Set.InjOn shrink family := by
    intro A hA B hB hAB
    by_contra hne
    have hle : (shrink A).card ≤ (A ∩ B).card := by
      apply Finset.card_le_card
      intro x hx
      have hxB : x ∈ shrink B := by
        have hAB' : shrink A = shrink B := hAB
        rw [← hAB']
        exact hx
      exact Finset.mem_inter.mpr ⟨hshrinkSub A hA hx, hshrinkSub B hB hxB⟩
    have hmeet := hinter A hA B hB hne
    rw [hshrinkCard A hA] at hle
    omega
  have himage := h (family.image shrink)
    (fun B hB ↦ by
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      exact hshrinkCard A hA)
    (fun B hB B' hB' hne ↦ by
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hB'
      have hAA' : A ≠ A' := fun heq ↦ hne (heq ▸ rfl)
      calc
        (shrink A ∩ shrink A').card ≤ (A ∩ A').card :=
          Finset.card_le_card (Finset.inter_subset_inter (hshrinkSub A hA) (hshrinkSub A' hA'))
        _ ≤ lam := hinter A hA A' hA' hAA')
  rwa [Finset.card_image_of_injOn hinj] at himage

end JB.CodingTheory
end
end

section
section
namespace JB.CodingTheory.InterleavedJohnson
open JB.CodingTheory
open scoped BigOperators

/-- On the radius range `E ≤ n`, decreasing the error radius can only
increase the Johnson denominator. -/
theorem denominator_anti_on {n d E E₀ : ℕ}
    (hE : E ≤ E₀) (hE₀ : E₀ ≤ n) :
    denominator n d E₀ ≤ denominator n d E := by
  unfold denominator
  have hE' : (E : ℤ) ≤ E₀ := by exact_mod_cast hE
  have hE₀' : (E₀ : ℤ) ≤ n := by exact_mod_cast hE₀
  nlinarith

theorem denominator_pos_of_le {n d E E₀ : ℕ}
    (hE : E ≤ E₀) (hE₀ : E₀ ≤ n)
    (hpos : 0 < denominator n d E₀) :
    0 < denominator n d E :=
  hpos.trans_le (denominator_anti_on hE hE₀)

end JB.CodingTheory.InterleavedJohnson
end
end

section
section
namespace JBAgreement
open Polynomial Finset

/-- One dimension-`k` polynomial pair explains the two words up to `e` pair
errors and satisfies the full mutual/list conclusion at the same radius. -/
def StrongAgreementConclusion
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dom : ι → F) (u₀ u₁ : ι → F) (k e : ℕ) : Prop :=
  ∃ v₀ v₁ : F[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
    (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e ∧
    (∀ S₂ : Finset F, e + 1 < S₂.card →
      (∀ z ∈ S₂, (disagree (fun x => u₀ x + z * u₁ x)
          (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) →
      (S₂.filter fun z =>
        lineAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) z ≠
          corrAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e)

end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset

/-- A certificate for the numerical hypotheses of the checked four-parameter
interpolation kernel.  This type belongs to the implementation layer: callers
use `innerStrongTerm`, which minimizes over all such certificates. -/
structure StrongCertificate (k n e : ℕ) where
  multiplicity : ℕ
  weightedDegree : ℕ
  yDegree : ℕ
  zDegree : ℕ
  yDegree_le : k * yDegree ≤ weightedDegree
  coefficient_surplus :
    n * (multiplicity * (multiplicity + 1)) * (zDegree + yDegree + 1) <
      ((yDegree + 1) * (2 * (weightedDegree + 1)) -
        k * (yDegree * (yDegree + 1))) * (zDegree + 1)
  root_surplus : weightedDegree < multiplicity * (n - e)
  agreement_slack : 1 ≤ n - e - k

/-- The exact number of exceptional parameters charged by a numerical
certificate.  A parameter set of cardinality strictly larger than this term is
enough for the strong (correlated-and-mutual) conclusion. -/
def StrongCertificate.term {k n e : ℕ} (c : StrongCertificate k n e) : ℕ :=
  c.yDegree * (e + 2) +
    (n - k) * (4 * k * (c.yDegree * c.zDegree) + c.yDegree) / (n - e - k) +
    c.zDegree + 3 * (c.yDegree * c.zDegree)

/-- The best exceptional-parameter term furnished by the checked
interpolation argument.  It is a natural-number infimum, hence is attained
whenever a numerical certificate exists. -/
noncomputable def innerStrongTerm (k n e : ℕ) : ℕ :=
  sInf {q : ℕ | ∃ c : StrongCertificate k n e, c.term = q}

/-- Least integral cardinality threshold corresponding to `innerStrongTerm`. -/
noncomputable def innerStrongThreshold (k n e : ℕ) : ℕ :=
  innerStrongTerm k n e + 1

theorem innerStrongTerm_le {k n e : ℕ} (c : StrongCertificate k n e) :
    innerStrongTerm k n e ≤ c.term := by
  exact Nat.sInf_le ⟨c, rfl⟩

theorem exists_certificate_at_innerStrongTerm {k n e : ℕ}
    (h : Nonempty (StrongCertificate k n e)) :
    ∃ c : StrongCertificate k n e, c.term = innerStrongTerm k n e := by
  have hset :
      ({q : ℕ | ∃ c : StrongCertificate k n e, c.term = q} : Set ℕ).Nonempty := by
    obtain ⟨c⟩ := h
    exact ⟨c.term, c, rfl⟩
  simpa [innerStrongTerm] using Nat.sInf_mem hset

end JBAgreement
end
end

section
section
namespace JBAgreement
open Polynomial Finset
section Exact
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- More than `innerStrongTerm` proximate line
parameters force a single dimension-`k` pair with at most `e` pair disagreements.
The same pair satisfies the mutual/list conclusion.  The interpolation integers
are hidden in the attained minimum. -/
theorem correlatedAgreement_innerStrong
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (S : Finset F)
    (hclose : ∀ z ∈ S, ∃ p : F[X], p.natDegree < k ∧
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e)
    (hk : 1 ≤ k)
    (hcert : Nonempty (StrongCertificate k (Fintype.card ι) e))
    (hS : innerStrongTerm k (Fintype.card ι) e < S.card) :
    StrongAgreementConclusion dom u₀ u₁ k e := by
  obtain ⟨c, hc⟩ := exists_certificate_at_innerStrongTerm hcert
  have hyDegree : (k - 1) * c.yDegree ≤ c.weightedDegree :=
    (Nat.mul_le_mul_right c.yDegree (Nat.sub_le k 1)).trans c.yDegree_le
  have hcoefficient :
      Fintype.card ι * (c.multiplicity * (c.multiplicity + 1)) *
          (c.zDegree + c.yDegree + 1) <
        ((c.yDegree + 1) * (2 * (c.weightedDegree + 1)) -
            (k - 1) * (c.yDegree * (c.yDegree + 1))) * (c.zDegree + 1) := by
    apply c.coefficient_surplus.trans_le
    apply Nat.mul_le_mul_right
    apply Nat.sub_le_sub_left
    exact Nat.mul_le_mul_right _ (Nat.sub_le k 1)
  apply correlatedAgreement_unconditional_sharp_noFieldSize dom hdom u₀ u₁ k e hk
    S hclose c.multiplicity c.weightedDegree c.yDegree c.zDegree
    hyDegree hcoefficient c.root_surplus c.agreement_slack
  rw [← hc] at hS
  exact hS

/-- Weak-cardinality form of `correlatedAgreement_innerStrong`. -/
theorem correlatedAgreement_innerStrong_threshold
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (S : Finset F)
    (hclose : ∀ z ∈ S, ∃ p : F[X], p.natDegree < k ∧
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e)
    (hk : 1 ≤ k)
    (hcert : Nonempty (StrongCertificate k (Fintype.card ι) e))
    (hS : innerStrongThreshold k (Fintype.card ι) e ≤ S.card) :
    StrongAgreementConclusion dom u₀ u₁ k e := by
  apply correlatedAgreement_innerStrong dom hdom u₀ u₁ k e S hclose hk hcert
  rw [innerStrongThreshold] at hS
  omega

end Exact
end JBAgreement
end
end

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Whir JBAgreement JB.CodingTheory.InterleavedJohnson

/-- The codes of `C_main`'s Johnson levels `(6,1) (4,2) (4,3)` (ν = 24). -/
noncomputable def codesMain24J : ℕ → LevelCode
  | 0 => codeJ18R1
  | 1 => codeJ14R2
  | _ => codeJ10R3

end LeanVM.Protocol.Whir.Sound
end
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- `C_main` at S2 P20, Johnson: levels `(6,1,230) (4,2,115) (4,3,77)`, `g = 14`, OOD; root `0` of
`n₀` commitments. -/
def cfgMain24J (n₀ : ℕ) : WhirConfig := ⟨⟨24, [⟨6, 1, 230⟩, ⟨4, 2, 115⟩, ⟨4, 3, 77⟩], 8, 0, n₀, false, 14⟩, true⟩

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- `C_main` level 0's query group: `2^-14·eQuery ≤ 7·2^-131` (it is `2^-128.30`). -/
theorem query_main0J :
    (2 : ENNReal)⁻¹ ^ 14 * eQuery codeJ18R1 codeJ14R2 230 ≤ 7 * (2 : ENNReal)⁻¹ ^ 131 :=
  disc7 eQuery_J7.1

/-- `C_main`'s other query groups: `2^-14·eQuery ≤ 7·2^-131` (`2^-128.80`, `2^-129.44`). -/
theorem query_main12J :
    (2 : ENNReal)⁻¹ ^ 14 * eQuery codeJ14R2 codeJ10R3 115 ≤ 7 * (2 : ENNReal)⁻¹ ^ 131 ∧
      (2 : ENNReal)⁻¹ ^ 14 * eQueryFinal codeJ10R3 77 ≤ 7 * (2 : ENNReal)⁻¹ ^ 131 :=
  ⟨disc7 eQuery_J7.2.1, disc7 eQuery_J7.2.2.1⟩

/-- **`εmax` of `C_main` at the Johnson radius** (J1, J2): every group escape is at most `2^-128`,
with `2^-131` to spare. -/
theorem whirEps_main24J (n₀ : ℕ) :
    whirEpsJ codesMain24J (cfgMain24J n₀).grind (cfgMain24J n₀).levels + (2 : ENNReal)⁻¹ ^ 131 ≤
      (2 : ENNReal)⁻¹ ^ 128 := by
  obtain ⟨f0, f1, f2, -, -⟩ := eFold_J
  obtain ⟨o0, o1, -⟩ := eOod_J
  obtain ⟨q1, q2⟩ := query_main12J
  refine add_margin_le ?_
  simp only [whirEpsJ, cfgMain24J, levelEpsJ, max_le_iff]
  exact ⟨⟨le_seven_of (by norm_num) f0, le_seven_of (by norm_num) o0⟩, query_main0J,
    ⟨le_seven_of (by norm_num) f1, le_seven_of (by norm_num) o1⟩, q1,
    le_seven_of (by norm_num) f2, q2,
    le_seven_of (by norm_num) eTail_le⟩

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`εmax` of `C_rec` in unique decoding** (J1, R5's shape). -/
theorem whirEps_rec20U :
    whirEpsUd codesRec20U cfgRec20U.grind cfgRec20U.levels + (2 : ENNReal)⁻¹ ^ 131 ≤
      (2 : ENNReal)⁻¹ ^ 128 := by
  obtain ⟨f0, f1, q0, q1⟩ := eps_rec20U
  refine add_margin_le ?_
  simp only [whirEpsUd, cfgRec20U, levelEpsUd, max_le_iff]
  exact ⟨⟨le_seven_of (by norm_num) f0, disc7 q0⟩, le_seven_of (by norm_num) f1, disc7 q1,
    le_seven_of (by norm_num) eTail_le⟩

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

theorem ladderArith_main24J (n₀ : ℕ) :
    LadderArithJ (cfgMain24J n₀).μ (cfgMain24J n₀).per codesMain24J 0 0 (cfgMain24J n₀).levels := by
  obtain ⟨o0, o1, -⟩ := eOod_J
  obtain ⟨q0, q1, q2, -⟩ := eQuery_J7
  have h := seven_inv_lt_one
  have ho := inv_two_pow_lt_one (c := 170) (by norm_num)
  exact ⟨rfl, rfl, o0.trans_lt ho, q0.trans_lt h, by norm_num [cfgMain24J, codesMain24J, codeJ18R1],
    rfl, rfl, o1.trans_lt ho, q1.trans_lt h, by norm_num [cfgMain24J, codesMain24J, codeJ14R2],
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain24J, codesMain24J, codeJ10R3]⟩

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- **`C_main`'s stacked opening at the Johnson radius** (J1, J2): groups escape at most
`2^-128`. -/
noncomputable def stackedMain24JSpec (n₀ : ℕ) (hn₀ : 0 < n₀) (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine (cfgMain24J n₀).μ c.1) (T : ENNReal) :
    Spec (verifyStackedJ (cfgMain24J n₀) claims)
      (fun h ↦ StackedPreUd (cfgMain24J n₀).toUdConfig (codesMain24J 0) claims (commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) (eBatch claims.length (codesMain24J 0)) T :=
  stackedSpecJ claims hcl rfl rfl rfl (by norm_num [cfgMain24J]) rfl hn₀ (by norm_num [cfgMain24J])
    (by norm_num [cfgMain24J]) (ladderArith_main24J n₀) (le_of_add_margin (whirEps_main24J n₀)) T

/-- **`C_rec`'s stacked opening at the Johnson radius** (J2). -/
noncomputable def stackedRec20JSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20J.μ c.1) (T : ENNReal) :
    Spec (verifyStackedJ cfgRec20J claims)
      (fun h ↦ StackedPreUd cfgRec20J.toUdConfig (codesRec20J 0) claims (commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) (eBatch claims.length (codesRec20J 0)) T :=
  stackedSpecJ claims hcl rfl rfl rfl (by norm_num [cfgRec20J]) rfl (by norm_num [cfgRec20J])
    (by norm_num [cfgRec20J]) (by norm_num [cfgRec20J]) ladderArith_rec20J
    (le_of_add_margin whirEps_rec20J) T

/-- **`C_rec`'s stacked opening in unique decoding** (J1). -/
noncomputable def stackedRec20USpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20U.μ c.1) (T : ENNReal) :
    Spec (verifyStackedJ cfgRec20U claims)
      (fun h ↦ StackedPreUd cfgRec20U.toUdConfig (codesRec20U 0) claims (commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) (eBatch claims.length (codesRec20U 0)) T :=
  (stackedUdSpec (cfg := cfgRec20U.toUdConfig) (codes := codesRec20U) claims hcl rfl rfl
    (by norm_num [cfgRec20U]) rfl (by norm_num [cfgRec20U]) (by norm_num [cfgRec20U])
    (by norm_num [cfgRec20U]) ladderArith_rec20U
    (le_of_add_margin whirEps_rec20U) T).congr (verifyStackedJ_ud cfgRec20U rfl claims).symm

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
set_option exponentiation.threshold 512
section

/-- `C_main`'s candidates at the Johnson threshold (J1, J2): at most `98`. -/
theorem candidates_main24J_ncard_le (W : Word) :
    (Candidates 24 1 (codesMain24J 0).thr W).ncard ≤ 98 := -- layout-lint: allow (cfgMain24J's μ)
  candidates_ncard_le (codesMain24J 0) (by norm_num) rfl rfl W

/-- `C_rec`'s candidates at the Johnson threshold (J2): at most `231`. -/
theorem candidates_rec20J_ncard_le (W : Word) :
    (Candidates 19 3 (codesRec20J 0).thr W).ncard ≤ 231 :=
  candidates_ncard_le (codesRec20J 0) (by norm_num) rfl rfl W

end
end LeanVM.Protocol.Whir.Sound
end

-- ===== from `LvmWhirSuffixR` =====

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd VerifierProgram Finset
section

/-- The final level's fold count. -/
theorem finInfo_snd_snd : ∀ (i pre : ℕ) (levels : List Whir.Level) (hne : levels ≠ []),
    (finInfo i pre levels).2.2 = (levels.getLast hne).fold
  | _, _, [], hne => absurd rfl hne
  | _, _, [_], _ => rfl
  | i, pre, level :: next :: rest, _ => by
    rw [finInfo, finInfo_snd_snd (i + 1) (pre + level.fold) (next :: rest) (List.cons_ne_nil _ _),
      List.getLast_cons (List.cons_ne_nil _ _)]

/-- The final level's index. -/
theorem finInfo_index : ∀ (i pre : ℕ) (levels : List Whir.Level),
    (finInfo i pre levels).1 = i + (levels.length - 1)
  | _, _, [] => rfl
  | _, _, [_] => rfl
  | i, pre, level :: next :: rest => by
    rw [finInfo, finInfo_index (i + 1) (pre + level.fold) (next :: rest)]
    simp only [List.length_cons]
    omega

/-- The fold challenges before the final level. -/
theorem finInfo_snd_fst : ∀ (i pre : ℕ) (levels : List Whir.Level),
    (finInfo i pre levels).2.1 = pre + ((levels.dropLast).map (·.fold)).sum
  | _, _, [] => by simp [finInfo]
  | _, _, [_] => by simp [finInfo]
  | i, pre, level :: next :: rest => by
    rw [finInfo, finInfo_snd_fst (i + 1) (pre + level.fold) (next :: rest)]
    simp only [List.dropLast_cons_cons, List.map_cons, List.sum_cons]
    omega

end
end LeanVM.Protocol.Whir.Sound
end

section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd VerifierProgram Finset
section
variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P : LevelCode}
  {level : Whir.Level} {pre : ℕ} {εmax : ENNReal}

/-- **J2's `C_rec` after the residual** (final level `(3, 3, 77)`, index `1`, code `codeJ10R3`, `6`
fold challenges before it): from `ResC`, rejection but for `2^-14·eQueryFinal` and `eTail`, at
`εmax = 2^-128`. -/
noncomputable def finSuffixRec20JSpec (w : List E → E) (hw : IsMultiaffine 19 w)
    (a : (WhirStateT × List E) × List E) :
    Spec (finSuffixJ 19 laneBits 8 1 2 14 false w 1 ⟨3, 3, 77⟩ a)
      (fun h ↦ ResC 19 laneBits w 1 codeJ10R3 3 6 a.1 a.2 (viewC 1 2 (commits h)))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) ((2 : ENNReal)⁻¹ ^ 14 * eQueryFinal codeJ10R3 77) 0 :=
  finSuffixSpecR (level := ⟨3, 3, 77⟩) ⟨hw, by norm_num, by norm_num [codeJ10R3], rfl, by norm_num,
      by norm_num, by norm_num [codeJ10R3]⟩ (by norm_num)
    (eQuery_J7.2.2.1.trans_lt seven_inv_lt_one)
    ((disc7 eQuery_J7.2.2.1).trans (le_self_add.trans_eq seven_add_one))
    (eTail_le.trans (inv_two_pow_anti (by norm_num))) a

end
end LeanVM.Protocol.Whir.Sound
end
