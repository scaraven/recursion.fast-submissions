-- New for lvm2 (WP JB-L, J2): a WHIR level with a next commitment under the relativised doom, the twin of
-- `LvmWhirMidJ` (itself ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/{LevelMid,LevelMidSpec}.lean`,
-- formal rev 0b850750) on the program cut at the residual (`LvmWhirPrefixJ`). Changed against `LvmWhirMidJ`: the
-- doom is `ViolR` for a good set `Gd`, the next level starts from `gdNext`, and the post is `PostR`.
/-
  LeanVM.Protocol.Whir.Sound.MidR
-/
import LvmWhirFoldsR
import LvmWhirPrefixJ
import LvmWhirPathR
import LvmWhirMidJ

-- ===== merged from `LvmWhirEscapeR` (GOLF module merge: `LvmWhirEscapeR.lean` is now a stub importing `LvmWhirMidR`) =====
section
-- New for lvm2 (WP JB-L, J2): the escapes at the level interface with an out-of-domain step for the relativised doom
-- (`ViolR`, `LvmWhirPathR`). Twins of `QueryGood`, `exists_agreeSet`, `card_lambda_bad_le`, `escRet_queryFrag_le`
-- (`LvmWhirEscapeJ`, ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Escape.lean`, formal rev 0b850750)
-- and `escRet_queryFragG_le` (`LvmWhirMidJ`): only the tracked members of the lists are counted; same bounds.
/-
  LeanVM.Protocol.Whir.Sound.EscapeR

  The escapes of a WHIR level interface with an out-of-domain step, relativised to the members
  that are on no path of the good set `Gd`.
-/

/-!
# Escapes at the level interface, relativised

The doom on the folded word `C` is `ViolR P Gd fs (fun _ ↦ C) Φ σ`: every **tracked** member of
`C`'s list (on no path of `Gd` after the fold challenges `fs`) violates the running claim.

* `QueryGoodR`: after positions `qs`, every tracked member `V` of the next list violates the running
  claim, or the out-of-domain claim, or the consistency claim at some queried column.
* `exists_agreeSet_R`: under the relativised doom and `OodSep`, the positions breaking `QueryGoodR`
  lie in a set of at most `thr − 1` columns. The one tracked member `V*` consistent with the running
  claim and the out-of-domain answer has a joined message whose encoding agrees with `C` on fewer
  than `thr` columns: otherwise that encoding is a member of `C`'s list, tracked
  (`pathAt_joinMsg_iff`), so it violates the running claim by the doom.
* `card_lambda_bad_le_R`: under `QueryGoodR`, at most `(t + 1)·listMax'` values `λ` break `ViolR`
  for the glued claim.
* `escRet_queryFrag_le_R`, `escRet_queryFragG_le_R`: the query group escapes the glued claim's
  relativised doom with probability at most `eQuery P P' t` (`2^-g · eQuery P P' t` with the proof
  of work).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-- After positions `qs`, every tracked member of the list of `Q'` violates the running claim
`(Φ, σ)`, the out-of-domain claim `(eq_eval(z, ·), y)`, or the consistency claim at a queried
column of the folded word `C`. -/
def QueryGoodR (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ) {μ : ℕ} (Gd : Set (Column μ))
    (fs : List E) (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (qs : List ℕ) : Prop :=
  ∀ V ∈ iList P'.code P'.thr Q', Tracked Gd fs (decode P' V) →
    claimSum Φ (decode P' V) ≠ σ ∨ oodVal z (decode P' V) ≠ y ∨
      ∃ q ∈ qs, encAt P.κ P.R (joinMsg hκ (decode P' V)) q ≠ wordAt C q

/-- **The query step, relativised.** Under the relativised doom before the positions (every tracked
member of the list of the folded word `C` violates `(Φ, σ)`, and the out-of-domain values separate
the list of `Q'`), the positions breaking `QueryGoodR` all lie in a set of at most `thr − 1`
columns. -/
theorem exists_agreeSet_R (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ) {μ : ℕ}
    (Gd : Set (Column μ)) (fs : List E)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : ViolR P Gd fs (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodR P P' hκ Gd fs Q' C Φ σ z y qs → ∀ q ∈ qs, ∀ h : q < P.n,
        (⟨q, h⟩ : Fin P.n) ∈ A := by
  classical
  by_cases hex : ∃ V ∈ iList P'.code P'.thr Q', Tracked Gd fs (decode P' V) ∧
      claimSum Φ (decode P' V) = σ ∧ oodVal z (decode P' V) = y
  · obtain ⟨V₀, hV₀, htr, hclaim, hood⟩ := hex
    set G := joinMsg hκ (decode P' V₀)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      have hclose : P.thr ≤ (univ.filter fun x ↦ enc P.κ P.R G x = C x).card :=
        Nat.lt_succ_iff.mp (not_le.mp hlt)
      have htrG : Tracked Gd fs (decode P (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G)) := by
        rw [decode_enc P (fun _ ↦ G)]
        exact fun q hq hp ↦ htr q hq ((pathAt_joinMsg_iff hκ q fs _).mp hp)
      have h := hviol _ (mem_iList_of_close P C G hclose) htrG
      rw [decode_enc P (fun _ ↦ G), claimSum_zero] at h
      exact h (by rw [sum_joinMsg]; exact hclaim)
    · intro hlt
      simp only [QueryGoodR, not_forall, not_or, not_not, exists_prop, not_exists, not_and] at hqs
      obtain ⟨V, hV, -, hc, ho, hall⟩ := hqs
      have hVV : V = V₀ := by
        by_contra hne
        exact hsep V hV V₀ hV₀ hne (ho.trans hood.symm)
      subst hVV
      have h := hall q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd ?_ hqs⟩
    intro V hV htr
    by_contra h
    simp only [not_or, not_not] at h
    exact hex ⟨V, hV, htr, h.1, h.2.1⟩

open Classical in
/-- **The batching step of a level with a next commitment, relativised.** -/
theorem card_lambda_bad_le_R (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) {μ : ℕ}
    (Gd : Set (Column μ)) (fs : List E)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n)
    (hgood : QueryGoodR P P' hκ Gd fs Q' C Φ σ z y qs) :
    (univ.filter fun lam : E ↦ ¬ ViolR P' Gd fs Q'
        (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])).card ≤
      (qs.length + 1) * P'.listMax := by
  set L := iList P'.code P'.thr Q'
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans
    ((card_filter_exists_le L (fun V lam ↦ Tracked Gd fs (decode P' V) ∧
        claimSum Φ (decode P' V) + lam * oodVal z (decode P' V) + lam * lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R (joinMsg hκ (decode P' V)) qs[k] =
        σ + lam * y + lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])
      (N := qs.length + 1) fun V hV ↦ ?_).trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ViolR, not_forall, not_not,
      exists_prop] at hlam ⊢
    obtain ⟨V, hV, htr, heq⟩ := hlam
    refine ⟨V, hV, htr, ?_⟩
    rw [claimSum_glue2, claimSum_inducedWeight P hκ qs hqs lam] at heq
    rw [oodVal]
    simpa only [one_mul] using heq
  · by_cases htr : Tracked Gd fs (decode P' V)
    · refine (Finset.card_le_card fun lam hlam ↦ ?_).trans (card_glue_bad_le
        (claimSum Φ (decode P' V)) σ (oodVal z (decode P' V)) y
        (fun k : Fin qs.length ↦ encAt P.κ P.R (joinMsg hκ (decode P' V)) qs[k])
        (fun k : Fin qs.length ↦ wordAt C qs[k]) ?_)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        exact hlam.2
      · rcases hgood V hV htr with h | h | ⟨q, hq, hne⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
          exact Or.inr (Or.inr ⟨⟨k, hk⟩, hne⟩)
    · simp [htr]
  · rw [mul_comm]
    exact Nat.mul_le_mul_left _ (P'.card_iList_le Q')

open Classical in
/-- **The query group of a level with a next commitment, relativised.** -/
theorem escRet_queryFrag_le_R (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    {μ : ℕ} (Gd : Set (Column μ)) (fs : List E)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : ViolR P Gd fs (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      ViolR P' Gd fs Q' (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag per (P.κ + P.R) t c) ≤
      eQuery P P' t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet_R P P' hκ Gd fs Q' C Φ σ z y hviol hsep
  refine (retExp_queryFrag_le per (P.κ + P.R) t c hper hpd h₀ hW _
    (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A)
    ((((t + 1) * P'.listMax : ℕ) : ENNReal) / Fintype.card E) ?_).trans ?_
  · intro qs hr hlen
    by_cases hall : ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A
    · have : allIn (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) qs = 1 := by
        unfold allIn
        split_ifs with h
        · rfl
        · exact absurd hall h
      rw [this]
      exact (avg_le_one _ fun _ ↦ by split_ifs <;> simp).trans le_self_add
    · have hgood : QueryGoodR P P' hκ Gd fs Q' C Φ σ z y qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le_R P P' hκ Gd fs Q' C Φ σ z y qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦ ¬ ViolR P' Gd fs Q'
          (fun r ↦ Φ r + 1 * lam * eqEval z r +
            1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
          (σ + 1 * lam * y + 1 * lam * lam *
            ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])) fun lam hlam ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        exact fun hv ↦ hlam (hJ qs lam hr hlen hv)
      rw [← hlen]
      exact_mod_cast hsub.trans hcard
  · rw [card_filter_mem, eQuery]
    exact add_le_add (pow_frac_le P A hA t) le_rfl

open Classical in
/-- **The query group of a level with a next commitment and an OOD sample, with the proof of
work, relativised.** -/
theorem escRet_queryFragG_le_R (g : ℕ) (hg : g ≤ 192) (P P' : LevelCode) {ℓ' : ℕ}
    (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ) (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    {μ : ℕ} (Gd : Set (Column μ)) (fs : List E)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : ViolR P Gd fs (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      ViolR P' Gd fs Q' (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFragG g per (P.κ + P.R) t c) ≤
      (2 : ENNReal)⁻¹ ^ g * eQuery P P' t := by
  refine escRet_powCheck_le g hg _ h₀ _ _ fun h hh ↦ ?_
  rw [← hh] at hW
  refine escRet_queryFrag_le_R P P' hκ per t c hper hpd h hW Gd fs Q' C Φ σ z y hviol hsep
    (fun g cs ↦ J g cs) fun qs lam hr hlen hv ↦ ?_
  rw [hh]
  exact hJ qs lam hr hlen hv

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirEscapeR` =====

/-!
# A level with a next commitment, relativised

`whirPrefixJ μ per c₀ n₀ g i (level :: next :: rest) s` is the fold rounds, then `midTailPJ`
(commitment, OOD point `z`, OOD answer `y` and its intro polynomial, `grindPre g`, the query group
with the proof of work, the query intro polynomial, the glue, the next levels' prefix).

* Combinators: `specRetFact` (a fact of every return of the program joins the post),
  `specCases` (a case split on a proposition of the parameters), `specAnchor` (the post may name
  the start history `h₁`, a prefix of the end history).
* Doom along the level: `AfterFoldR`, `MidCR` (the next oracle committed), `OodCR` (the next list
  is separated at `z`), `GlueCR` (every tracked member of the next list violates the glued claim);
  `levelPre_nextR` gives `LevelPreR` of the next level for `gdNext` (`tracked_gdNext_iff`).
* `midSpecR`: from `LevelPreR` of level `i` for `Gd`, the level's groups escape with probability
  at most `eFold`, `eOod`, `2^-g·eQuery` (R2's `escRet_queryFragG_le_R`), and the level hands
  `LevelPreR` of level `i + 1` for `gdNext … (view) s'.folds Gd` to the next levels' spec `K`;
  the post is `s.folds <+: a.folds ∧ PostR … i pre (level :: next :: rest) Gd a h`
  (`postR_mid`: `PostR` of the next levels for `gdNext` is `PostR` of this level).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-! ## Combinators -/

section Combinators

variable {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop}
  {εmax L T : ENNReal}

/-- **A fact of every return** of the program joins the post. -/
def specRetFact {R : α → Prop} (S : Spec p Pre Post εmax L T)
    (hR : ∀ {l : List Ev} {a : α}, p.after l = some (.ret a) → R a) :
    Spec p Pre (fun a h ↦ R a ∧ Post a h) εmax L T :=
  { S with post := fun hl ha hD ↦ ⟨hR ha, S.post hl ha hD⟩ }

open Classical in
/-- **A case split** on a proposition (of the parameters, not of the history). -/
noncomputable def specCases (c : Prop) (S₁ : c → Spec p Pre Post εmax L T)
    (S₂ : ¬ c → Spec p Pre Post εmax L T) : Spec p Pre Post εmax L T :=
  if hc : c then S₁ hc else S₂ hc

/-- **The start history in the post**: a family of specifications, one per start history `h₁`,
gives a specification whose post holds for some prefix `h₁` of the end history. -/
def specAnchor {Q : List Ev → α → List Ev → Prop}
    (S : ∀ h₁, Spec p (fun h ↦ h = h₁ ∧ Pre h) (Q h₁) εmax L T) :
    Spec p Pre (fun a h ↦ ∃ h₁, h₁ <+: h ∧ Q h₁ a h) εmax L T where
  D h₀ l := (S h₀).D h₀ l
  V h₀ l := (S h₀).V h₀ l
  le_one h₀ l := (S h₀).le_one h₀ l
  start_D h₀ hp := (S h₀).start_D h₀ ⟨rfl, hp⟩
  start_V h₀ hp := (S h₀).start_V h₀ ⟨rfl, hp⟩
  read {h₀ _ _} x hl ha hD := (S h₀).read x hl ha hD
  grind {h₀ _ _ _} hl ha hD := (S h₀).grind hl ha hD
  commit {h₀ _ _ _ _} word hl ha hw hD := (S h₀).commit word hl ha hw hD
  sample {h₀ _ _} hl ha := (S h₀).sample hl ha
  query {h₀ _ _ _ _ _} hl ha hq := (S h₀).query hl ha hq
  moveEnd {h₀ _ _} hl ha hm hD := (S h₀).moveEnd hl ha hm hD
  retEnd {h₀ _ _} hl ha hD := (S h₀).retEnd hl ha hD
  retDoom {h₀ _ _} hl ha hD := (S h₀).retDoom hl ha hD
  post {h₀ _ _} hl ha hD := ⟨h₀, List.prefix_append _ _, (S h₀).post hl ha hD⟩
  bound {h₀ _} hl hne hm hD := (S h₀).bound hl hne hm hD

end Combinators

/-! ## Doom along the level -/

section Doom

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (ℓ ℓ' pre : ℕ)
  (Gd : Set (Column μ))

/-- After the commitment of the next oracle (`MidC` relativised). -/
def MidCR (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ∃ cs₀ W', cs = cs₀ ++ [(P'.κ + P'.R, 3 * 2 ^ ℓ', W')] ∧ WellShaped (3 * 2 ^ ℓ') W' ∧
    AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs₀

/-- After the out-of-domain point: the next list is separated at `z`. -/
def OodCR (r : WhirStateT × List E) (z : List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidCR μ ℓ₀ w i P P' ℓ ℓ' pre Gd r cs ∧ z.length = P.κ ∧
    OodSep P' (rowsOf ℓ' (laneO (i + 1) cs P'.n)) z

/-- After the query group: every tracked member of the next list violates the glued claim. -/
def GlueCR (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E)
    (g : List ℕ × E × List (List K)) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (QuadOK hy y ∧ OodCR μ ℓ₀ w i P P' ℓ ℓ' pre Gd r z cs) ∧
    ViolR P' Gd r.1.folds (rowsOf ℓ' (laneO (i + 1) cs P'.n))
      (runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []))
      (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []).target

end Doom

/-! ## Bookkeeping lemmas -/

section Lemmas

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {ℓ ℓ' pre : ℕ}
  {Gd : Set (Column μ)}

theorem afterFoldR_len {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs) : r.1.folds.length = pre + ℓ := by
  obtain ⟨⟨⟨hl, -⟩, -⟩, hr⟩ := h
  omega

theorem afterFoldR_κ {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs) : μ - r.1.folds.length = P.κ := by
  have := afterFoldR_len h
  obtain ⟨⟨⟨-, -, hκ, -⟩, -⟩, -⟩ := h
  omega

/-- The glue keeps the fold challenges. -/
theorem glueMid_folds (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ)
    (lam : E) (words : List (List K)) (hq : List E) :
    (glueMid μ i r z y hy qs lam words hq).folds = r.1.folds := by
  rw [glueMid, glue_twoJ]

/-- After the commitment: the next oracle's word is appended. -/
theorem midCR_of_commit {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)} {W : Word}
    (next : Whir.Level) (hℓ' : next.fold = ℓ') (hP' : P'.κ + (pre + ℓ) + ℓ' = μ)
    (hR' : P'.R = next.logInvRate) (h : AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs)
    (hW : WellShaped (3 * 2 ^ next.fold) W) :
    MidCR μ ℓ₀ w i P P' ℓ ℓ' pre Gd r
      (cs ++ [(μ - r.1.folds.length - next.fold + next.logInvRate, 3 * 2 ^ next.fold, W)]) := by
  have hlen := afterFoldR_len h
  subst hℓ'
  refine ⟨cs, W, ?_, hW, h⟩
  congr 3
  omega

/-- The commitments after the next commitment, at index `i`. -/
theorem midCR_word {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : MidCR μ ℓ₀ w i P P' ℓ ℓ' pre Gd r cs) :
    ∃ cs₀, cs[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs₀ i) ∧ wordOf cs i = wordOf cs₀ i ∧
      laneO i cs P.n = laneO i cs₀ P.n ∧ AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs₀ := by
  obtain ⟨cs₀, W', rfl, -, haf⟩ := h
  have hsh := haf.1.2
  have hi : i < cs₀.length := by rw [hsh.1]; omega
  exact ⟨cs₀, shapeOK_append hsh _, wordOf_append _ _ hi, laneO_append _ _ hi _, haf⟩

/-- **The next level's relativised doom** from the glued doom and the query intro polynomial,
for the next good set `gdNext`. -/
theorem levelPre_nextR (hP' : P'.κ + (pre + ℓ) + ℓ' = μ) (r : WhirStateT × List E) (z : List E)
    (y : E) (hy : List E) (g : List ℕ × E × List (List K)) (hq : List E)
    (cs : List (ℕ × ℕ × Word)) (hglue : GlueCR μ ℓ₀ w i P P' ℓ ℓ' pre Gd r z y hy g cs)
    (hhq : QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2)) :
    LevelPreR μ ℓ₀ w (i + 1) P' ℓ' (pre + ℓ)
      (gdNext P' ℓ' (i + 1) cs (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq).folds Gd)
      (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq) cs := by
  obtain ⟨⟨hhy, ⟨cs₀, W', rfl, hW', haf⟩, hz, -⟩, hviol⟩ := hglue
  have hlen := afterFoldR_len haf
  have hκm := afterFoldR_κ haf
  obtain ⟨⟨⟨-, -, -, hg, hquad, -⟩, hshape⟩, -⟩ := haf
  refine ⟨⟨?_, by simp, hP', ?_, ?_, ?_⟩, ?_⟩
  · rw [glueMid, glue_twoJ]; simp [hlen]
  · intro c hc
    rw [glueMid, glue_twoJ] at hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rw [glueMid, glue_twoJ]
    rcases hc with hc | rfl | rfl
    · exact hg c hc
    · refine ⟨le_rfl, ?_⟩
      rw [hκm, ← hz]
      exact isMultiaffine_eqEval z
    · exact ⟨le_rfl, isMultiaffine_inducedWeight _ _ _ (length_powers _ _)⟩
  · rw [glueMid, glue_twoJ]
    exact quadOK_zipWith (quadOK_zipWith hquad hhy _) hhq _
  · have hr : runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq) =
        runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []) := by
      rw [glueMid_runW, glueMid_runW]
    have ht : (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq).target =
        (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []).target := by
      rw [glueMid_target, glueMid_target]
    simp only [List.length_nil, Nat.sub_zero, foldsN, List.foldl_nil, hr, ht, glueMid_folds]
    intro V hV htr
    exact hviol V hV ((tracked_gdNext_iff P' ℓ' (i + 1) _ r.1.folds Gd hV).mp htr)
  · refine ⟨by simp [hshape.1], W', ?_, ?_⟩
    · rw [List.getElem?_append_right (by rw [hshape.1]), hshape.1, Nat.sub_self]
      simp [wdOf]
    · simpa [wdOf] using hW'

/-- **The post of the next levels is the post of this level**: `PostR` from level `i + 1` for
`gdNext` at the fold challenges `fs` of the level's end, `fs` a prefix of the run's. -/
theorem postR_mid {ℓ₀ c₀ n₀ : ℕ} {w : List E → E} {codes : ℕ → LevelCode} {pre : ℕ}
    {level next : Whir.Level} {rest : List Whir.Level} {fs : List E}
    (hfs : fs.length = pre + level.fold) {a : (WhirStateT × List E) × List E} {h : List Ev}
    (hpre : fs <+: a.1.1.folds)
    (hp : PostR μ ℓ₀ w codes c₀ n₀ (i + 1) (pre + level.fold) (next :: rest)
      (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) fs Gd) a h) :
    PostR μ ℓ₀ w codes c₀ n₀ i pre (level :: next :: rest) Gd a h := by
  have ht : a.1.1.folds.take (pre + level.fold) = fs := by
    rw [← hfs]; exact (List.prefix_iff_eq_take.mp hpre).symm
  simp only [PostR, finInfo, gdFinal, ht]
  exact hp

end Lemmas

/-! ## The specification -/

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {w : List E → E} {codes : ℕ → LevelCode} {i : ℕ}
  {level next : Whir.Level} {rest : List Whir.Level} {pre : ℕ} {Gd : Set (Column μ)}
  {εmax T : ENNReal}

/-- The query group of a level with a next level, the query intro polynomial and the next
levels' prefix. -/
noncomputable def midQuerySpecR
    (H : MidHypJ μ ℓ₀ per c₀ n₀ w (codes i) (codes (i + 1)) level next pre) (hg : g ≤ 192)
    (hQlt : eQuery (codes i) (codes (i + 1)) level.queries < 1)
    (K : ∀ s', Spec (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s')
      (fun h ↦ LevelPreR μ ℓ₀ w (i + 1) (codes (i + 1)) next.fold (pre + level.fold)
        (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) s'
        (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s'.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ (i + 1) (pre + level.fold) (next :: rest)
          (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) a h)
      εmax εmax T)
    (r : WhirStateT × List E) (hr : r.1.folds.length = pre + level.fold) (z : List E) (y : E)
    (hy : List E) :
    Spec ((queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i)).bind fun gg ↦
          midFinishPJ μ per c₀ n₀ g i next rest r z y hy gg.1 gg.2.1 gg.2.2)
      (fun h ↦ QuadOK hy y ∧ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd
        r z (viewC c₀ n₀ (commits h)))
      (fun a h ↦ r.1.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ i pre (level :: next :: rest) Gd a h)
      εmax ((2 : ENNReal)⁻¹ ^ g * eQuery (codes i) (codes (i + 1)) level.queries) T :=
  ((Spec.ofNoMove (p := queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i))
      (Pre := fun h ↦ QuadOK hy y ∧ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold
        pre Gd r z (viewC c₀ n₀ (commits h)))
      (Post := fun gg h ↦ GlueCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd
        r z y hy gg (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_queryFragG _ _ _ _ _).noMove
      ((grind_disc_le g _).trans_lt hQlt) fun h₀ hp ↦ by
        obtain ⟨cs₀, hW, -, -, haf⟩ := midCR_word hp.2.1
        have hκm := afterFoldR_κ haf
        have hd : μ - r.1.folds.length + level.logInvRate = (codes i).κ + (codes i).R := by
          rw [hκm, H.hR]
        have hκ' : (codes i).κ = next.fold + (codes (i + 1)).κ := by
          have := H.hP; have := H.hP'; omega
        have hlf : r.2.length = level.fold := haf.2
        have hviol : ViolR (codes i) Gd r.1.folds
            (fun _ : Fin 0 → Bool ↦ fun v ↦ foldsN r.2 (laneO i cs₀ (codes i).n) 0 v)
            (runW w ℓ₀ r.1) r.1.target := by
          have := haf.1.1.2.2.2.2.2
          rwa [hlf, Nat.sub_self, rowsOf_zero] at this
        have hW' := commits_cidx H.hc hW
        rw [hd]
        refine escRet_queryFragG_le_R g hg (codes i) (codes (i + 1)) hκ' per level.queries
          (cidx c₀ n₀ i) H.hper H.hpd h₀ hW' Gd r.1.folds
          (rowsOf next.fold (laneO (i + 1) (viewC c₀ n₀ (commits h₀)) (codes (i + 1)).n)) _
          (runW w ℓ₀ r.1) r.1.target z y hviol hp.2.2.2
          (fun gg cs ↦ GlueCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r z y
            hy gg (viewC c₀ n₀ cs))
          fun qs lam hr' hlen hv ↦ ⟨hp, ?_⟩
        rw [glueMid_runW, glueMid_target, enfOf_eq haf.1.2 r.2 hlf qs hr' lam, hκm]
        exact hv).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun gg ↦
    (roundPolyInv (fun cs ↦ GlueCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd
        r z y hy gg (viewC c₀ n₀ cs)) (enfOf i r.2 gg.1 gg.2.1 gg.2.2) (T := εmax) le_rfl).bind'
      fun hq ↦
      (K (glueMid μ i r z y hy gg.1 gg.2.1 gg.2.2 hq)).mono
        (fun h hp ↦ levelPre_nextR H.hP' r z y hy gg hq _ hp.2 hp.1)
        (fun a h hp ↦ by
          rw [glueMid_folds] at hp
          exact ⟨hp.1, postR_mid hr hp.1 hp.2⟩)
        le_rfl le_rfl le_rfl

/-- After the fold rounds of a level with a next level: the commitment, the out-of-domain group,
the OOD answer and intro polynomial, the moves before the proof of work, the query group. -/
noncomputable def midTailSpecR
    (H : MidHypJ μ ℓ₀ per c₀ n₀ w (codes i) (codes (i + 1)) level next pre) (hg : g ≤ 192)
    (hεO : eOod (codes (i + 1)) (codes i).κ ≤ εmax) (hOlt : eOod (codes (i + 1)) (codes i).κ < 1)
    (hQlt : eQuery (codes i) (codes (i + 1)) level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQuery (codes i) (codes (i + 1)) level.queries ≤ εmax)
    (K : ∀ s', Spec (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s')
      (fun h ↦ LevelPreR μ ℓ₀ w (i + 1) (codes (i + 1)) next.fold (pre + level.fold)
        (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) s'
        (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s'.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ (i + 1) (pre + level.fold) (next :: rest)
          (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) a h)
      εmax εmax T)
    (r : WhirStateT × List E) (hr : r.1.folds.length = pre + level.fold) :
    Spec (midTailPJ μ per c₀ n₀ g i level next rest r)
      (fun h ↦ AfterFoldR μ ℓ₀ w i (codes i) level.fold pre Gd r (viewC c₀ n₀ (commits h)))
      (fun a h ↦ r.1.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ i pre (level :: next :: rest) Gd a h) εmax 0 T :=
  (commitInv (fun cs ↦ AfterFoldR μ ℓ₀ w i (codes i) level.fold pre Gd r (viewC c₀ n₀ cs))
      (fun cs ↦ MidCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r
        (viewC c₀ n₀ cs))
      (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
      (fun cs W h hW ↦ by
        rw [viewC_append (le_length_of_viewC (ne_nil_of_shapeOK h.1.2))]
        exact midCR_of_commit next rfl H.hP' H.hR' h hW)
      (T := eOod (codes (i + 1)) (codes i).κ) hεO).bind' fun _ ↦
  ((Spec.ofNoMove (p := sampleChallenges (μ - r.1.folds.length))
      (Pre := fun h ↦ MidCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r
        (viewC c₀ n₀ (commits h)))
      (Post := fun z h ↦ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r z
        (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_sampleN _).noMove hOlt fun h₀ hp ↦ by
        obtain ⟨cs₀, -, -, -, haf⟩ := midCR_word hp
        have hκm := afterFoldR_κ haf
        have hκ : μ - r.1.folds.length = next.fold + (codes (i + 1)).κ := by
          rw [hκm]; have := H.hP; have := H.hP'; omega
        have hκ1 : 1 ≤ μ - r.1.folds.length := by rw [hκm]; exact (codes i).hκ
        refine (escRet_sampleN_le (codes (i + 1)) hκ hκ1
          (rowsOf next.fold (laneO (i + 1) (viewC c₀ n₀ (commits h₀)) (codes (i + 1)).n))
          (fun z cs ↦ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r z
            (viewC c₀ n₀ cs)) h₀
          fun z hz hsep ↦ ⟨hp, hz.trans hκm, hsep⟩).trans (by rw [hκm])).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun z ↦
  (readInv (fun cs ↦ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r z
      (viewC c₀ n₀ cs)) (T := 0) zero_le).bind' fun y ↦
  (roundPolyInv (fun cs ↦ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r z
      (viewC c₀ n₀ cs)) y
      (T := (2 : ENNReal)⁻¹ ^ g * eQuery (codes i) (codes (i + 1)) level.queries) hεQ).bind'
    fun hy ↦
  (grindPreInv (fun cs ↦ QuadOK hy y ∧ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold
      next.fold pre Gd r z (viewC c₀ n₀ cs)) g hεQ).bind' fun _ ↦
  (midQuerySpecR H hg hQlt K r hr z y hy).congr
    (query_bindG' per g (cidx c₀ n₀ i) (μ - r.1.folds.length + level.logInvRate) level.queries
      fun qs lam words ↦ midFinishPJ μ per c₀ n₀ g i next rest r z y hy qs lam words).symm

/-- **The specification of a level with a next level, relativised**, on the program cut at the
residual: from `LevelPreR` for `Gd`, the post is `PostR` for `Gd` and the fold challenges extend
`s.folds`. -/
noncomputable def midSpecR
    (H : MidHypJ μ ℓ₀ per c₀ n₀ w (codes i) (codes (i + 1)) level next pre) (hg : g ≤ 192)
    (hεF : eFold (codes i) level.fold ≤ εmax) (hεO : eOod (codes (i + 1)) (codes i).κ ≤ εmax)
    (hOlt : eOod (codes (i + 1)) (codes i).κ < 1)
    (hQlt : eQuery (codes i) (codes (i + 1)) level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQuery (codes i) (codes (i + 1)) level.queries ≤ εmax)
    (K : ∀ s', Spec (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s')
      (fun h ↦ LevelPreR μ ℓ₀ w (i + 1) (codes (i + 1)) next.fold (pre + level.fold)
        (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) s'
        (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s'.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ (i + 1) (pre + level.fold) (next :: rest)
          (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) a h)
      εmax εmax T)
    (s : WhirStateT) :
    Spec (whirPrefixJ μ per c₀ n₀ g i (level :: next :: rest) s)
      (fun h ↦ LevelPreR μ ℓ₀ w i (codes i) level.fold pre Gd s (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ i pre (level :: next :: rest) Gd a h) εmax εmax T :=
  (((specRetFact (R := fun r ↦ s.folds <+: r.1.folds)
      (foldRoundsSpecR μ ℓ₀ w i (codes i) level.fold pre Gd (viewC c₀ n₀)
        (fun cs ↦ ShapeOK i (codes i) level.fold (viewC c₀ n₀ cs)) H.hw H.hℓ₀ hεF level.fold s [])
      fun ha ↦ foldRoundsT_folds_prefix _ _ _ ha).bind' fun r ↦
    specCases (s.folds <+: r.1.folds ∧ r.1.folds.length = pre + level.fold)
      (fun hr ↦ (midTailSpecR H hg hεO hOlt hQlt hεQ K r hr.2).mono (fun _ hp ↦ hp.2)
        (fun _ _ hp ↦ ⟨hr.1.trans hp.1, hp.2⟩) le_rfl le_rfl le_rfl)
      (fun hr ↦ Spec.dead.mono (fun _ hp ↦ hr ⟨hp.1, afterFoldR_len hp.2⟩) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl)).mono
    (fun _ hp ↦ ⟨⟨hp.1, hp.2⟩, by simp⟩) (fun _ _ h ↦ h) le_rfl hεF le_rfl).congr
    (whirPrefixJ_mid μ per c₀ n₀ g i level next rest s).symm

end
end LeanVM.Protocol.Whir.Sound
