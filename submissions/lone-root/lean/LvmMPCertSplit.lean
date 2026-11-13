-- New for lvm2 roll 11 (M′, R11-C): the history parser of M′'s run up to `C_main`'s residual, and the luck's
-- readers on it. Adapted from `LvmCertSExtJSplit` (`recPrefix_split`, `folds_splitJ`, `foldChal_of_splitJ`,
-- `rec1Of_of_splitJ`, `foldChal1J_of_splitJ`), with a level-generic step (`midTailPJ_split`).
import LvmMPCertLuck
import LvmMPCertOpen
import LvmCertSExtJSplit

/-!
# M′'s history parser

`C_main`'s opening at M′ (`stackPrefixJ (cfgMain23Jq 1)`, levels `(6,2,115) (4,3,77) (4,4,58)`, `g = 14`, OOD)
up to the residual: `ρ`, the first round polynomial, level 0's six fold rounds, then twice a level step
(`midTailPJ_split`: the next level's cap, the OOD point, answer and intro, the query group, the query intro;
`17 + 18 = 35` and `13 + 13 = 26` challenges, no commitment) and the next level's four fold rounds, then the
residual.

* **`mainPrefix_split`**: a completed run of the program up to the residual (`LvmMPCert`'s `mainPrefixProg`) is
  the root `W₀`, the middle phases, and the opening as above, with the level-1 and level-2 caps `W₁`, `W₂` and
  the fold states `r0`, `r1`, `r2` (`r2.1.folds = r0.2 ++ r1.2 ++ r2.2`);
* **`readersM_of_split`**: on such a history (and any events after it) the luck's readers read `W₀, W₁, W₂`
  and the fold challenges `r0.2, r1.2, r2.2`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir

/-! ## A level step -/

theorem take_drop_appendM {S A B : List E} {d k : ℕ} (hS : S.length = d) (hA : A.length = k) :
    ((S ++ (A ++ B)).drop d).take k = A := by
  rw [List.drop_left' hS, List.take_left' hA]

/-- **A level with a next level, after its fold rounds** (`midTailPJ`, `g ≠ 0`): the next level's cap, then
`μ − |folds|` OOD coordinates, the query group's `1 + (posCount + 2)` challenges and reads, no commitment; then
the next levels from a state with the same fold challenges. -/
theorem midTailPJ_split {μ per c₀ n₀ g i : ℕ} {level next : Whir.Level} {rest : List Whir.Level}
    {r : WhirStateT × List E} {l : List Ev} {b : (WhirStateT × List E) × List E} (hg : g ≠ 0)
    (h : (midTailPJ μ per c₀ n₀ g i level next rest r).after l = some (.ret b)) :
    ∃ (W : Compile.Word) (lm l' : List Ev) (s' : WhirStateT),
      l = Ev.commit (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold) W :: (lm ++ l') ∧
      commits lm = [] ∧
      (lm.filterMap sampleOf).length = (μ - r.1.folds.length) + (1 + (posCount per level.queries level.queries + 2)) ∧
      s'.folds = r.1.folds ∧ (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s').after l' = some (.ret b) := by
  unfold midTailPJ at h
  obtain ⟨_, lc, l₁, rfl, hc, h1⟩ := after_bind_ret h
  obtain ⟨W, rfl⟩ := readCommitment_after hc
  obtain ⟨z, lz, l₂, rfl, hz, h2⟩ := after_bind_ret h1
  obtain ⟨y, ly, l₃, rfl, hy, h3⟩ := after_bind_ret h2
  obtain ⟨hy', lhy, l₄, rfl, hhy, h4⟩ := after_bind_ret h3
  obtain ⟨_, lgp, l₅, rfl, hgp, h5⟩ := after_bind_ret h4
  rw [query_bindG'] at h5
  obtain ⟨gg, lgq, l₆, rfl, hgq, h6⟩ := after_bind_ret h5
  unfold midFinishPJ at h6
  obtain ⟨hq, lhq, l₇, rfl, hhq, h7⟩ := after_bind_ret h6
  obtain ⟨rfl, hzl⟩ := sampleChallenges_after _ hz
  refine ⟨W, z.map Ev.sample ++ (ly ++ (lhy ++ (lgp ++ (lgq ++ lhq)))), l₇, _, by simp, ?_, ?_,
    glueMid_folds _ _ _ _ _ _ _ _, h7⟩
  · simp only [LeanVM.Protocol.Whir.Sound.commits_append,
      NoCommit.after_commits (nc_sampleChallenges _) hz,
      NoCommit.after_commits (p := readScalar) nc_readScalar hy,
      NoCommit.after_commits (nc_roundPoly _ _ _) hhy, NoCommit.after_commits (nc_grindPre _) hgp,
      NoCommit.after_commits (NoCommit.bind (nc_powCheck _) fun _ ↦ nc_queryFrag _ _ _ _) hgq,
      NoCommit.after_commits (nc_roundPoly _ _ _) hhq, List.nil_append]
  · simp only [List.filterMap_append, filterMap_sample_map,
      MovesOnly.after_samples (p := readScalar) (fun _ ↦ trivial) hy,
      MovesOnly.after_samples (movesOnly_roundPoly _) hhy,
      MovesOnly.after_samples (movesOnly_roundPoly _) hhq, List.nil_append, List.append_nil,
      List.length_append, hzl, grindPre_after_samples hg hgp, queryFragG_after_samples hg hgq]

/-- The fold rounds' run: their challenges are the run's samples, no commitment. -/
theorem foldRoundsT_run {n : ℕ} {s : WhirStateT} {l : List Ev} {r : WhirStateT × List E}
    (h : (foldRoundsT n s []).after l = some (.ret r)) :
    commits l = [] ∧ l.filterMap sampleOf = r.2 ∧ r.2.length = n ∧ r.1.folds = s.folds ++ r.2 := by
  obtain ⟨e1, e2, e3, -, -⟩ := foldRoundsT_after n s [] h
  rw [List.nil_append] at e1
  exact ⟨NoCommit.after_commits (nc_foldRoundsT _ _ _) h, e1.symm, by rw [e1]; exact e2, by rw [e3, e1]⟩

/-! ## The run up to the residual -/

section Split

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {x : List UInt8}

/-- **A completed run of M′'s program up to the residual** (`LvmMPCert`'s `mainPrefixProg`): the root `W₀`, the
middle phases, `ρ`, the first round polynomial, level 0's fold rounds (`r0`), level 1's cap `W₁`, `35` challenges,
level 1's fold rounds (`r1`), level 2's cap `W₂`, `26` challenges, level 2's fold rounds (`r2`), the residual. -/
theorem mainPrefix_split {h₁ : List Ev} {cl : List LeanVM.Protocol.Verifier.StackClaim}
    {a : E × ((WhirStateT × List E) × List E)}
    (hpre : (commitRootUd cfgMain24G >>= fun _ ↦ mid x >>= fun cl ↦
      stackPrefixJ (cfgMain23Jq 1) cl >>= fun a ↦ VerifierProgram.ret (cl, a)).after h₁ = some (.ret (cl, a))) :
    ∃ (W₀ : Compile.Word) (lm : List Ev) (ρ : E) (lq lf0 : List Ev) (r0 : WhirStateT × List E) (ht1 : ℕ) (W₁ : Compile.Word)
      (lm0 lf1 : List Ev) (r1 : WhirStateT × List E) (ht2 : ℕ) (W₂ : Compile.Word) (lm1 lf2 : List Ev)
      (r2 : WhirStateT × List E) (lres : List Ev) (res : List E),
      h₁ = Ev.commit 19 64 W₀ :: (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit ht1 (3 * 2 ^ 4) W₁ ::
        (lm0 ++ (lf1 ++ (Ev.commit ht2 (3 * 2 ^ 4) W₂ :: (lm1 ++ (lf2 ++ lres)))))))))) ∧
      a = (ρ, (r2, res)) ∧ (mid x).after lm = some (.ret cl) ∧
      commits lq = [] ∧ lq.filterMap sampleOf = [] ∧
      commits lf0 = [] ∧ lf0.filterMap sampleOf = r0.2 ∧ r0.2.length = 6 ∧ r0.1.folds = r0.2 ∧
      commits lm0 = [] ∧ (lm0.filterMap sampleOf).length = 35 ∧
      commits lf1 = [] ∧ lf1.filterMap sampleOf = r1.2 ∧ r1.2.length = 4 ∧ r1.1.folds = r0.1.folds ++ r1.2 ∧
      commits lm1 = [] ∧ (lm1.filterMap sampleOf).length = 26 ∧
      commits lf2 = [] ∧ lf2.filterMap sampleOf = r2.2 ∧ r2.2.length = 4 ∧ r2.1.folds = r1.1.folds ++ r2.2 ∧
      commits lres = [] ∧ lres.filterMap sampleOf = [] := by
  obtain ⟨_, hr, l₂, rfl, h1, h2⟩ := after_bind_ret (p := commitRootUd cfgMain24G) hpre
  obtain ⟨W₀, rfl⟩ := readCommitment_after (ht := 19) (w := 64) h1
  obtain ⟨cl', lm, l₃, rfl, h3, h4⟩ := after_bind_ret (p := mid x) h2
  obtain ⟨a', lp, l₄, rfl, h5, h6⟩ := after_bind_ret (p := stackPrefixJ (cfgMain23Jq 1) cl') h4
  obtain ⟨rfl, rfl, rfl⟩ : l₄ = [] ∧ cl' = cl ∧ a' = a := by
    cases l₄ with
    | nil => simp [VerifierProgram.after] at h6; exact ⟨rfl, h6⟩
    | cons e es => cases e <;> simp [VerifierProgram.after] at h6
  unfold stackPrefixJ at h5
  obtain ⟨ρ, l₆, l₇, rfl, h6, h7⟩ := after_bind_ret (p := sampleChallenge) h5
  obtain rfl := sample_after h6
  obtain ⟨quad, lq, l₈, rfl, h8, h9⟩ := after_bind_ret h7
  obtain ⟨b, lw, l₉, rfl, h10, h11⟩ := after_bind_ret h9
  obtain ⟨rfl, rfl⟩ : l₉ = [] ∧ (ρ, b) = a' := by
    cases l₉ with
    | nil => simp [VerifierProgram.after] at h11; exact ⟨rfl, h11⟩
    | cons e es => cases e <;> simp [VerifierProgram.after] at h11
  change (whirPrefixJ 23 8 0 1 14 0 [⟨6, 2, 115⟩, ⟨4, 3, 77⟩, ⟨4, 4, 58⟩] _).after lw = _ at h10
  rw [whirPrefixJ_mid] at h10
  obtain ⟨r0, lf0, l₁₀, rfl, hf0, h12⟩ := after_bind_ret h10
  obtain ⟨W₁, lm0, l₁₁, s1, rfl, hc0, hs0, hfs1, h13⟩ := midTailPJ_split (by decide) h12
  rw [whirPrefixJ_mid] at h13
  obtain ⟨r1, lf1, l₁₂, rfl, hf1, h14⟩ := after_bind_ret h13
  obtain ⟨W₂, lm1, l₁₃, s2, rfl, hc1, hs1, hfs2, h15⟩ := midTailPJ_split (by decide) h14
  rw [whirPrefixJ_one] at h15
  obtain ⟨r2, lf2, l₁₄, rfl, hf2, h16⟩ := after_bind_ret h15
  obtain ⟨res, lres, l₁₅, rfl, hres, h17⟩ := after_bind_ret h16
  obtain ⟨rfl, rfl⟩ : l₁₅ = [] ∧ (r2, res) = b := by
    cases l₁₅ with
    | nil => simp [VerifierProgram.after] at h17; exact ⟨rfl, h17⟩
    | cons e es => cases e <;> simp [VerifierProgram.after] at h17
  obtain ⟨cf0, sf0, lf0l, ff0⟩ := foldRoundsT_run hf0
  obtain ⟨cf1, sf1, lf1l, ff1⟩ := foldRoundsT_run hf1
  obtain ⟨cf2, sf2, lf2l, ff2⟩ := foldRoundsT_run hf2
  have hr0 : r0.1.folds = r0.2 := by rw [ff0]; rfl
  have hl0 : r0.1.folds.length = 6 := by rw [hr0, lf0l]
  have hr1 : r1.1.folds = r0.1.folds ++ r1.2 := by rw [ff1, hfs1]
  have hl1 : r1.1.folds.length = 10 := by rw [hr1, List.length_append, hl0, lf1l]; rfl
  refine ⟨W₀, lm, ρ, lq, lf0, r0, 23 - r0.1.folds.length - 4 + 3, W₁, lm0, lf1, r1,
    23 - r1.1.folds.length - 4 + 4, W₂, lm1, lf2, r2, lres, res, by simp, rfl, h3,
    NoCommit.after_commits (nc_roundPoly _ _ _) h8, MovesOnly.after_samples (movesOnly_roundPoly _) h8,
    cf0, sf0, lf0l, hr0, hc0, ?_, cf1, sf1, lf1l, hr1, hc1, ?_, cf2, sf2, lf2l, by rw [ff2, hfs2],
    NoCommit.after_commits (nc_readScalars _) hres,
    MovesOnly.after_samples (movesOnly_readScalars _) hres⟩
  · rw [hs0, hl0]; rfl
  · rw [hs1, hl1]; rfl

/-- **The luck's readers on a split run** (and any events `T` after it): the words `W₀, W₁, W₂` and the fold
challenges `r0.2, r1.2, r2.2`. -/
theorem readersM_of_split {W₀ W₁ W₂ : Compile.Word} {lm lq lf0 lm0 lf1 lm1 lf2 T : List Ev} {ρ : E}
    {cl : List LeanVM.Protocol.Verifier.StackClaim} {r0 r1 r2 : WhirStateT × List E} {ht1 ht2 w1 w2 : ℕ}
    (hmid : (mid x).after lm = some (.ret cl))
    (hlq : commits lq = []) (hlqs : lq.filterMap sampleOf = [])
    (hf0 : commits lf0 = []) (hf0s : lf0.filterMap sampleOf = r0.2) (hl0 : r0.2.length = 6)
    (hm0 : commits lm0 = []) (hm0s : (lm0.filterMap sampleOf).length = 35)
    (hf1 : commits lf1 = []) (hf1s : lf1.filterMap sampleOf = r1.2) (hl1 : r1.2.length = 4)
    (hm1s : (lm1.filterMap sampleOf).length = 26)
    (hf2s : lf2.filterMap sampleOf = r2.2) (hl2 : r2.2.length = 4) {h : List Ev}
    (hh : h = Ev.commit 19 64 W₀ :: (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit ht1 w1 W₁ ::
        (lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T))))))))))) :
    wdR (rd0M mid x) h = W₀ ∧ chalR (rd0M mid x) 1 LeanVM.Protocol.EndToEnd.laneBits h = r0.2 ∧
      wdR (rd1M mid x) h = W₁ ∧ chalR (rd1M mid x) 35 4 h = r1.2 ∧
      wdR (rd2M mid x) h = W₂ ∧ chalR (rd2M mid x) 26 4 h = r2.2 := by
  have hroot : (commitRootUd cfgMain24G).after [Ev.commit 19 64 W₀] = some (.ret ()) := by
    simp [commitRootUd, cfgMain24G, VerifierProgram.readCommitment, VerifierProgram.after]
  have h0 : rd0M mid x h = some (W₀, Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit ht1 w1 W₁ ::
      (lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T))))))))) := by
    unfold rd0M rootRd afterMidG
    rw [hh, show Ev.commit 19 64 W₀ :: (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit ht1 w1 W₁ ::
      (lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T))))))))))
        = [Ev.commit 19 64 W₀] ++ (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit ht1 w1 W₁ ::
      (lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T)))))))))) from rfl,
      retSplit_of_after _ _ _ hroot]
    dsimp only
    rw [retSplit_of_after _ _ _ hmid]
    rfl
  have h1 : rd1M mid x h = some (W₁, lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T))))) := by
    unfold rd1M nextRd
    rw [h0, Option.bind_some]
    have := splitCommit_of_noCommit (Ev.sample ρ :: (lq ++ lf0)) (by
      simp only [commits, LeanVM.Protocol.Whir.Sound.commits_append, hlq, hf0]; rfl) ht1 w1 W₁
      (lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T)))))
    simpa only [List.cons_append, List.append_assoc] using this
  have h2 : rd2M mid x h = some (W₂, lm1 ++ (lf2 ++ T)) := by
    unfold rd2M nextRd
    rw [h1, Option.bind_some]
    have := splitCommit_of_noCommit (lm0 ++ lf1) (by
      simp only [LeanVM.Protocol.Whir.Sound.commits_append, hm0, hf1]; rfl) ht2 w2 W₂ (lm1 ++ (lf2 ++ T))
    simpa only [List.cons_append, List.append_assoc] using this
  refine ⟨wdR_of_rd h0, ?_, wdR_of_rd h1, ?_, wdR_of_rd h2, ?_⟩
  · unfold chalR
    rw [h0]
    dsimp only
    simp only [List.filterMap_cons, sampleOf, List.filterMap_append, hlqs, hf0s, List.nil_append]
    rw [List.drop_one, List.tail_cons]
    exact List.take_left' hl0
  · unfold chalR
    rw [h1]
    dsimp only
    simp only [List.filterMap_append, hf1s]
    exact take_drop_appendM hm0s hl1
  · unfold chalR
    rw [h2]
    dsimp only
    simp only [List.filterMap_append, hf2s]
    exact take_drop_appendM hm1s hl2

end Split

end Lvm.ASM
