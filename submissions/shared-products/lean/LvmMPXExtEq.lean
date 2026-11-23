-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (iv)): O5c at M′, generic in the middle phases. Adapted from B1's
-- `LvmCertSExq2.ext_eq_gen` (ff8902c2): the replay of an accepted proof's history (now one root, `C_main`'s three
-- levels and two openings, `openMain_P20`), the decoders' inputs from the history (`decode_SMH`), `EXM_node`.
import LvmMPXNodeSem
import LvmCertSExq2Codec
import LvmMPCertSplit
import LvmCertSExq2
import LvmMPCert
import LvmMPXLayout

-- (GOLF2: 12 declarations that `certified` does not use moved verbatim to `LvmXSChildOff`, outside its import closure.)

-- ===== merged from `LvmMPXExtSplit` (GOLF module merge: `LvmMPXExtSplit.lean` is now a stub importing `LvmMPXExtEq`) =====
section
-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (iv)): M′'s history up to `C_main`'s residual, event kind by
-- event kind, with the program at the two openings. Refines `LvmMPCertSplit.mainPrefix_split` (R11-C) the way
-- `LvmCertSExq2.ext_eq_gen` (B1, ff8902c2) split `C_rec`'s level step inline.

/-!
# M′'s history, kind by kind

* **`midTailPJ_splitK`**: a level step with a next level (`g ≠ 0`): the next cap, then `pre` (the OOD point,
  its answer and intro, the proof of work, the positions, `λ`), the opening `query w`, `post` (the query intro),
  then the next levels; the program after the cap and `pre` is at the opening of `cidx c₀ n₀ i`.
* **`mainPrefix_splitK`**: a completed run of `mainPrefixProg` is the root `W₀`, the middle phases `lm`, `ρ`, the
  intro `lq`, level 0's fold rounds `lf0`, level 1's cap `W₁`, `pre0`, `query w0`, `post0`, level 1's fold rounds
  `lf1`, level 2's cap `W₂`, `pre1`, `query w1`, `post1`, level 2's fold rounds `lf2`, the residual `lres`; with
  each piece's kinds and the program `PSWithM mid x` at the two openings (115 and 77 positions).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir

/-- The kinds of a level step's `pre`: `z` OOD samples, the answer, the intro (2), the proof of work (separator,
nonce, PoW challenge), `np` position samples, `λ`. -/
def preKinds (z np : ℕ) : List EvK :=
  List.replicate z .sample ++ [.read, .read, .read, .sample, .read, .sample] ++ List.replicate np .sample ++ [.sample]

theorem kinds_all_sample {l : List Ev} (h : ∀ e ∈ l, kindOf e = .sample) :
    l.map kindOf = List.replicate l.length .sample :=
  List.eq_replicate_iff.2 ⟨by simp, fun b hb => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb; exact h e he⟩

/-- **A level step with a next level**, kind by kind. -/
theorem midTailPJ_splitK {μ per c₀ n₀ g i : ℕ} {level next : Whir.Level} {rest : List Whir.Level}
    {r : WhirStateT × List E} {l : List Ev} {b : (WhirStateT × List E) × List E} (hg : g ≠ 0)
    (h : (midTailPJ μ per c₀ n₀ g i level next rest r).after l = some (.ret b)) :
    ∃ (W : Compile.Word) (pre : List Ev) (w : List (List K)) (post l' : List Ev) (qs : List ℕ)
      (k : List (List K) → VerifierProgram ((WhirStateT × List E) × List E)) (s' : WhirStateT),
      l = Ev.commit (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold) W ::
        (pre ++ (Ev.query w :: (post ++ l'))) ∧
      pre.map kindOf = preKinds (μ - r.1.folds.length) (posCount per level.queries level.queries) ∧
      qs.length = posLen per level.queries level.queries ∧
      (midTailPJ μ per c₀ n₀ g i level next rest r).after
        (Ev.commit (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold) W :: pre) =
          some (.query (cidx c₀ n₀ i) qs k) ∧
      post.map kindOf = [.read, .read] ∧
      s'.folds = r.1.folds ∧ (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s').after l' = some (.ret b) ∧
      (∀ (l'' : List Ev) (p' : VerifierProgram ((WhirStateT × List E) × List E)),
        (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s').after l'' = some p' →
        (midTailPJ μ per c₀ n₀ g i level next rest r).after
          (Ev.commit (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold) W ::
            (pre ++ (Ev.query w :: (post ++ l'')))) = some p') := by
  have h0 := h
  unfold midTailPJ at h
  obtain ⟨_, lc, l₁, rfl, hc, h1⟩ := after_bind_ret h
  obtain ⟨W, rfl⟩ := readCommitment_after hc
  obtain ⟨z, lz, l₂, rfl, hz, h2⟩ := after_bind_ret h1
  obtain ⟨y, ly, l₃, rfl, hy, h3⟩ := after_bind_ret h2
  obtain ⟨hy', lhy, l₄, rfl, hhy, h4⟩ := after_bind_ret h3
  obtain ⟨_, lgp, l₅, rfl, hgp, h5⟩ := after_bind_ret h4
  obtain ⟨_, lpw, l₆, rfl, hpw, h6⟩ := after_bind_ret h5
  obtain ⟨qs, lps, l₇, rfl, hps, h7⟩ := after_bind_ret h6
  obtain ⟨lam, llam, l₈, rfl, hlam, h8⟩ := after_bind_ret h7
  obtain ⟨w, lw, l₉, rfl, hw, h9⟩ := after_bind_ret h8
  unfold midFinishPJ at h9
  obtain ⟨hq, lhq, l₁₀, rfl, hhq, h10⟩ := after_bind_ret h9
  obtain ⟨rfl, hzl⟩ := sampleChallenges_after _ hz
  obtain rfl := read_after hy
  obtain ⟨c₁, y₁, rfl⟩ := grindPre_after hg hgp
  obtain ⟨c₂, rfl⟩ := powCheck_after hg hpw
  obtain rfl := sample_after hlam
  obtain rfl := queryOpenings_after hw
  obtain ⟨hpk, hql⟩ := samplePositionsAux_kinds per _ _ _ hps
  have hpn := samplePositionsAux_after per _ _ _ hps
  have hpl : lps.length = posCount per level.queries level.queries := by
    rw [← hpn, samples_length, kinds_all_sample hpk, List.count_replicate_self]
  refine ⟨W, z.map Ev.sample ++ ([Ev.read y] ++ (lhy ++ ([Ev.sample c₁, Ev.read y₁] ++ ([Ev.sample c₂] ++
    (lps ++ [Ev.sample lam]))))), w, lhq, l₁₀, qs,
    fun words ↦ midFinishPJ μ per c₀ n₀ g i next rest r z y hy' qs lam words,
    glueMid μ i r z y hy' qs lam w hq, ?_, ?_, hql, ?_, roundPoly_kinds hhq,
    glueMid_folds _ _ _ _ _ _ _ _, h10, fun l'' p' hl'' => ?_⟩
  · simp only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append]
  · simp only [preKinds, List.map_append, List.map_map, roundPoly_kinds hhy, kinds_all_sample hpk, hpl]
    rw [show (kindOf ∘ Ev.sample) = fun _ => EvK.sample from rfl, List.map_const', hzl]
    simp [kindOf]
  · unfold midTailPJ
    have e : Ev.commit (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold) W ::
        (z.map Ev.sample ++ ([Ev.read y] ++ (lhy ++ ([Ev.sample c₁, Ev.read y₁] ++ ([Ev.sample c₂] ++
          (lps ++ [Ev.sample lam])))))) =
        [Ev.commit (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold) W] ++
        (z.map Ev.sample ++ ([Ev.read y] ++ (lhy ++ ([Ev.sample c₁, Ev.read y₁] ++ ([Ev.sample c₂] ++
          (lps ++ [Ev.sample lam])))))) := rfl
    rw [e, after_bind_append _ hc, after_bind_append _ hz, after_bind_append _ hy, after_bind_append _ hhy,
      after_bind_append _ hgp, after_bind_append _ hpw, after_bind_append _ hps]
    rfl
  · unfold midTailPJ
    have e : Ev.commit (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold) W ::
        (z.map Ev.sample ++ ([Ev.read y] ++ (lhy ++ ([Ev.sample c₁, Ev.read y₁] ++ ([Ev.sample c₂] ++
          (lps ++ [Ev.sample lam]))))) ++ (Ev.query w :: (lhq ++ l''))) =
        [Ev.commit (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold) W] ++
        (z.map Ev.sample ++ ([Ev.read y] ++ (lhy ++ ([Ev.sample c₁, Ev.read y₁] ++ ([Ev.sample c₂] ++
          (lps ++ ([Ev.sample lam] ++ ([Ev.query w] ++ (lhq ++ l''))))))))) := by simp
    rw [e, after_bind_append _ hc, after_bind_append _ hz, after_bind_append _ hy, after_bind_append _ hhy,
      after_bind_append _ hgp, after_bind_append _ hpw, after_bind_append _ hps, after_bind_append _ hlam,
      after_bind_append _ hw]
    unfold midFinishPJ
    rw [after_bind_append _ hhq]
    exact hl''

/-! ## The program -/

theorem levels_main23Jq_ne : (cfgMain23Jq 1).levels ≠ [] := List.cons_ne_nil _ _

/-- **`P_S` at M′ is the run up to `C_main`'s residual, then `C_main`'s suffix and `true`.** -/
theorem PSWithM_eq_prefix (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (x : List UInt8) :
    PSWithM mid x = (mainPrefixProg mid x).bind fun ca ↦
      (stackSuffixJ (cfgMain23Jq 1) ca.1 levels_main23Jq_ne ca.2).bind fun _ ↦ .ret true := by
  unfold PSWithM mainPrefixProg
  simp only [verifyStackedJ_eq_prefix (cfgMain23Jq 1) rfl levels_main23Jq_ne, bind_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rfl

/-- `posLen` at the two opened levels. -/
theorem posLen_main : posLen 8 115 115 = 115 ∧ posLen 8 77 77 = 77 ∧ posCount 8 115 115 = 15 ∧
    posCount 8 77 77 = 10 := by decide

section Split

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {x : List UInt8}

/-- **A completed run of M′'s program up to the residual, kind by kind** (`mainPrefix_split`, refined): the root
`W₀`, the middle phases, `ρ`, the intro, level 0's six fold rounds, level 1's cap `W₁`, `pre0` (`17` OOD samples …
`15` position samples, `λ`), the opening `w0` of `115` positions of commitment `0`, its intro `post0`, level 1's
four fold rounds, level 2's cap `W₂`, `pre1` (`13` OOD samples … `10` position samples, `λ`), the opening `w1` of
`77` positions of commitment `1`, its intro `post1`, level 2's four fold rounds, the residual `lres`. -/
theorem mainPrefix_splitK {h₁ : List Ev} {cl : List LeanVM.Protocol.Verifier.StackClaim} {a : E × ((WhirStateT × List E) × List E)}
    (hpre : (mainPrefixProg mid x).after h₁ = some (.ret (cl, a))) :
    ∃ (W₀ : Compile.Word) (lm : List Ev) (ρ : E) (lq lf0 : List Ev) (r0 : WhirStateT × List E)
      (W₁ : Compile.Word) (pre0 : List Ev) (w0 : List (List K)) (post0 lf1 : List Ev) (r1 : WhirStateT × List E)
      (W₂ : Compile.Word) (pre1 : List Ev) (w1 : List (List K)) (post1 lf2 : List Ev) (r2 : WhirStateT × List E)
      (lres : List Ev) (res : List E) (qs0 qs1 : List ℕ)
      (k0 k1 : List (List K) → VerifierProgram Bool),
      h₁ = Ev.commit 19 64 W₀ :: (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ ::
        (pre0 ++ (Ev.query w0 :: (post0 ++ (lf1 ++ (Ev.commit 13 (3 * 2 ^ 4) W₂ ::
          (pre1 ++ (Ev.query w1 :: (post1 ++ (lf2 ++ lres)))))))))))))) ∧
      a = (ρ, (r2, res)) ∧ (mid x).after lm = some (.ret cl) ∧
      lq.map kindOf = [.read, .read] ∧
      lf0.map kindOf = (List.replicate 6 [EvK.sample, .read, .read]).flatten ∧ lf0.filterMap sampleOf = r0.2 ∧
      r0.2.length = 6 ∧ r0.1.folds = r0.2 ∧
      pre0.map kindOf = preKinds 17 15 ∧ post0.map kindOf = [.read, .read] ∧
      lf1.map kindOf = (List.replicate 4 [EvK.sample, .read, .read]).flatten ∧ lf1.filterMap sampleOf = r1.2 ∧
      r1.2.length = 4 ∧ r1.1.folds = r0.1.folds ++ r1.2 ∧
      pre1.map kindOf = preKinds 13 10 ∧ post1.map kindOf = [.read, .read] ∧
      lf2.map kindOf = (List.replicate 4 [EvK.sample, .read, .read]).flatten ∧ lf2.filterMap sampleOf = r2.2 ∧
      r2.2.length = 4 ∧ r2.1.folds = r1.1.folds ++ r2.2 ∧
      lres = res.map Ev.read ∧ res.length = 2 ^ 9 ∧
      qs0.length = 115 ∧ (PSWithM mid x).after (Ev.commit 19 64 W₀ :: (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++
        (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0)))))) = some (.query 0 qs0 k0) ∧
      qs1.length = 77 ∧ (PSWithM mid x).after (Ev.commit 19 64 W₀ :: (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++
        (Ev.commit 16 (3 * 2 ^ 4) W₁ :: (pre0 ++ (Ev.query w0 :: (post0 ++ (lf1 ++
          (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1))))))))))) = some (.query 1 qs1 k1) := by
  replace hpre : (commitRootUd cfgMain24G >>= fun _ ↦ mid x >>= fun cl ↦
      stackPrefixJ (cfgMain23Jq 1) cl >>= fun a ↦ VerifierProgram.ret (cl, a)).after h₁ = some (.ret (cl, a)) := hpre
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
  obtain ⟨W₁, pre0, w0, post0, l₁₁, qs0, k0', s1, rfl, hk0, hq0l, hq0, hp0, hfs1, h13, hc0⟩ :=
    midTailPJ_splitK (by decide) h12
  rw [whirPrefixJ_mid] at h13
  obtain ⟨r1, lf1, l₁₂, rfl, hf1, h14⟩ := after_bind_ret h13
  obtain ⟨W₂, pre1, w1, post1, l₁₃, qs1, k1', s2, rfl, hk1, hq1l, hq1, hp1, hfs2, h15, -⟩ :=
    midTailPJ_splitK (by decide) h14
  rw [whirPrefixJ_one] at h15
  obtain ⟨r2, lf2, l₁₄, rfl, hf2, h16⟩ := after_bind_ret h15
  obtain ⟨res, lres, l₁₅, rfl, hres, h17⟩ := after_bind_ret h16
  obtain ⟨rfl, rfl⟩ : l₁₅ = [] ∧ (r2, res) = b := by
    cases l₁₅ with
    | nil => simp [VerifierProgram.after] at h17; exact ⟨rfl, h17⟩
    | cons e es => cases e <;> simp [VerifierProgram.after] at h17
  obtain ⟨-, sf0, lf0l, ff0⟩ := foldRoundsT_run hf0
  obtain ⟨-, sf1, lf1l, ff1⟩ := foldRoundsT_run hf1
  obtain ⟨-, sf2, lf2l, ff2⟩ := foldRoundsT_run hf2
  have hr0 : r0.1.folds = r0.2 := by rw [ff0]; rfl
  have hl0 : r0.1.folds.length = 6 := by rw [hr0, lf0l]
  have hr1 : r1.1.folds = r0.1.folds ++ r1.2 := by rw [ff1, hfs1]
  have hl1 : r1.1.folds.length = 10 := by rw [hr1, List.length_append, hl0, lf1l]; rfl
  rw [hl0] at hk0 hq0 hc0
  rw [hl1] at hk1 hq1
  -- the program at the two openings
  have hroot : (commitRootUd cfgMain24G).after [Ev.commit 19 64 W₀] = some (.ret ()) := h1
  have hPS : ∀ (l : List Ev) (i : ℕ) (qs : List ℕ) (k : List (List K) → VerifierProgram ((WhirStateT × List E) × List E)),
      (whirPrefixJ 23 8 0 1 14 0 [⟨6, 2, 115⟩, ⟨4, 3, 77⟩, ⟨4, 4, 58⟩]
        ⟨Verifier.dot (Verifier.powers ρ cl'.length) (List.map (fun x => x.2) cl'), quad, [], []⟩).after l =
          some (.query i qs k) →
      ∃ K, (PSWithM mid x).after (Ev.commit 19 64 W₀ :: (lm ++ (Ev.sample ρ :: (lq ++ l)))) =
        some (.query i qs K) := fun l i qs k hl => by
    rw [PSWithM_eq_prefix]
    refine atQuery_bind _ ?_
    unfold mainPrefixProg
    simp only [bind_eq]
    refine atQuery_append (l₁ := [Ev.commit 19 64 W₀]) hroot (atQuery_append (l₁ := lm) h3 (atQuery_bind _ ?_))
    unfold stackPrefixJ
    exact atQuery_append (l₁ := [Ev.sample ρ]) (rfl : sampleChallenge.after [Ev.sample ρ] = some (.ret ρ))
      (atQuery_append (l₁ := lq) h8 (atQuery_bind _ ⟨k, hl⟩))
  obtain ⟨K0, hK0⟩ := hPS (lf0 ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: pre0)) 0 qs0 k0' (by
    rw [whirPrefixJ_mid, after_bind_append _ hf0]; exact hq0)
  obtain ⟨K1, hK1⟩ := hPS (lf0 ++ (Ev.commit 16 (3 * 2 ^ 4) W₁ :: (pre0 ++ (Ev.query w0 :: (post0 ++ (lf1 ++
      (Ev.commit 13 (3 * 2 ^ 4) W₂ :: pre1))))))) 1 qs1 k1' (by
    rw [whirPrefixJ_mid, after_bind_append _ hf0]
    refine hc0 _ _ ?_
    rw [whirPrefixJ_mid, after_bind_append _ hf1]; exact hq1)
  refine ⟨W₀, lm, ρ, lq, lf0, r0, W₁, pre0, w0, post0, lf1, r1, W₂, pre1, w1, post1, lf2, r2, lres, res, qs0, qs1,
    K0, K1, by simp [hl0, hl1], rfl, h3, roundPoly_kinds h8, foldRoundsT_kinds 6 _ _ hf0, sf0, lf0l, hr0, ?_, hp0,
    foldRoundsT_kinds 4 _ _ hf1, sf1, lf1l, hr1, ?_, hp1, foldRoundsT_kinds 4 _ _ hf2, sf2, lf2l,
    by rw [ff2, hfs2], readScalars_after_eq _ hres, ?_, by rw [hq0l]; exact posLen_main.1, ?_,
    by rw [hq1l]; exact posLen_main.2.1, ?_⟩
  · rw [hk0]; show preKinds (23 - 6) (posCount 8 115 115) = _; rw [posLen_main.2.2.1]
  · rw [hk1]; show preKinds (23 - 10) (posCount 8 77 77) = _; rw [posLen_main.2.2.2]
  · rw [readScalars_after_len _ hres, ff2, hfs2, List.length_append, hl1, lf2l]; rfl
  · simpa only [List.cons_append, List.append_assoc] using hK0
  · simpa only [List.cons_append, List.append_assoc] using hK1

end Split

end Lvm.ASM
end
-- ===== end of `LvmMPXExtSplit` =====

-- ===== merged from `LvmMPXExtRun` (GOLF module merge: `LvmMPXExtRun.lean` is now a stub importing `LvmMPXExtEq`) =====
section
-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (iv)): the schedule's view of `C_main`'s opening at `P20`, as
-- B1's `openRec_P20` (ff8902c2, `LvmCertSExq2Run`) was for `C_rec`'s: the replay's slices, offsets and kinds.

/-!
# `openMain_P20`: the replay of M′'s history up to the residual

The history (`mainPrefix_splitK`) is replayed (`trun_simK2`, `trun_query`) in five segments of reads, samples and
commitments, cut at the two openings:

* `A1` (`midItems ++ mainHeadA1`): the middle phases, `ρ`, the intro, level 0's six fold rounds, from π byte `14176`
  (the root's cap pending from `5984`);
* `A2` (`mainHeadA2`): level 1's cap (at `capOffM 1 = 190288`), `pre0`; then level 0's opening (`115` positions of
  `728` bytes);
* `B1` (`mainHeadB1`): the opening's intro, level 1's four fold rounds;
* `A3` (`mainHeadA3`): level 2's cap (at `capOffM 2 = 278440`), `pre1`; then level 1's opening (`77` positions of
  `672` bytes);
* `B2` (`mainHeadB2`): the opening's intro, level 2's four fold rounds, up to the residual at `resOffM = 334616`.

**`openMain_P20`** (by evaluation): the slices `fsPreK2` the segments' samples absorb are the chain's messages
`fsMsgs` of positions `2–1214`, `1215–1249`, `1250–1253`, `1254–1279`, `1280–1283`; the offsets; the kinds.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters

/-- `C_main`'s commitment shapes `(ht, w)` at M′ (level 1: `2^16` rows of `3 · 2^4` words, level 2: `2^13`). -/
def shMain : Ref → ℕ × ℕ
  | ⟨.main, 1⟩ => (16, 48)
  | ⟨.main, 2⟩ => (13, 48)
  | _ => (19, 64)

/-- The schedule's `openMain` phase at `P20`. -/
def mainOpenI : List Item := ((phases P20).getD 7 default).2

/-- `ρ`, the intro round, level 0's six fold rounds. -/
def mainHeadA1 : List Item := mainOpenI.take 14
/-- Level 1's cap, the OOD point, its answer and intro, level 0's proof of work, positions and `λ`. -/
def mainHeadA2 : List Item := (mainOpenI.drop 14).take 25
/-- After level 0's opening: its intro, level 1's four fold rounds. -/
def mainHeadB1 : List Item := (mainOpenI.drop 40).take 9
/-- Level 2's cap, the OOD point, its answer and intro, level 1's proof of work, positions and `λ`. -/
def mainHeadA3 : List Item := (mainOpenI.drop 49).take 21
/-- After level 1's opening: its intro, level 2's four fold rounds. -/
def mainHeadB2 : List Item := (mainOpenI.drop 71).take 9

/-- The kinds of a level's intro and `n` fold rounds. -/
def foldKinds (n : ℕ) : List EvK := [.read, .read] ++ (List.replicate n [EvK.sample, .read, .read]).flatten

/-! ## Item-level forms of the kinds' walks (proof help for `openMain_P20`, GOLF-DEC2) -/

/-- The π offset after items of reads and samples (`offK2 ∘ itemK2`, one step per item). -/
private def offI : List Item → ℕ → ℕ
  | [], off => off
  | .read m :: its, off => offI its (off + 24 * m)
  | .sample :: its, off => offI its off
  | .readW _ _ :: its, off => offI its off
  | .cap _ _ :: its, off => offI its off
  | .positions _ :: its, off => offI its off
  | .opening _ :: its, off => offI its off

/-- The first pending byte after items of reads and samples (`pendK2 ∘ itemK2`). -/
private def pendI : List Item → ℕ → ℕ → ℕ
  | [], _, pend => pend
  | .read m :: its, off, pend => pendI its (off + 24 * m) pend
  | .sample :: its, off, _ => pendI its off off
  | .readW _ _ :: its, off, pend => pendI its off pend
  | .cap _ _ :: its, off, pend => pendI its off pend
  | .positions _ :: its, off, pend => pendI its off pend
  | .opening _ :: its, off, pend => pendI its off pend

private theorem fsPreK2_reads (ks : List K2) : ∀ (m off pend : ℕ),
    fsPreK2 (List.replicate m .read ++ ks) off pend = fsPreK2 ks (off + 24 * m) pend
  | 0, off, pend => rfl
  | m + 1, off, pend => by
    rw [List.replicate_succ, List.cons_append, fsPreK2, fsPreK2_reads ks m]
    congr 1
    ring

private theorem offK2_reads (ks : List K2) : ∀ (m off : ℕ),
    offK2 (List.replicate m .read ++ ks) off = offK2 ks (off + 24 * m)
  | 0, off => rfl
  | m + 1, off => by
    rw [List.replicate_succ, List.cons_append, offK2, offK2_reads ks m]
    congr 1
    ring

private theorem pendK2_reads (ks : List K2) : ∀ (m off pend : ℕ),
    pendK2 (List.replicate m .read ++ ks) off pend = pendK2 ks (off + 24 * m) pend
  | 0, off, pend => rfl
  | m + 1, off, pend => by
    rw [List.replicate_succ, List.cons_append, pendK2, pendK2_reads ks m]
    congr 1
    ring

private theorem fsPreK2_items (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (its : List Item) (off pend : ℕ), RSItems its = true →
    fsPreK2 (itemK2 p sh its) off pend = Lvm.X.fsPre p its off pend
  | [], _, _, _ => rfl
  | .read m :: its, off, pend, h => by
    rw [itemK2, fsPreK2_reads, fsPreK2_items p sh its _ _ h, Lvm.X.fsPre]
    rfl
  | .sample :: its, off, pend, h => by
    rw [itemK2, fsPreK2, fsPreK2_items p sh its _ _ h, Lvm.X.fsPre]
  | .readW _ _ :: _, _, _, h => by simp [RSItems] at h
  | .cap _ _ :: _, _, _, h => by simp [RSItems] at h
  | .positions _ :: _, _, _, h => by simp [RSItems] at h
  | .opening _ :: _, _, _, h => by simp [RSItems] at h

private theorem offK2_items (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (its : List Item) (off : ℕ), RSItems its = true →
    offK2 (itemK2 p sh its) off = offI its off
  | [], _, _ => rfl
  | .read m :: its, off, h => by
    rw [itemK2, offK2_reads, offK2_items p sh its _ h, offI]
  | .sample :: its, off, h => by
    rw [itemK2, offK2, offK2_items p sh its _ h, offI]
  | .readW _ _ :: _, _, h => by simp [RSItems] at h
  | .cap _ _ :: _, _, h => by simp [RSItems] at h
  | .positions _ :: _, _, h => by simp [RSItems] at h
  | .opening _ :: _, _, h => by simp [RSItems] at h

private theorem pendK2_items (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (its : List Item) (off pend : ℕ), RSItems its = true →
    pendK2 (itemK2 p sh its) off pend = pendI its off pend
  | [], _, _, _ => rfl
  | .read m :: its, off, pend, h => by
    rw [itemK2, pendK2_reads, pendK2_items p sh its _ _ h, pendI]
  | .sample :: its, off, pend, h => by
    rw [itemK2, pendK2, pendK2_items p sh its _ _ h, pendI]
  | .readW _ _ :: _, _, _, h => by simp [RSItems] at h
  | .cap _ _ :: _, _, _, h => by simp [RSItems] at h
  | .positions _ :: _, _, _, h => by simp [RSItems] at h
  | .opening _ :: _, _, _, h => by simp [RSItems] at h

/-- The samples among items of reads and samples (`(itemKinds its).count .sample`). -/
private def sampI : List Item → ℕ
  | [] => 0
  | .read _ :: its => sampI its
  | .sample :: its => sampI its + 1
  | .readW _ _ :: its => sampI its
  | .cap _ _ :: its => sampI its
  | .positions _ :: its => sampI its
  | .opening _ :: its => sampI its

private theorem count_itemKinds : ∀ (its : List Item), RSItems its = true → (itemKinds its).count .sample = sampI its
  | [], _ => rfl
  | .read m :: its, h => by
    rw [itemKinds, List.count_append, count_itemKinds its h, sampI, List.count_replicate]
    simp
  | .sample :: its, h => by
    rw [itemKinds, List.count_cons, count_itemKinds its h, sampI]
    simp
  | .readW _ _ :: _, h => by simp [RSItems] at h
  | .cap _ _ :: _, h => by simp [RSItems] at h
  | .positions _ :: _, h => by simp [RSItems] at h
  | .opening _ :: _, h => by simp [RSItems] at h

private theorem rs_left : ∀ (a b : List Item), RSItems (a ++ b) = true → RSItems a = true
  | [], _, _ => rfl
  | .read _ :: a, b, h => by rw [List.cons_append, RSItems] at h; rw [RSItems]; exact rs_left a b h
  | .sample :: a, b, h => by rw [List.cons_append, RSItems] at h; rw [RSItems]; exact rs_left a b h
  | .readW _ _ :: _, _, h => by simp [RSItems] at h
  | .cap _ _ :: _, _, h => by simp [RSItems] at h
  | .positions _ :: _, _, h => by simp [RSItems] at h
  | .opening _ :: _, _, h => by simp [RSItems] at h

/-- **`openMain_P20`**: the replay's slices, offsets and kinds at `P20` (by evaluation). -/
theorem openMain_P20 :
    fsPreK2 (itemK2 P20 shMain (midItems ++ mainHeadA1)) 14176 5984 = ((Lvm.X.fsMsgs P20).drop 1).take 1213 ∧
    offK2 (itemK2 P20 shMain (midItems ++ mainHeadA1)) 14176 = 190288 ∧
    pendK2 (itemK2 P20 shMain (midItems ++ mainHeadA1)) 14176 5984 = 190240 ∧
    fsPreK2 (itemK2 P20 shMain mainHeadA2) 190288 190240 = ((Lvm.X.fsMsgs P20).drop 1214).take 35 ∧
    offK2 (itemK2 P20 shMain mainHeadA2) 190288 = 194480 ∧
    pendK2 (itemK2 P20 shMain mainHeadA2) 190288 190240 = 194480 ∧
    fsPreK2 (itemK2 P20 shMain mainHeadB1) 278200 278200 = ((Lvm.X.fsMsgs P20).drop 1249).take 4 ∧
    offK2 (itemK2 P20 shMain mainHeadB1) 278200 = 278440 ∧
    pendK2 (itemK2 P20 shMain mainHeadB1) 278200 278200 = 278392 ∧
    fsPreK2 (itemK2 P20 shMain mainHeadA3) 278440 278392 = ((Lvm.X.fsMsgs P20).drop 1253).take 26 ∧
    offK2 (itemK2 P20 shMain mainHeadA3) 278440 = 282632 ∧
    pendK2 (itemK2 P20 shMain mainHeadA3) 278440 278392 = 282632 ∧
    fsPreK2 (itemK2 P20 shMain mainHeadB2) 334376 334376 = ((Lvm.X.fsMsgs P20).drop 1279).take 4 ∧
    offK2 (itemK2 P20 shMain mainHeadB2) 334376 = 334616 ∧
    pendK2 (itemK2 P20 shMain mainHeadB2) 334376 334376 = 334568 ∧
    (itemKinds midItems).count .sample = 1206 ∧ RSItems midItems = true ∧
    itemK2 P20 shMain mainHeadA1 = ([EvK.sample] ++ foldKinds 6).map toK2 ∧
    itemK2 P20 shMain mainHeadA2 = .commit 16 48 4096 :: (preKinds 17 15).map toK2 ∧
    itemK2 P20 shMain mainHeadB1 = (foldKinds 4).map toK2 ∧
    itemK2 P20 shMain mainHeadA3 = .commit 13 48 4096 :: (preKinds 13 10).map toK2 ∧
    itemK2 P20 shMain mainHeadB2 = (foldKinds 4).map toK2 ∧
    Lvm.X.capOffM P20 1 = 190288 ∧ Lvm.X.capOffM P20 2 = 278440 ∧ Lvm.X.resOffM P20 = 334616 := by
  obtain ⟨-, -, -, -, -, -, c1, c2, r, -⟩ := Lvm.X.layoutM_P20
  rw [c1, c2, r]
  -- the middle phases item by item (`fsPre`, `offI`, `pendI`, `sampI`), not as the ~7,000 kinds `itemK2` expands
  -- their reads to; one kernel evaluation for all (GOLF-DEC2)
  suffices h : RSItems (midItems ++ mainHeadA1) = true ∧
      Lvm.X.fsPre P20 (midItems ++ mainHeadA1) 14176 5984 = ((Lvm.X.fsMsgs P20).drop 1).take 1213 ∧
      offI (midItems ++ mainHeadA1) 14176 = 190288 ∧
      pendI (midItems ++ mainHeadA1) 14176 5984 = 190240 ∧
      fsPreK2 (itemK2 P20 shMain mainHeadA2) 190288 190240 = ((Lvm.X.fsMsgs P20).drop 1214).take 35 ∧
      offK2 (itemK2 P20 shMain mainHeadA2) 190288 = 194480 ∧
      pendK2 (itemK2 P20 shMain mainHeadA2) 190288 190240 = 194480 ∧
      fsPreK2 (itemK2 P20 shMain mainHeadB1) 278200 278200 = ((Lvm.X.fsMsgs P20).drop 1249).take 4 ∧
      offK2 (itemK2 P20 shMain mainHeadB1) 278200 = 278440 ∧
      pendK2 (itemK2 P20 shMain mainHeadB1) 278200 278200 = 278392 ∧
      fsPreK2 (itemK2 P20 shMain mainHeadA3) 278440 278392 = ((Lvm.X.fsMsgs P20).drop 1253).take 26 ∧
      offK2 (itemK2 P20 shMain mainHeadA3) 278440 = 282632 ∧
      pendK2 (itemK2 P20 shMain mainHeadA3) 278440 278392 = 282632 ∧
      fsPreK2 (itemK2 P20 shMain mainHeadB2) 334376 334376 = ((Lvm.X.fsMsgs P20).drop 1279).take 4 ∧
      offK2 (itemK2 P20 shMain mainHeadB2) 334376 = 334616 ∧
      pendK2 (itemK2 P20 shMain mainHeadB2) 334376 334376 = 334568 ∧
      sampI midItems = 1206 ∧
      itemK2 P20 shMain mainHeadA1 = ([EvK.sample] ++ foldKinds 6).map toK2 ∧
      itemK2 P20 shMain mainHeadA2 = .commit 16 48 4096 :: (preKinds 17 15).map toK2 ∧
      itemK2 P20 shMain mainHeadB1 = (foldKinds 4).map toK2 ∧
      itemK2 P20 shMain mainHeadA3 = .commit 13 48 4096 :: (preKinds 13 10).map toK2 ∧
      itemK2 P20 shMain mainHeadB2 = (foldKinds 4).map toK2 by
    obtain ⟨hrs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      h21⟩ := h
    have hm := rs_left _ _ hrs
    rw [fsPreK2_items _ _ _ _ _ hrs, offK2_items _ _ _ _ hrs, pendK2_items _ _ _ _ _ hrs,
      count_itemKinds _ hm]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hm, h17, h18, h19, h20, h21,
      rfl, rfl, rfl⟩
  decide +kernel

end Lvm.ASM
end
-- ===== end of `LvmMPXExtRun` =====

/-!
# O5c at M′: `EXM = S.Ex K.ext` on good logs

**`ext_eqM_gen`**: for `mid` with `MidSpecM`, `MidShapeM`, `MidFollows`, `NodeSoundM` with a `child` that reads the
stream block of the decoded window as `wStreamM` does (`hchild`), on an accepted `'S'` proof over a log with
`μ K L < 1`, `EXM (accV VS) = S.Ex K.ext` or `EXM` returns a witness of the relation (an `S` node outside the
extractor's domain: the search).

In the domain, `EXM_node`'s inputs are the replayed history's: the chain answers at `foldPosK k` are the history's
fold samples (`simK2_chain` on the five segments of `openMain_P20`); `C_main`'s three words under π's caps
(`readRowG … (capM π i)`) are the history's committed words (`readRowG_eq_wordOf`, `capI_capM0`, `capI_capM1`, `capI_capM2`); `resEM π` is the
replayed residual; the decoders succeed there (`decode_SMH`, from `psInvM`'s post `ExtIM` and no luck at the end).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

/-! ## π's values -/

/-- **O12 at M′**: the generic reading `readRowG` is WP-5's word under the cap, for a scheme whose word decoder is
`kOfBytes` and whose leaves of shape `(ht, z + occ)` carry `occ` words. -/
theorem readRowG_eq_wordOf (S : Scheme) (hK : S.decK = kOfBytes) {ht lv z occ : ℕ} (hO : S.occ ht (z + occ) = occ)
    (L : Log) (cap : List RecursionFast.Digest) (p : ℕ) :
    Lvm.X.readRowG ht lv z occ L cap p = S.wordOf L ⟨ht, z + occ, lv, cap⟩ p := by
  have hl : Lvm.X.xLeafBytesG ht lv L cap p = Scheme.leafBytes L ⟨ht, z + occ, lv, cap⟩ p := by
    simp only [Lvm.X.xLeafBytesG, Scheme.leafBytes, xDescend_eq]
    rfl
  rw [Lvm.X.readRowG, Scheme.wordOf, Scheme.padRow, hl, hK]
  show _ = padRowOf kOfBytes (z + occ) (S.occ ht (z + occ)) _
  rw [hO, padRowOf, Nat.min_eq_left (Nat.le_add_left _ _), Nat.add_sub_cancel]
  simp only [Lvm.X.xRowOf, rowOf, kOfBytes_eq, List.take_take, Nat.min_self]

/-! ## The history's commitments -/

theorem commits_nil_of_kinds : ∀ (l : List Ev), EvK.other ∉ l.map kindOf → commits l = []
  | [], _ => rfl
  | e :: l, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    cases e with
    | read _ => exact commits_nil_of_kinds l h.2
    | sample _ => exact commits_nil_of_kinds l h.2
    | commit _ _ _ => exact absurd rfl h.1
    | query _ => exact absurd rfl h.1
    | grind _ => exact absurd rfl h.1

theorem commits_nil_of_kindsEq {l : List Ev} {ks : List EvK} (h : l.map kindOf = ks) (ho : EvK.other ∉ ks) :
    commits l = [] := commits_nil_of_kinds l (h ▸ ho)

/-! ## The scheme's caps at M′ -/

/-! ## O5c at M′ -/

end Lvm.ASM
