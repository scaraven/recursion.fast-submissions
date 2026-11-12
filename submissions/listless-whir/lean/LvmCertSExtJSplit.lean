-- New for lvm2 (J2C-C, J2′): the history parsers of `P_S` with `C_rec` at the Johnson radius (`cfgRec20Jp`, OOD
-- after level 0). Adapted from this entry's `LvmCertSExt.lean` (WP-14 / X-REC2 S4: `accept_split`, `recData2`,
-- `recData2_split`, `foldChal_split`, `rec1Of_split`, `foldChal1_split`), re-cut for `stackPrefixJ`.
import LvmCertSLuckJ
import LvmCertSExt
import LvmCertSInv
import LvmWhirMidR

/-!
# The J2′ history parsers (J2C-DES §3, T7)

`C_rec`'s opening at J2′ (`verifyStackedJ cfgRec20Jp`, levels `(6,2,115) (4,3,77)`, `g = 14`) is the UD
one of S4 up to level 1's cap; after the cap it samples the **OOD point** (13 coordinates), reads its
answer `y` and intro polynomial, then runs level 0's query group (`18` challenges), the query intro, level
1's four fold rounds and the residual (`whirPrefixJ`), then the final level's suffix (`stackSuffixJ`).

* `recPrefix_split`: a completed run of `recPrefixProg mid x` (`LvmCertSInv`: roots, middle phases,
  `stackPrefixJ`) is the roots, the middle phases, `ρ`, the first round polynomial, level 0's fold rounds,
  level 1's cap, the OOD point, answer and intro, level 0's query group, the query intro, level 1's fold
  rounds and the residual; with the values.
* `PSWith_eq_prefixJ`: **`P_S = recPrefixProg >>= (suffix; C_main; true)`**; `accept_splitJ`: an accepted
  history is a completed `recPrefixProg` run (split as above) and the rest.
* **`recData2J mid x h`**: the run's `(α₀, r₁, res)` (level-0 fold challenges, final fold state, residual),
  read off `h` as the return of `recPrefixProg`; `recData2J_of_prefix`, `recData2J_split` (`α₀ = r.2`),
  `folds_splitJ` (`r₁`'s folds are `r.2 ++ r₁.2`).
* The luck's readers on a split history: `foldChal_of_splitJ` (`α₀ = r.2`), `rec1Of_of_splitJ`,
  `foldChal1J_of_splitJ` (`α₁ = r₁.2`), `W1L_of_splitJ`; the commitments `commits_prefixJ`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

/-! ## Facts about runs -/

/-- **The OOD point's run**: its challenges, in order. -/
theorem sampleChallenges_after : ∀ (n : ℕ) {l : List Ev} {z : List E},
    (VerifierProgram.sampleChallenges n).after l = some (.ret z) → l = z.map Ev.sample ∧ z.length = n
  | 0, l, z, h => by
    cases l with
    | nil => simp [VerifierProgram.sampleChallenges, VerifierProgram.after] at h; subst h; simp
    | cons e es => cases e <;> simp [VerifierProgram.sampleChallenges, VerifierProgram.after] at h
  | n + 1, l, z, h => by
    unfold VerifierProgram.sampleChallenges at h
    obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
    obtain rfl := sample_after h1
    obtain ⟨zs, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
    obtain ⟨rfl, hl⟩ := sampleChallenges_after n h3
    cases m₂ with
    | nil =>
      simp [VerifierProgram.after, pure] at h4; subst h4
      simp [hl]
    | cons e es => cases e <;> simp [VerifierProgram.after, pure] at h4

theorem filterMap_sample_map (z : List E) : (z.map Ev.sample).filterMap sampleOf = z := by
  induction z with
  | nil => rfl
  | cons c z ih => simp [sampleOf, ih]

theorem nc_sampleChallenges : ∀ n, (VerifierProgram.sampleChallenges n).NoCommit
  | 0 => trivial
  | n + 1 => NoCommit.bind nc_sample fun _ ↦ NoCommit.bind (nc_sampleChallenges n) fun _ ↦ nc_ret _

/-- **J2′'s level-0 query group of `C_rec`** (P20, `g = 14`): the separating challenge and nonce, the
proof of work, `115` positions, `λ`, the openings of commitment `cidx 1 2 0`. -/
abbrev qgRecJ (d : ℕ) : VerifierProgram (List ℕ × E × List (List K)) :=
  (grindPre 14).bind fun _ ↦ queryFragG 14 8 d 115 (cidx 1 2 0)

/-- Its `18` challenges (separating, proof of work, `15` positions' challenges for `115` positions, `λ`). -/
theorem qgRecJ_after_samples {d : ℕ} {l : List Ev} {gg : List ℕ × E × List (List K)}
    (h : (qgRecJ d).after l = some (.ret gg)) : (l.filterMap sampleOf).length = 18 := by
  obtain ⟨_, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret h
  rw [List.filterMap_append, List.length_append, grindPre_after_samples (by decide) h1,
    queryFragG_after_samples (by decide) h2]
  rfl

theorem nc_qgRecJ (d : ℕ) : (qgRecJ d).NoCommit :=
  NoCommit.bind (nc_grindPre _) fun _ ↦ NoCommit.bind (nc_powCheck _) fun _ ↦ nc_queryFrag _ _ _ _

/-! ## The program -/

theorem levels_rec20Jp_ne : cfgRec20Jp.levels ≠ [] := List.cons_ne_nil _ _

/-- **`P_S` at J2′ is the run up to `C_rec`'s residual, then `C_rec`'s suffix, `C_main`'s opening and
`true`.** -/
theorem PSWith_eq_prefixJ (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    PSWith mid x = (recPrefixProg mid x).bind fun ca ↦
      (stackSuffixJ cfgRec20Jp ca.1.1 levels_rec20Jp_ne ca.2).bind fun _ ↦
        (verifyStackedJ (cfgMain24J 3) ca.1.2).bind fun _ ↦ .ret true := by
  unfold PSWith recPrefixProg
  simp only [verifyStackedJ_eq_prefix cfgRec20Jp rfl levels_rec20Jp_ne, bind_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rfl

section Split

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}

/-- **A completed run of `recPrefixProg`** (J2′): the roots, the middle phases, `C_rec`'s batching
challenge, first round polynomial, level-0 fold rounds, level-1 cap, the OOD point (`13` challenges), its
answer and intro polynomial, level 0's query group, the query intro polynomial, level-1 fold rounds and
the residual; it returns `(cl, ρ, (r₁, res))`. -/
theorem recPrefix_split {h₁ : List Ev} {cl : OpenClaims} {a : E × ((WhirStateT × List E) × List E)}
    (hpre : (recPrefixProg mid x).after h₁ = some (.ret (cl, a))) :
    ∃ (hr lm : List Ev) (ρ : E) (lq : List Ev) (quad : List E) (lf : List Ev)
      (r : WhirStateT × List E) (lc lz : List Ev) (z : List E) (ly : List Ev) (y : E) (lhy : List Ev)
      (hy : List E) (lg : List Ev) (g : List ℕ × E × List (List K)) (lhq : List Ev) (hq : List E)
      (lf1 : List Ev) (r₁ : WhirStateT × List E) (lres : List Ev) (res : List E),
      h₁ = hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lz ++ (ly ++ (lhy ++ (lg ++
        (lhq ++ (lf1 ++ lres))))))))))) ∧
      a = (ρ, (r₁, res)) ∧
      rootsProg.after hr = some (.ret ()) ∧ (mid x).after lm = some (.ret cl) ∧
      (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq = some (.ret quad) ∧
      (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r) ∧
      (readCommitment (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4)).after lc = some (.ret ()) ∧
      (VerifierProgram.sampleChallenges (19 - r.1.folds.length)).after lz = some (.ret z) ∧
      readScalar.after ly = some (.ret y) ∧
      (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 y none).after lhy = some (.ret hy) ∧
      (qgRecJ (19 - r.1.folds.length + 2)).after lg = some (.ret g) ∧
      (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).after lhq = some (.ret hq) ∧
      (foldRoundsT 4 (glueMid 19 0 r z y hy g.1 g.2.1 g.2.2 hq) []).after lf1 = some (.ret r₁) ∧
      (readScalars (2 ^ (19 - r₁.1.folds.length))).after lres = some (.ret res) := by
  unfold recPrefixProg at hpre
  obtain ⟨_, hr, l₂, rfl, h1, h2⟩ := after_bind_ret (p := rootsProg) hpre
  obtain ⟨cl', lm, l₃, rfl, h3, h4⟩ := after_bind_ret (p := mid x) h2
  obtain ⟨a', lp, l₄, rfl, h5, h6⟩ := after_bind_ret (p := stackPrefixJ cfgRec20Jp cl'.1) h4
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
  change (whirPrefixJ 19 8 1 2 14 0 [⟨6, 2, 115⟩, ⟨4, 3, 77⟩] _).after lw = _ at h10
  rw [whirPrefixJ_mid] at h10
  obtain ⟨r, lf, l₁₀, rfl, h12, h13⟩ := after_bind_ret h10
  unfold midTailPJ at h13
  obtain ⟨_, lc, l₁₁, rfl, hc, h14⟩ := after_bind_ret h13
  obtain ⟨z, lz, l₁₂, rfl, hz, h15⟩ := after_bind_ret h14
  obtain ⟨y, ly, l₁₃, rfl, hyr, h16⟩ := after_bind_ret h15
  obtain ⟨hy, lhy, l₁₄, rfl, hhy, h17⟩ := after_bind_ret h16
  obtain ⟨_, lgp, l₁₅, rfl, hgp, h18⟩ := after_bind_ret h17
  rw [query_bindG'] at h18
  obtain ⟨g, lgq, l₁₆, rfl, hgq, h19⟩ := after_bind_ret h18
  have hg : (qgRecJ (19 - r.1.folds.length + 2)).after (lgp ++ lgq) = some (.ret g) :=
    (after_bind_append (fun _ ↦ queryFragG 14 8 (19 - r.1.folds.length + 2) 115 (cidx 1 2 0))
      (p := grindPre 14) hgp lgq).trans hgq
  unfold midFinishPJ at h19
  obtain ⟨hq, lhq, l₁₇, rfl, hhq, h20⟩ := after_bind_ret h19
  rw [whirPrefixJ_one] at h20
  obtain ⟨r₁, lf1, l₁₈, rfl, hf1, h21⟩ := after_bind_ret h20
  obtain ⟨res, lres, l₁₉, rfl, hres, h22⟩ := after_bind_ret h21
  obtain ⟨rfl, rfl⟩ : l₁₉ = [] ∧ (r₁, res) = b := by
    cases l₁₉ with
    | nil => simp [VerifierProgram.after] at h22; exact ⟨rfl, h22⟩
    | cons e es => cases e <;> simp [VerifierProgram.after] at h22
  exact ⟨hr, lm, ρ, lq, quad, lf, r, lc, lz, z, ly, y, lhy, hy, lgp ++ lgq, g, lhq, hq, lf1, r₁, lres,
    res, by simp, rfl, h1, h3, h8, h12, hc, hz, hyr, hhy, hg, hhq, hf1, hres⟩

/-- **An accepted history of `P_S` at J2′** is a completed run of `recPrefixProg` (`recPrefix_split`
splits it), then a run of `C_rec`'s suffix, `C_main`'s opening and `true`. -/
theorem accept_splitJ {h : List Ev} (hacc : (PSWith mid x).after h = some (.ret true)) :
    ∃ (h₁ rest : List Ev) (cl : OpenClaims) (a : E × ((WhirStateT × List E) × List E)),
      h = h₁ ++ rest ∧ (recPrefixProg mid x).after h₁ = some (.ret (cl, a)) ∧
      ((stackSuffixJ cfgRec20Jp cl.1 levels_rec20Jp_ne a).bind fun _ ↦
        (verifyStackedJ (cfgMain24J 3) cl.2).bind fun _ ↦ .ret true).after rest = some (.ret true) := by
  rw [PSWith_eq_prefixJ] at hacc
  obtain ⟨⟨cl, a⟩, h₁, rest, rfl, h1, h2⟩ := after_bind_ret hacc
  exact ⟨h₁, rest, cl, a, rfl, h1, h2⟩

end Split

/-! ## The history's values -/

/-- **`C_rec`'s values at J2′**, read off a history as the return of `recPrefixProg`: the level-0 fold
challenges `α₀` (the first six of the final fold state's), the final fold state `r₁` (`α₁ = r₁.2`) and
the residual. -/
def recData2J (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    Option (List E × (WhirStateT × List E) × List E) :=
  match (recPrefixProg mid x).retSplit h with
  | none => none
  | some ((_, _, r₁, res), _, _) => some (r₁.1.folds.take 6, r₁, res)

theorem recData2J_of_prefix {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}
    {h₁ : List Ev} {cl : OpenClaims} {a : E × ((WhirStateT × List E) × List E)}
    (hpre : (recPrefixProg mid x).after h₁ = some (.ret (cl, a))) (t : List Ev) :
    recData2J mid x (h₁ ++ t) = some (a.2.1.1.folds.take 6, a.2.1, a.2.2) := by
  unfold recData2J
  rw [retSplit_of_after _ _ _ hpre]

/-- **The run's fold challenges**: `C_rec`'s final fold state holds `α₀ = r.2` (level 0's six) then
`α₁ = r₁.2` (level 1's four). -/
theorem folds_splitJ {cl : OpenClaims} {ρ : E} {quad : List E} {lf lf1 : List Ev} {r r₁ : WhirStateT × List E}
    {z : List E} {y : E} {hy hq : List E} {g : List ℕ × E × List (List K)}
    (h10 : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hf1 : (foldRoundsT 4 (glueMid 19 0 r z y hy g.1 g.2.1 g.2.2 hq) []).after lf1 = some (.ret r₁)) :
    r₁.1.folds = r.2 ++ r₁.2 ∧ r.2.length = 6 ∧ r₁.2.length = 4 := by
  obtain ⟨e1, e2, e3, -, -⟩ := foldRoundsT_after 6 _ [] h10
  rw [List.nil_append] at e1 e3
  obtain ⟨f1, f2, f3, -, -⟩ := foldRoundsT_after 4 _ [] hf1
  rw [List.nil_append] at f1
  exact ⟨by rw [f3, glueMid_folds, e3, ← e1, ← f1], by rw [e1]; exact e2, by rw [f1]; exact f2⟩

/-- **`recData2J` on a split run** (UD's `recData2_split`): `(α₀, r₁, res)` with `α₀ = r.2`. -/
theorem recData2J_split {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8} {h₁ : List Ev}
    {cl : OpenClaims} {ρ : E} {quad : List E} {lf lf1 : List Ev} {r r₁ : WhirStateT × List E}
    {res z : List E} {y : E} {hy hq : List E} {g : List ℕ × E × List (List K)}
    (hpre : (recPrefixProg mid x).after h₁ = some (.ret (cl, (ρ, (r₁, res)))))
    (h10 : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hf1 : (foldRoundsT 4 (glueMid 19 0 r z y hy g.1 g.2.1 g.2.2 hq) []).after lf1 = some (.ret r₁))
    (t : List Ev) : recData2J mid x (h₁ ++ t) = some (r.2, r₁, res) := by
  obtain ⟨hfl, h6, -⟩ := folds_splitJ h10 hf1
  rw [recData2J_of_prefix hpre t]
  dsimp only
  rw [hfl, List.take_left' h6]

section Readers

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}
  {hr lm lq lf lc R : List Ev} {cl : OpenClaims} {ρ : E} {quad : List E} {r : WhirStateT × List E}
  (h1 : rootsProg.after hr = some (.ret ())) (h3 : (mid x).after lm = some (.ret cl))
  (h8 : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq = some (.ret quad))
  (h10 : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
include h1 h3 h8 h10

/-- **The level-0 fold challenges read by the luck are the run's.** -/
theorem foldChal_of_splitJ :
    foldChal mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ R))))) = r.2 := by
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

/-- **`C_rec`'s level-1 cap as the luck reads it** is the run's. -/
theorem rec1Of_of_splitJ {W : Compile.Word} {ht w : ℕ} (hlc : lc = [Ev.commit ht w W]) :
    rec1Of mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ R)))))) = some (W, R) := by
  have hcq := NoCommit.after_commits (nc_roundPoly _ _ _) h8
  have hcf := NoCommit.after_commits (nc_foldRoundsT _ _ _) h10
  unfold rec1Of afterMid
  rw [retSplit_of_after _ _ _ h1]
  dsimp only
  rw [retSplit_of_after _ _ _ h3]
  dsimp only
  subst hlc
  have := splitCommit_of_noCommit ([Ev.sample ρ] ++ lq ++ lf) (by
    simp only [commits_append, hcq, hcf]; rfl) ht w W R
  simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using this

/-- The level-1 word read by the luck is the run's. -/
theorem W1L_of_splitJ {W : Compile.Word} {ht w : ℕ} (hlc : lc = [Ev.commit ht w W]) :
    W1L mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ R)))))) = W :=
  W1L_of_rec1Of (rec1Of_of_splitJ h1 h3 h8 h10 hlc)

/-- **The level-1 fold challenges read by the luck are the run's** (after the cap: `13` OOD challenges,
the answer and its intro, the query group's `18`, the query intro, then the four fold rounds). -/
theorem foldChal1J_of_splitJ {W : Compile.Word} {ht w : ℕ} (hlc : lc = [Ev.commit ht w W])
    {lz ly lhy lg lhq lf1 R' : List Ev} {z : List E} {y : E} {hy hq : List E}
    {g : List ℕ × E × List (List K)} {s₁ : WhirStateT} {r₁ : WhirStateT × List E}
    (hz : (VerifierProgram.sampleChallenges (19 - r.1.folds.length)).after lz = some (.ret z))
    (hyr : readScalar.after ly = some (.ret y))
    (hhy : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 y none).after lhy = some (.ret hy))
    (hg : (qgRecJ (19 - r.1.folds.length + 2)).after lg = some (.ret g))
    (hhq : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).after lhq = some (.ret hq))
    (hf1 : (foldRoundsT 4 s₁ []).after lf1 = some (.ret r₁)) :
    foldChal1J mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lz ++ (ly ++ (lhy ++
      (lg ++ (lhq ++ (lf1 ++ R')))))))))))) = r₁.2 := by
  obtain ⟨e1, e2, -⟩ := foldRoundsT_after 4 _ [] hf1
  rw [List.nil_append] at e1
  obtain ⟨-, e3, -⟩ := foldRoundsT_after 6 _ [] h10
  obtain ⟨rfl, hzl⟩ := sampleChallenges_after _ hz
  have hfl : r.1.folds.length = 6 := by
    obtain ⟨-, -, e4, -⟩ := foldRoundsT_after 6 _ [] h10
    rw [e4]; simpa using e3
  have hzs : ((z.map Ev.sample).filterMap sampleOf).length = 13 := by
    rw [filterMap_sample_map, hzl, hfl]
  have hys := MovesOnly.after_samples (p := readScalar) (fun _ ↦ trivial) hyr
  have hhys := MovesOnly.after_samples (movesOnly_roundPoly _) hhy
  have hgs := qgRecJ_after_samples hg
  have hhqs := MovesOnly.after_samples (movesOnly_roundPoly _) hhq
  unfold foldChal1J
  rw [rec1Of_of_splitJ h1 h3 h8 h10 hlc]
  dsimp only
  simp only [List.filterMap_append, hys, hhys, hhqs, ← e1, List.nil_append]
  rw [← List.append_assoc, List.drop_append_of_le_length (by simp only [List.length_append]; omega),
    List.drop_eq_nil_of_le (by simp only [List.length_append]; omega),
    List.nil_append, List.take_append_of_le_length (by rw [e1, e2]),
    List.take_of_length_le (by rw [e1, e2])]

end Readers

end Lvm.ASM
