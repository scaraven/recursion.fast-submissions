-- WP-14 (ASM), adapted for lvm2 S4 (X-REC2-CERT): the extraction map of the `S` branch (DEC's
-- level-1 decoder `decodeRec1` then WP-13b's level-0 decoder `decodeRec`, on `C_rec`'s two words,
-- fold challenges and final residual read off the history), its correctness at an accepted history
-- outside doom and luck, and the knowledge certificate of `schemeS` with the middle phases abstract.
import LvmCertSLuck
import LvmCertS2Mid
import LvmXDecUd
import LvmXDec1Ud

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
