-- New for `flock-recursive` (BLUEPRINT §3, A.4, A.9; stage S-G4, `hFin` step 2a).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessAccSem
import FRSoundness4P4aSeg

/-!
# `hFin`, step 2a: the phase segments of an accepted skeleton

`refPhases` over the phase table, cut at phase `k` (**`refPhases_at`**, in `refPhases_chain`'s
style): the trace splits as `A ++ trk`, `A` the earlier phases' items; phase `k` runs `refPhase`
on `trk` from the context `cAt k` (the generator's context after the earlier phases) and the
registers `M` the earlier phases left; its values extend into the skeleton's registers (`ExtA`);
its flag is one of the skeleton's flags.

On the full table (**`phase_at`**) the Fiat–Shamir entries from `phStart k` on are the
`fsOf` of `trk` (`fsOf_drop_phStart`), and the skeleton's `outs[k]` is the list phase `k` pushes
(`skeleton_outs`, from `genPhase_outs`).

The phase table facts used here (`phaseIx_P1`, `phaseIx_Pf`, `phases_lvl`, `phases_pf`) are the
names and shapes of named rows, read off `phases`' definition (`levelPhases`, `finalPhase`).
-/

namespace FR.Snd
open RecursionFast

variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- The items of a list of phases. -/
abbrev psItems (ps : List Phase) : List Item := ps.flatMap fun p => p.shape.items

theorem genPhases_take_succ (p : Phase) (ps : List Phase) (n k : ℕ) (c : GCtx) :
    (genPhases ((p :: ps).take (k + 1)) n c).2 = (genPhases (ps.take k) (n + 1) (genPhase n p c).2).2 :=
  rfl

/-- **Phase `k` of a run of phases**: the trace before it (`A`, one entry per earlier item), its
reference run from the generator's context and the earlier registers `M`, the register file it
extends, and its flag among the run's flags. -/
theorem refPhases_at : ∀ (ps : List Phase) (n : ℕ) (c : GCtx) (r : Array Val) (tr : Trace)
    (y : List Val × List Bool × Trace), refPhases impl κ inp ps n c r tr = some y →
    c.next = r.size → StartOk ps c r → ps.all (fun p => shapeOK p.shape) = true →
    ∀ k (hk : k < ps.length), ∃ (A trk : Trace) (M : List Val) (x : List Val × Bool × Trace),
      tr = A ++ trk ∧ A.length = (psItems (ps.take k)).length ∧
      refPhase impl κ inp (n + k) ps[k] (genPhases (ps.take k) n c).2 (r ++ M.toArray) trk =
        some x ∧
      (genPhases (ps.take k) n c).2.next = (r ++ M.toArray).size ∧
      ((ps[k].shape = .seed ∧ CtxOk (genPhases (ps.take k) n c).2 #[default]) ∨
        CtxOk (genPhases (ps.take k) n c).2 (r ++ M.toArray)) ∧
      ExtA (r ++ (M ++ x.1).toArray) (r ++ y.1.toArray) ∧ x.2.1 ∈ y.2.1
  | [], _, _, _, _, _, _, _, _, _, k, hk => absurd hk (by simp)
  | p :: ps, n, c, r, tr, y, h, hb, hs, ha, k, hk => by
    have hwf : (p.shape = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r := by
      rcases hs with h | ⟨q, qs, he, hq, h0⟩
      · exact .inr h
      · cases he; exact .inl ⟨hq, h0⟩
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [refPhases, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y', hy', rfl⟩ := h
    rcases k with _ | k
    · refine ⟨[], tr, [], x, rfl, rfl, by simpa [genPhases] using hx, by simpa [genPhases] using hb,
        by simpa [genPhases] using hwf, ?_, by simp⟩
      have := ExtA.app (r ++ x.1.toArray) y'.1
      simpa [app_app] using this
    · obtain ⟨h1, h2, -⟩ := genPhase_ctx impl κ inp n p c r tr x hb hwf hx
      obtain ⟨seg, hseg, hlen, -⟩ := refPhase_chain inp κ impl hx hb ha.1
        (q0 := if isSeed p.shape then 0 else 1) (by split <;> simp_all)
        (by rcases hwf with ⟨h, -⟩ | h
            · left; simp [h, isSeed]
            · right; exact h.1)
      obtain ⟨A, trk, M, x', e1, e2, e3, e4, e5, e6, e7⟩ :=
        refPhases_at ps (n + 1) _ _ _ y' hy' h1 (.inl h2) ha.2 k (by simpa using hk)
      refine ⟨seg ++ A, trk, x.1 ++ M, x', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hseg, e1, List.append_assoc]
      · simp [psItems, hlen, e2]
      · rw [genPhases_take_succ, show n + (k + 1) = n + 1 + k by omega, ← app_app]
        simpa using e3
      · rw [genPhases_take_succ, e4, ← app_app]
      · rw [genPhases_take_succ, ← app_app]; simpa using e5
      · rw [← app_app, ← app_app]
        simpa [app_app, List.append_assoc] using e6
      · exact List.mem_cons_of_mem _ e7

theorem psItems_filter_length (ps : List Phase) :
    ((psItems ps).filter Item.isFS).length =
      (ps.map fun p => (p.shape.items.filter Item.isFS).length).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [psItems, List.filter_append, ih] at *

/-- The context before phase `k` (the generator's, after phases `0 … k − 1`). -/
def cAt (k : ℕ) : GCtx := (genPhases (phases.take k) 0 ctx₀).2

/-- Control (positive): before phase 0 the context is `ctx₀`. -/
theorem cAt_zero : cAt 0 = ctx₀ := rfl

/-- Control (positive, negative): after the seed phase the next free register is 7, not 0. -/
theorem cAt_one_next : (cAt 1).next = 7 ∧ (cAt 1).next ≠ 0 := by
  have : cAt 1 = (genPhase 0 ⟨"seed", .seed⟩ ctx₀).2 := rfl
  rw [this]; simp [genPhase, ctx₀]

/-- Controls for `psItems`: one phase's items; two seeds are two items, not one. -/
theorem psItems_ctl (p : Phase) : psItems [p] = p.shape.items ∧
    psItems [⟨"", .seed⟩, ⟨"", .seed⟩] ≠ [.seed] := by
  refine ⟨by simp [psItems], by simp [psItems, Shape.items]⟩

/-- **Phase `k` of the accepted skeleton** (`refPhases_at` on the table from `ctx₀`), with the
run's Fiat–Shamir entries from `phStart k` on. -/
theorem phase_at {tr : Trace} {y : List Val × List Bool × Trace}
    (h : refPhases impl κ inp phases 0 ctx₀ #[] tr = some y) {k : ℕ} (hk : k < phases.length) :
    ∃ (trk : Trace) (M : List Val) (x : List Val × Bool × Trace),
      refPhase impl κ inp k phases[k] (cAt k) (#[] ++ M.toArray) trk = some x ∧
      (cAt k).next = M.length ∧
      ((phases[k].shape = .seed ∧ CtxOk (cAt k) #[default]) ∨ CtxOk (cAt k) (#[] ++ M.toArray)) ∧
      ExtA (#[] ++ (M ++ x.1).toArray) (#[] ++ y.1.toArray) ∧ x.2.1 ∈ y.2.1 ∧
      (fsOf tr items).drop (phStart k) = fsOf trk (psItems (phases.drop k)) ∧
      ∃ A, tr = A ++ trk := by
  obtain ⟨A, trk, M, x, e1, e2, e3, e4, e5, e6, e7⟩ :=
    refPhases_at impl κ inp phases 0 ctx₀ #[] tr y h rfl
      (.inr ⟨_, _, rfl, rfl, by simp [CtxOk, ctx₀]⟩) phases_shapeOK k hk
  refine ⟨trk, M, x, by simpa [cAt] using e3, by simpa [cAt] using e4, e5, e6, e7, ?_⟩
  have hit : items = psItems (phases.take k) ++ psItems (phases.drop k) := by
    rw [psItems, psItems, ← List.flatMap_append, List.take_append_drop]; rfl
  refine ⟨?_, A, e1⟩
  rw [e1, hit, fsOf_append e2, List.drop_left' ?_]
  rw [fsOf_length e2, psItems_filter_length, phStart_eq_sum hk]

/-- `genPhase` pushes one list on `outs`. -/
theorem genPhase_outs (n : ℕ) (p : Phase) (c : GCtx) :
    (genPhase n p c).2.outs = c.outs.push ((genPhase n p c).2.outs.back?.getD []) := by
  obtain ⟨name, sh⟩ := p
  cases sh with
  | seed => simp [genPhase]
  | absorb f len => simp only [genPhase]; split_ifs <;> simp
  | squeezes k ch => cases ch <;> simp [genPhase]
  | uni f => simp [genPhase]
  | rounds f k deg inK real => simp only [genPhase]; split <;> simp
  | queries i => simp [genPhase]

theorem genPhases_outs : ∀ (ps : List Phase) (n : ℕ) (c : GCtx),
    (genPhases ps n c).2.outs.size = c.outs.size + ps.length ∧
      ∀ k (hk : k < ps.length), (genPhases ps n c).2.outs.getD (c.outs.size + k) [] =
        (genPhase (n + k) ps[k] (genPhases (ps.take k) n c).2).2.outs.back?.getD []
  | [], _, c => ⟨by simp [genPhases], fun k hk => absurd hk (by simp)⟩
  | p :: ps, n, c => by
    have ho := genPhase_outs n p c
    obtain ⟨ih1, ih2⟩ := genPhases_outs ps (n + 1) (genPhase n p c).2
    rw [ho, Array.size_push] at ih1 ih2
    refine ⟨by simp only [genPhases, ih1, List.length_cons]; omega, fun k hk => ?_⟩
    rcases k with _ | k
    · simp only [genPhases, List.getElem_cons_zero, List.take_zero, Nat.add_zero]
      have hpre := genPhases_prefix ps (n + 1) (genPhase n p c).2 c.outs.size (by rw [ho]; simp)
      rw [hpre, ho]; simp
    · have := ih2 k (by simpa using hk)
      simp only [genPhases] at this ⊢
      rw [show c.outs.size + (k + 1) = c.outs.size + 1 + k by omega, this,
        show n + 1 + k = n + (k + 1) by omega]
      rfl
where
  genPhases_prefix : ∀ (ps : List Phase) (n : ℕ) (c : GCtx) (m : ℕ), m < c.outs.size →
      (genPhases ps n c).2.outs.getD m [] = c.outs.getD m []
    | [], _, _, _, _ => rfl
    | p :: ps, n, c, m, hm => by
      simp only [genPhases]
      rw [genPhases_prefix ps (n + 1) _ m (by rw [genPhase_outs]; simp; omega), genPhase_outs]
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, show m ≠ c.outs.size by omega]

/-- **The skeleton's `outs[k]`** is phase `k`'s out list. -/
theorem skeleton_outs {k : ℕ} (hk : k < phases.length) :
    skeleton.2.outs.getD k [] = (genPhase k phases[k] (cAt k)).2.outs.back?.getD [] := by
  have := (genPhases_outs phases 0 ctx₀).2 k hk
  simpa [skeleton, ctx₀, cAt] using this

/-! ## The named rows of the phase table -/

theorem flatMap_level_getElem {n i k : ℕ} (hi : i < n) (hk : k < 5) :
    ((List.range n).flatMap levelPhases)[5 * i + k]'(by rw [flatMap_level_length]; omega) =
      (levelPhases i)[k] := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · rw [List.getElem_append_left (by rw [flatMap_level_length]; omega)]; exact ih h
    · rw [List.getElem_append_right (by rw [flatMap_level_length]; omega)]
      simp only [flatMap_level_length, Nat.add_sub_cancel_left, List.flatMap_singleton]; rfl

theorem phases_length : phases.length = 52 := by
  simp only [phases, List.length_append, piopPhases_length, flatMap_level_length, nLevels]; rfl

/-- **Level `i`'s phase `k`** is row `26 + 5i + k`. -/
theorem phases_lvl {i k : ℕ} (hi : i < 5) (hk : k < 5) :
    phases[26 + 5 * i + k]'(by rw [phases_length]; omega) = (levelPhases i)[k] := by
  have h1 : 26 + 5 * i + k < (piopPhases ++ (List.range nLevels).flatMap levelPhases).length := by
    simp only [List.length_append, piopPhases_length, flatMap_level_length, nLevels]; omega
  simp only [phases]
  rw [List.getElem_append_left h1, List.getElem_append_right (by rw [piopPhases_length]; omega)]
  simp only [piopPhases_length, show 26 + 5 * i + k - 26 = 5 * i + k by omega]
  exact flatMap_level_getElem (by simpa [nLevels] using hi) hk

/-- **Row 51 is `Pf`.** -/
theorem phases_pf : phases[51]'(by rw [phases_length]; omega) = finalPhase := by
  simp only [phases]
  rw [List.getElem_append_right (by
    simp only [List.length_append, piopPhases_length, flatMap_level_length, nLevels]; omega)]
  simp only [List.length_append, piopPhases_length, flatMap_level_length, nLevels]; rfl

end FR.Snd
