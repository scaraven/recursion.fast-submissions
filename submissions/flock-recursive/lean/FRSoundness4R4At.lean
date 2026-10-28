-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.4, A.9; stage R4).
import FRSoundness4R4Run

/-!
# Phase `k` of an accepted `gen4` skeleton (`phase_at4`, `SkRun4`)

3.x's `refPhases_at`/`phase_at`/`skeleton_outs` (`FRSoundnessAccSeg`) for `refPhases4`:

* **`refPhases4_at`**: a run of phases cut at phase `k`: the trace splits as `A ++ trk` (`A` one
  entry per earlier item), phase `k` runs `refPhase4` on `trk` from the generator's context
  `cAt4 S p k` and the earlier registers `M`; its values extend into the run's registers; its flag
  is one of the run's flags.
* **`phase_at4`** (`seq4`): the Fiat–Shamir entries from `phStart4 k` on are `trk`'s
  (`phStart4_eq_sum`, from `fsStarts4`'s fold).
* **`skeleton4_outs`**: the skeleton's `outs[k]` is phase `k`'s out list.
* **`SkRun4`**: the facts of an accepted run the views use (the reference run, every flag, the
  482 Fiat–Shamir entries and their queries); **`skRun4_of_accept`**.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable (impl : OpImpl) (κ : Kind) (inp : Input) (S : Seq) (p : KindP)

/-- The items of a list of phases. -/
abbrev psItems4 (S : Seq) (ps : List (String × Sh)) : List Item := ps.flatMap fun ph => ph.2.itemsL S.lv

theorem genPhases4_take_succ (ph : String × Sh) (ps : List (String × Sh)) (n k : ℕ) (c : GCtx) :
    (genPhases4 S p ((ph :: ps).take (k + 1)) n c).2 =
      (genPhases4 S p (ps.take k) (n + 1) (genPhase4 S p n ph c).2).2 := rfl

/-- **Phase `k` of a run of phases.** -/
theorem refPhases4_at : ∀ (ps : List (String × Sh)) (n : ℕ) (c : GCtx) (r : Array Val) (tr : Trace)
    (y : List Val × List Bool × Trace), refPhases4 impl κ inp S p ps n c r tr = some y →
    c.next = r.size → StartOk4 ps c r → ps.all (fun ph => shOK4 ph.2) = true →
    ∀ k (hk : k < ps.length), ∃ (A trk : Trace) (M : List Val) (x : List Val × Bool × Trace),
      tr = A ++ trk ∧ A.length = (psItems4 S (ps.take k)).length ∧
      refPhase4 impl κ inp S p (n + k) ps[k] (genPhases4 S p (ps.take k) n c).2 (r ++ M.toArray) trk =
        some x ∧
      (genPhases4 S p (ps.take k) n c).2.next = (r ++ M.toArray).size ∧
      ((ps[k].2 = .seed ∧ CtxOk (genPhases4 S p (ps.take k) n c).2 #[default]) ∨
        CtxOk (genPhases4 S p (ps.take k) n c).2 (r ++ M.toArray)) ∧
      ExtA (r ++ (M ++ x.1).toArray) (r ++ y.1.toArray) ∧ x.2.1 ∈ y.2.1
  | [], _, _, _, _, _, _, _, _, _, k, hk => absurd hk (by simp)
  | ph :: ps, n, c, r, tr, y, h, hb, hs, ha, k, hk => by
    have hwf : (ph.2 = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r := by
      rcases hs with h | ⟨q, qs, he, hq, h0⟩
      · exact .inr h
      · cases he; exact .inl ⟨hq, h0⟩
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [refPhases4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y', hy', rfl⟩ := h
    rcases k with _ | k
    · refine ⟨[], tr, [], x, rfl, rfl, by simpa [genPhases4] using hx, by simpa [genPhases4] using hb,
        by simpa [genPhases4] using hwf, ?_, by simp⟩
      have := ExtA.app (r ++ x.1.toArray) y'.1
      simpa [app_app] using this
    · obtain ⟨h1, h2, -⟩ := genPhase4_ctx impl κ inp S p n ph c r tr x hb hwf hx
      obtain ⟨seg, hseg, hlen, -⟩ := refPhase4_chain impl κ inp S p hx hb ha.1
        (q0 := if isSeed4 ph.2 then 0 else 1) (by split <;> simp_all)
        (by rcases hwf with ⟨h, -⟩ | h
            · left; simp [h, isSeed4]
            · right; exact h.1)
      obtain ⟨A, trk, M, x', e1, e2, e3, e4, e5, e6, e7⟩ :=
        refPhases4_at ps (n + 1) _ _ _ y' hy' h1 (.inl h2) ha.2 k (by simpa using hk)
      refine ⟨seg ++ A, trk, x.1 ++ M, x', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hseg, e1, List.append_assoc]
      · simp [psItems4, hlen, e2]
      · rw [genPhases4_take_succ, show n + (k + 1) = n + 1 + k by omega, ← app_app]
        simpa using e3
      · rw [genPhases4_take_succ, e4, ← app_app]
      · rw [genPhases4_take_succ, ← app_app]; simpa using e5
      · rw [← app_app, ← app_app]
        simpa [app_app, List.append_assoc] using e6
      · exact List.mem_cons_of_mem _ e7

/-- The context before phase `k` of `phasesOf S`. -/
def cAt4 (k : ℕ) : GCtx := (genPhases4 S p ((phasesOf S).take k) 0 ctx0).2

theorem psItems4_filter_length (ps : List (String × Sh)) :
    ((psItems4 S ps).filter Item.isFS).length =
      (ps.map fun ph => ((ph.2.itemsL S.lv).filter Item.isFS).length).sum := by
  induction ps with
  | nil => rfl
  | cons ph ps ih => simp [psItems4, List.filter_append, ih] at *

theorem fsStarts4_foldl (ps : List (String × Sh)) (a : ℕ) (acc : List ℕ) :
    (ps.foldl (fun (acc : ℕ × List ℕ) ph =>
      (acc.1 + ((ph.2.itemsL seq4.lv).filter Item.isFS).length, acc.2 ++ [acc.1])) (a, acc)).2 =
      acc ++ (List.range ps.length).map fun n =>
        a + ((ps.take n).map fun ph => ((ph.2.itemsL seq4.lv).filter Item.isFS).length).sum := by
  induction ps generalizing a acc with
  | nil => simp
  | cons ph ps ih =>
    rw [List.foldl_cons, ih, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, List.append_assoc,
      List.singleton_append, Function.comp_def, List.take_succ_cons, List.map_cons, List.sum_cons,
      Nat.add_assoc]

/-- **`phStart4 k`** is the number of Fiat–Shamir items before phase `k`. -/
theorem phStart4_eq_sum {k : ℕ} (hk : k < (phasesOf seq4).length) :
    phStart4 k = (((phasesOf seq4).take k).map fun ph =>
      ((ph.2.itemsL seq4.lv).filter Item.isFS).length).sum := by
  rw [phStart4, fsStarts4, fsStarts4_foldl, List.nil_append, List.getD_eq_getElem _ _ (by simpa)]
  simp

theorem shOK_all_seq4 : (phasesOf seq4).all (fun ph => shOK4 ph.2) = true := by
  rw [seq4_eq]; decide +kernel

/-- **Phase `k` of the accepted skeleton of `gen4 seq4 p`**, with the run's Fiat–Shamir entries
from `phStart4 k` on. -/
theorem phase_at4 {tr : Trace} {y : List Val × List Bool × Trace}
    (h : refPhases4 impl κ inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y) {k : ℕ}
    (hk : k < (phasesOf seq4).length) :
    ∃ (trk : Trace) (M : List Val) (x : List Val × Bool × Trace),
      refPhase4 impl κ inp seq4 p k (phasesOf seq4)[k] (cAt4 seq4 p k) (#[] ++ M.toArray) trk = some x ∧
      (cAt4 seq4 p k).next = M.length ∧
      (((phasesOf seq4)[k].2 = .seed ∧ CtxOk (cAt4 seq4 p k) #[default]) ∨
        CtxOk (cAt4 seq4 p k) (#[] ++ M.toArray)) ∧
      ExtA (#[] ++ (M ++ x.1).toArray) (#[] ++ y.1.toArray) ∧ x.2.1 ∈ y.2.1 ∧
      (fsOf tr (itemsOf seq4)).drop (phStart4 k) = fsOf trk (psItems4 seq4 ((phasesOf seq4).drop k)) ∧
      ∃ A, tr = A ++ trk := by
  obtain ⟨A, trk, M, x, e1, e2, e3, e4, e5, e6, e7⟩ :=
    refPhases4_at impl κ inp seq4 p _ 0 ctx0 #[] tr y h rfl (startOk4 seq4) shOK_all_seq4 k hk
  refine ⟨trk, M, x, by simpa [cAt4] using e3, by simpa [cAt4] using e4, e5, e6, e7, ?_, A, e1⟩
  have hit : itemsOf seq4 = psItems4 seq4 ((phasesOf seq4).take k) ++
      psItems4 seq4 ((phasesOf seq4).drop k) := by
    rw [psItems4, psItems4, ← List.flatMap_append, List.take_append_drop]; rfl
  rw [e1, hit, fsOf_append e2, List.drop_left' ?_]
  rw [fsOf_length e2, psItems4_filter_length, phStart4_eq_sum hk]

/-- `genPhase4` pushes one list on `outs`. -/
theorem genPhase4_outs (n : ℕ) (ph : String × Sh) (c : GCtx) :
    (genPhase4 S p n ph c).2.outs = c.outs.push ((genPhase4 S p n ph c).2.outs.back?.getD []) := by
  obtain ⟨name, sh⟩ := ph
  cases sh with
  | absorb f len => simp only [genPhase4]; split_ifs <;> simp
  | squeezes k ch => cases ch <;> simp [genPhase4]
  | uni f => simp only [genPhase4]; split_ifs <;> simp
  | rounds f k deg inK => cases inK <;> simp [genPhase4]
  | _ => simp [genPhase4]

theorem genPhases4_prefix : ∀ (ps : List (String × Sh)) (n : ℕ) (c : GCtx) (m : ℕ), m < c.outs.size →
    (genPhases4 S p ps n c).2.outs.getD m [] = c.outs.getD m []
  | [], _, _, _, _ => rfl
  | ph :: ps, n, c, m, hm => by
    simp only [genPhases4]
    rw [genPhases4_prefix ps (n + 1) _ m (by rw [genPhase4_outs]; simp; omega), genPhase4_outs]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, show m ≠ c.outs.size by omega]

theorem genPhases4_outs : ∀ (ps : List (String × Sh)) (n : ℕ) (c : GCtx),
    (genPhases4 S p ps n c).2.outs.size = c.outs.size + ps.length ∧
      ∀ k (hk : k < ps.length), (genPhases4 S p ps n c).2.outs.getD (c.outs.size + k) [] =
        (genPhase4 S p (n + k) ps[k] (genPhases4 S p (ps.take k) n c).2).2.outs.back?.getD []
  | [], _, c => ⟨by simp [genPhases4], fun k hk => absurd hk (by simp)⟩
  | ph :: ps, n, c => by
    have ho := genPhase4_outs S p n ph c
    obtain ⟨ih1, ih2⟩ := genPhases4_outs ps (n + 1) (genPhase4 S p n ph c).2
    rw [ho, Array.size_push] at ih1 ih2
    refine ⟨by simp only [genPhases4, ih1, List.length_cons]; omega, fun k hk => ?_⟩
    rcases k with _ | k
    · simp only [genPhases4, List.getElem_cons_zero, List.take_zero, Nat.add_zero]
      have hpre := genPhases4_prefix S p ps (n + 1) (genPhase4 S p n ph c).2 c.outs.size
        (by rw [ho]; simp)
      rw [hpre, ho]; simp
    · have := ih2 k (by simpa using hk)
      simp only [genPhases4] at this ⊢
      rw [show c.outs.size + (k + 1) = c.outs.size + 1 + k by omega, this,
        show n + 1 + k = n + (k + 1) by omega]
      rfl

/-- **The skeleton's `outs[k]`** is phase `k`'s out list. -/
theorem skeleton4_outs {k : ℕ} (hk : k < (phasesOf S).length) :
    (skeleton4 S p).2.outs.getD k [] =
      (genPhase4 S p k (phasesOf S)[k] (cAt4 S p k)).2.outs.back?.getD [] := by
  have := (genPhases4_outs S p (phasesOf S) 0 ctx0).2 k hk
  simpa [skeleton4, ctx0, cAt4] using this

/-! ## The accepted run's facts -/

/-- **The facts of an accepted `gen4 seq4 p` run** the views use. -/
structure SkRun4 (impl : OpImpl) (p : KindP) (inp : Input) (tr : Trace)
    (y : List Val × List Bool × Trace) : Prop where
  ref : refPhases4 impl p.tix inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y
  flags : ∀ b ∈ y.2.1, b = true
  len : (fsOf tr (itemsOf seq4)).length = 482
  hq : ∀ q < 482, ((fsOf tr (itemsOf seq4)).getD q default).1 =
    qOf inp q ((fsMsgs4 seq4).getD q none) ((fsOf tr (itemsOf seq4)).getD (q - 1) default).2

/-- **An accepted run of `gen4 seq4 p fin.ops`** (fields asking nothing) is a `SkRun4`. -/
theorem skRun4_of_accept (fin : Finals) {tr : Trace}
    (hna : ∀ f ∈ fin.finRS :: fin.rest, ∀ fi b, (f fi b).1.filterMap Op.item? = [])
    (h : semIR impl (gen4 seq4 p fin.ops) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y := by
  obtain ⟨y, hy, hf, -⟩ := accept_chain4 impl seq4 p inp fin hna h
  obtain ⟨hl, hq⟩ := fsQ_gen4 impl inp seq4 p shOK_seq4 _ h
  rw [fsMsgs4_len] at hl hq
  exact ⟨y, ⟨hy, hf, hl, hq⟩⟩

/-! ## Controls -/

/-- Control (positive): before phase 0 the context is `ctx0`; after the seed the next free
register is `4` (`seedOps4`'s registers), not `0` (negative). -/
theorem cAt4_ctl : cAt4 S p 0 = ctx0 ∧ (cAt4 S p 1).next = 4 ∧ (cAt4 S p 1).next ≠ 0 := by
  have : cAt4 S p 1 = (genPhase4 S p 0 ("seed", .seed) ctx0).2 := rfl
  refine ⟨rfl, ?_, ?_⟩ <;> rw [this] <;> simp [genPhase4, ctx0, seedOps4, opsOut, Op.outs]

end FR.Snd.R4
