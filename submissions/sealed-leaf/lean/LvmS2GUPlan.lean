-- New for lvm2 U-TAPE (UT-L, 2026-11-16): the plan's and Q_link's static stream facts at S2GU (`P20U`): one decision
-- each, as S2GT's `LvmS2GTPlan` (the node soundness and the `KS` bridge read them).
-- GOLF3-U (2026-11-16, proof only): the three decisions (`passR_P20U`, `planSt_P20U`, `hQU20`'s `qOkF`) in one kernel
-- evaluation over the literal `schedU20` and `P20UL` (`planFacts_of`, generic in the parameter set).
import LvmE2QPlanF
import LvmS2GUSched
import LvmS2GUSchedLit
import LvmQAsmFactsL
import LvmE2QInstU

-- (SLF-K: 6 declarations that `certified` does not use moved verbatim to `LvmS2GUOff`, outside its import closure.)

/-!
# The S2GU plan's facts

* **`passR_P20U`**: the one-pass decision at `P20U` (3,649 entries, `Σ clen = 283,952`, `Σ (40 + len) = 538,655`; the
  cap queries at entries 2, 1,004 and 2,423 [measured, a probe evaluation of the plan; the same probe gives S2GT's
  2, 1,316, 2,735]).
* **`planSt_P20U`**: `PlanOk P20U`; **`streamOk_P20U`**; **`qOkF_P20U`** (`hQU20`'s decision).
* **`planFacts_of`** (proof help, any parameter set): the three from one decision over a schedule literal `S` and a
  parameter literal `q` (`schedule p = S`, `p = q`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay Lvm.PlanChk

/-! Proof help (GOLF3-U): the QLT entries' count from one walk of the plan (`fsCnt`, `LvmS2GTPlan`'s private copy),
and the plan's three decisions in one kernel evaluation of the plan walk over a schedule literal (`planFacts_of`). -/

/-- An entry is an FS query (proof help). -/
private def fsB (e : PE) : Bool := match e.k with | .fs _ => true | _ => false

/-- `n` plus the FS entries of `l` (proof help). -/
private def fsCnt : List PE → ℕ → ℕ
  | [], n => n
  | e :: l, n => fsCnt l (Nat.add n (cond (fsB e) 1 0))

private theorem fm_len {α : Type} (F : PE × ℕ → Option α) (hF : ∀ e i, (F (e, i)).isSome = fsB e) :
    ∀ (l : List PE) (i n : ℕ), ((l.zipIdx i).filterMap F).length + n = fsCnt l n
  | [], _, _ => by simp [fsCnt]
  | e :: l, i, n => by
    rw [List.zipIdx_cons, List.filterMap_cons, fsCnt]
    have h := hF e i
    cases hf : F (e, i) with
    | none =>
      rw [hf, Option.isSome_none] at h
      rw [← h, fm_len F hF l (i + 1) _]
      rfl
    | some a =>
      rw [hf, Option.isSome_some] at h
      rw [← h, List.length_cons, ← fm_len F hF l (i + 1) _]
      show _ = _ + (n + 1)
      omega

private theorem fm_len0 {α : Type} (F : PE × ℕ → Option α) (hF : ∀ e i, (F (e, i)).isSome = fsB e)
    (l : List PE) : ((l.zipIdx 0).filterMap F).length = fsCnt l 0 :=
  fm_len F hF l 0 0

private theorem qlt_len (p : Params) (lay : Layout) :
    (qltEntries p lay).length = 2 + fsCnt (plan p) 0 + (17 * nBlk (hashedLen p) - hashedLen p / 8) := by
  rw [qltEntries, List.length_append, List.length_append, List.length_map, List.length_range, fm_len0 _ ?_]
  · rfl
  · intro e i; rcases e with ⟨k, len⟩; cases k <;> rfl

/-! Proof help (GOLF3-U): the walks the decision runs, in `List.rec`/`Nat.rec` form (`planItemsR`, `openItemsR`,
`offAtR`, `fsCntR`, with `openPlanR` inside `planItemR`), each proved equal to its definition by induction (no
evaluation): the kernel runs a recursor directly, where the structural definitions (`brecOn`, `List.range`, `flatMap`,
`++`) cost it about twice as much (the S2GU decision: 14.1 → 8.7 M heartbeats). -/

/-- `List.append` by `List.rec` (proof help). -/
noncomputable def appL {α : Type} (a b : List α) : List α := a.rec b (fun x _ ih => x :: ih)

theorem appL_eq {α : Type} (a b : List α) : appL a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x a ih => exact congrArg (x :: ·) ih

/-- `(List.range' k n).flatMap f ++ tl` by `Nat.rec` (proof help). -/
noncomputable def upL {α : Type} (f : ℕ → List α) (n : ℕ) : ℕ → List α → List α :=
  Nat.rec (motive := fun _ => ℕ → List α → List α) (fun _ tl => tl) (fun _ ih k tl => appL (f k) (ih (k + 1) tl)) n

theorem upL_eq {α : Type} (f : ℕ → List α) :
    ∀ (n k : ℕ) (tl : List α), upL f n k tl = (List.range' k n).flatMap f ++ tl
  | 0, _, _ => rfl
  | n + 1, k, tl => by
    rw [show upL f (n + 1) k tl = appL (f k) (upL f n (k + 1) tl) from rfl, upL_eq f n (k + 1) tl, appL_eq,
      List.range'_succ, List.flatMap_cons, List.append_assoc]

/-- `openPlan` by `upL` (proof help). -/
noncomputable def openPlanR (L : Level) (pe ce co : Nat) : List PE :=
  upL (fun j => ⟨.leaf, L.row⟩ :: upL (fun lvl =>
    [⟨.node pe L.height j lvl (if lvl + 1 = L.path then some (ce, co, L.path) else none), 64⟩]) L.path 0 []) L.t 0 []

theorem openPlan_eq_R (L : Level) (pe ce co : Nat) : openPlan L pe ce co = openPlanR L pe ce co := by
  simp only [openPlanR, upL_eq, List.append_nil, openPlan, List.range_eq_range', List.map_eq_flatMap]

/-- `planItem` with `openPlanR` (proof help). -/
noncomputable def planItemR (p : Params) (w : WS) : Item → List PE × WS
  | .read m => ([], { w with pend := w.pend + eBytes * m })
  | .readW m wd => ([], { w with pend := w.pend + wd * m })
  | .cap c r => ([], { w with pcaps := (r, w.pend, nodeBytes * 2 ^ c) :: w.pcaps,
                              pend := w.pend + nodeBytes * 2 ^ c })
  | .sample => ([⟨.fs w.st, 32 + w.pend⟩], { w.settle with i := w.i + 1, pend := 0, st := w.i })
  | .positions r =>
    let n := (p.level r).nPosQ
    ((List.range n).map (fun k => if k = 0 then ⟨.fs w.st, 32 + w.pend⟩ else ⟨.fs (w.i + k - 1), 32⟩),
      { w.settle with i := w.i + n, pend := 0, st := w.i + n - 1, pe := w.i, posRef := some r,
                      ok := w.ok && decide (1 ≤ n) })
  | .opening r =>
    let L := p.level r
    match w.caps.find? (·.1 == r) with
    | none => ([], { w with ok := false })
    | some (_, ce, co, nb) =>
      (openPlanR L w.pe ce co,
        { w with i := w.i + L.t * (1 + L.path),
                 ok := w.ok && w.pend == 0 && w.pcaps.isEmpty && w.posRef == some r &&
                   decide (1 ≤ L.path) && decide (L.path ≤ L.height) &&
                   decide (nodeBytes * 2 ^ (L.height - L.path) ≤ nb) && decide (L.row ≤ queryCap) &&
                   decide (positionsPerAnswer * (L.nPosQ - 1) < L.t) && decide (L.t ≤ positionsPerAnswer * L.nPosQ) })

theorem planItem_eq_R (p : Params) (w : WS) (it : Item) : planItem p w it = planItemR p w it := by
  cases it with
  | opening r =>
    simp only [planItem, planItemR]
    generalize List.find? (fun x => x.1 == r) w.caps = o
    rcases o with _ | ⟨_, ce, co, nb⟩
    · rfl
    · simp only [openPlan_eq_R]
  | _ => rfl

/-- `planItems` by `List.rec` (proof help). -/
noncomputable def planItemsR (p : Params) (l : List Item) : WS → List PE × WS :=
  l.rec (fun w => ([], w)) (fun it _ ih w =>
    (appL (planItemR p w it).1 (ih (planItemR p w it).2).1, (ih (planItemR p w it).2).2))

theorem planItems_eq_R (p : Params) : ∀ (l : List Item) (w : WS), planItems p w l = planItemsR p l w
  | [], _ => rfl
  | it :: l, w => by
    rw [planItems, planItem_eq_R, planItems_eq_R p l, ← appL_eq]
    rfl

/-- `openItems` by `List.rec` (proof help). -/
noncomputable def openItemsR (p : Params) (l : List Item) : WS → List OpenInfo :=
  l.rec (fun _ => []) (fun it _ ih w => appL (openItem p w it) (ih (planItemR p w it).2))

theorem openItems_eq_R (p : Params) : ∀ (l : List Item) (w : WS), openItems p w l = openItemsR p l w
  | [], _ => rfl
  | it :: l, w => by
    rw [openItems, planItem_eq_R, openItems_eq_R p l, ← appL_eq]
    rfl

/-- `offAt` of the entries' lengths by `List.rec` (proof help). -/
noncomputable def offAtR (l : List PE) : ℕ → ℕ → ℕ :=
  l.rec (fun a _ => a) (fun e _ ih a i => Nat.casesOn (motive := fun _ => ℕ) i a (fun i' => ih (a + (40 + e.len)) i'))

theorem offAt_eq_R : ∀ (l : List PE) (a i : ℕ), offAt (l.map PE.len) a i = offAtR l a i
  | _, _, 0 => by cases ‹List PE› <;> rfl
  | [], _, _ + 1 => rfl
  | e :: l, a, i + 1 => by
    rw [List.map_cons, offAt, offAt_eq_R l]
    rfl

/-- `fsCnt` by `List.rec` (proof help). -/
noncomputable def fsCntR (l : List PE) : ℕ → ℕ :=
  l.rec (fun n => n) (fun e _ ih n => ih (Nat.add n (cond (fsB e) 1 0)))

private theorem fsCnt_eq_R : ∀ (l : List PE) (n : ℕ), fsCnt l n = fsCntR l n
  | [], _ => rfl
  | e :: l, n => by rw [fsCnt, fsCnt_eq_R l]; rfl

/-- **The plan's facts from one decision** (proof help, any parameter set `p`): over the schedule literal `S`
(`schedule p = S`) and the parameter literal `q` (`p = q`), with `|Σ| = t2 + 1` (the sizes), one kernel evaluation of
`h` (the plan walk `planItemsR q S w0`, the openings `openItemsR q S w0`, in recursor form) gives the one-pass decision, `PlanOk` with the
walk's last entry, and Q_link's `qOkF` at the layout `ly`. The A twins instantiate it at their literals. -/
theorem planFacts_of {p q : Params} {S : List Item} {tbl : List (ℕ × ℕ)} {n t1 t2 : ℕ} {ly : Layout}
    (hS : schedule p = S) (hq : p = q) (hl : hashedLen p = t2 + 1)
    (h : let P := planItemsR q S w0
      let L : List PE := ⟨.q0, 7⟩ :: ⟨.fs 0, seedLenP q⟩ :: P.1
      let O := openItemsR q S w0
      passR (capLk tbl) n t1 t2 L tbl 0 0 0 = true ∧
      ((P.2.ok = true ∧ P.2.pend = 0 ∧ P.2.pcaps = []) ∧ P.2.i = n) ∧
      (decide (2 + fsCntR L 0 + (17 * nBlk (t2 + 1) - (t2 + 1) / 8) ≤ 2 ^ ly.aQ) &&
        decide ((t2 + 1) / 8 + 17 ≤ 2 ^ ly.m) && decide (17 * nBlk (t2 + 1) + 4 ≤ 2 ^ ly.m) &&
        decide (t2 + 1 < 2 ^ 64) &&
      (O.all fun o => decide (1 ≤ o.L.path) && decide (o.L.path < o.L.height) &&
        (pchunks o.L.t).all (fun c => decide (c.2 ≤ ly.K)) &&
        decide (offAtR L 1 o.ce / 8 + 1 + o.co / 8 + 4 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ ly.m) &&
        decide (o.L.row < 2 ^ 64)) &&
      decide ((O.map fun o => o.L.t).sum ≤ 2 ^ ly.pa)) = true) :
    passR (capLk tbl) n t1 t2 (plan p) tbl 0 0 0 = true ∧ (PlanOk p ∧ (planAll p).2.i = n) ∧
      qOkF p ly = true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [plan, planAll, hS, hq, planItems_eq_R]; exact h.1
  · rw [PlanOk, planAll, hS, hq, planItems_eq_R]; exact h.2.1
  · rw [qOkF, qlt_len, hl, lens, opens, plan, planAll, hS, hq, planItems_eq_R, openItems_eq_R, fsCnt_eq_R]
    simp only [offAt_eq_R]
    exact h.2.2

end Lvm.E2Q
