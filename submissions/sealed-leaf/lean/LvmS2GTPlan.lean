-- New for lvm2 S2GT (GT-L2, 2026-11-15): the plan's and Q_link's static facts at S2GT (`P20T`, `cfgG20`) that the
-- node soundness reads (S2GT-STMT 11): one decision each, as S2GF's `LvmE2QPlanF`/`LvmE2QNodeFacts`.
import LvmE2QNodeG
import LvmE2QInstT
import LvmS2GTSched

/-!
# The S2GT plan's facts

* **`passR_P20T`**: the one-pass decision at `P20T` (3,961 entries, `Σ clen = 305,984`, `Σ (40 + len) = 583,151`;
  the cap queries at entries 2, 1,316 and 2,735 [measured, a probe evaluation of the plan]).
* **`planSt_P20T`**: `PlanOk P20T`; **`streamOk_P20T`**, **`hQT20`** (`QOk P20T (lay cfgG20)`), **`planC_P20T`**.
* **`nodeStG20`**: `NodeStC cfgG20`, what `nodeSoundC` reads at S2GT.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay Lvm.PlanChk

/-- The cap entries at `P20T` and their lengths (the FS queries that absorb the caps). -/
def tblT20 : List (ℕ × ℕ) := [(2, 8224), (1316, 4176), (2735, 4176)]

/-! Proof help (GOLF2-K1): the QLT entries' count from one walk of the plan (`fsCnt`, GOLF-DEC3's `qlt_len` in
`LvmQAsmFactsL`, private there), and the plan's three decisions (`passR_P20T`, `planSt_P20T`, `hQT20`) in one kernel
evaluation of the plan walk over the literal `schedT20` (`planFactsT`), read off by rewriting with the equation
lemmas (39.3 → 17.5 M kernel heartbeats). -/

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

set_option maxRecDepth 200000 in
/-- **The plan's facts at `P20T`** in one kernel evaluation (the walk over the literal `schedT20`): the one-pass
decision, `PlanOk` and the walk's last entry, `qOkF` (the QLT count by `fsCnt`, `|Σ|` from `sizes_P20T`). -/
private theorem planFactsT :
    let S := schedT20
    let P := planItems P20T w0 S
    let L : List PE := ⟨.q0, 7⟩ :: ⟨.fs 0, seedLenP P20T⟩ :: P.1
    let O := openItems P20T w0 S
    let ly := lay cfgG20
    passR (capLk tblT20) 3961 305984 583151 L tblT20 0 0 0 = true ∧
    ((P.2.ok = true ∧ P.2.pend = 0 ∧ P.2.pcaps = []) ∧ P.2.i = 3961) ∧
    (decide (2 + fsCnt L 0 + (17 * nBlk 583152 - 583152 / 8) ≤ 2 ^ ly.aQ) && decide (583152 / 8 + 17 ≤ 2 ^ ly.m) &&
    decide (17 * nBlk 583152 + 4 ≤ 2 ^ ly.m) && decide (583152 < 2 ^ 64) &&
    (O.all fun o => decide (1 ≤ o.L.path) && decide (o.L.path < o.L.height) &&
      (pchunks o.L.t).all (fun c => decide (c.2 ≤ ly.K)) &&
      decide (offAt (L.map PE.len) 1 o.ce / 8 + 1 + o.co / 8 + 4 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ ly.m) &&
      decide (o.L.row < 2 ^ 64)) &&
    decide ((O.map fun o => o.L.t).sum ≤ 2 ^ ly.pa)) = true := by
  decide +kernel

/-- **The one decision at `P20T`.** -/
theorem passR_P20T : passR (capLk tblT20) 3961 305984 583151 (plan P20T) tblT20 0 0 0 = true := by
  rw [plan, planAll, schedule_P20T_lit]; exact planFactsT.1

/-- `PlanOk P20T` and the walk's last entry. -/
theorem planSt_P20T : PlanOk P20T ∧ (planAll P20T).2.i = 3961 := by
  rw [PlanOk, planAll, schedule_P20T_lit]; exact planFactsT.2.1

/-- **Q_link's stream facts at `P20T`.** -/
theorem streamOk_P20T : StreamOk P20T := streamOk_ofR passR_P20T sizes_P20T.1.2.2.1

/-- **Q_link's static checks at S2GT** (`qOkB` decided as `qOkF`, as `hQF20`). -/
theorem hQT20 : QOk P20T (lay cfgG20) :=
  qOk_of streamOk_P20T (by
    rw [← qOkF_eq, qOkF, qlt_len, sizes_P20T.1.2.2.1, lens, opens, plan, planAll, schedule_P20T_lit]
    exact planFactsT.2.2)

/-- S2GT's plan facts. -/
theorem planC_P20T : PlanC P20T :=
  planC_ofR passR_P20T planSt_P20T.1 (by decide) sizes_P20T.1.1 (by norm_num) sizes_P20T.1.2.2.1 (by norm_num)
    (by norm_num) rfl

/-- S2GT's node statics. -/
theorem nodeStG20 : NodeStC cfgG20 :=
  ⟨streamOk_P20T, hQT20, by decide,
    by rw [show cfgG20.p = P20T from rfl, sizes_P20T.1.2.2.2.2.1]; norm_num,
    by rw [show cfgG20.p = P20T from rfl, sizes_P20T.1.2.2.2.2.1, sizes_P20T.1.2.2.1]; rfl, rfl,
    by decide, by decide, planC_P20T⟩

end Lvm.E2Q
