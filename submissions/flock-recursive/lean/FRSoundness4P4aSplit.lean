-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5.1–§5.2, A.10 phase 2; stage P4a pass 5
-- (P4e)): 3.x's `stmt_split` (`FRSoundnessFrDF`) at S-E12a's node statement `StmtN4` (deviation D6).
import FRSoundness4P4aNS

/-!
# The front's parameters at revision 4.1 and the statement split

* **`front4 zw BgA`**: `Front4a` at S-E12a's maps (`zlm4 indN4 etN4`, the node's S2 weight
  `wN4` and truth `truthSN4`); **`front4_ok`**: its hypotheses from the witness's (`WitBits`,
  `ZwSame`) and the background's reads.
* **`Stmt4`**: revision 4.1's statement on a log: a node's S-E12a `StmtN4` on `f⁽⁰⁾` (with its L
  rows, indexed M rows and public digests as parameters), a segment's Z and S truths (what
  `segHolds_of_truths` reads).
* **`stmt_split4`**: a false statement is phase 2's doom `DF4a 2 = (BgA ∨ ¬ truthS) ∨ ¬ ZHolds`,
  when `BgA` carries the node's L rows, M rows and public cells (P4b's parts).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-- **The front's parameters at S-E12a's maps.** -/
noncomputable def front4 (zw : Wit) (BgA : Log → Log → Prop) : Front4a :=
  ⟨zlm4 N4c.indN4 N4c.etN4, zw, wN4, truthSN4 zw, BgA⟩

theorem front4_ok {zw : Wit} {BgA : Log → Log → Prop} (hb : WitBits zw) (hz : ZwSame zw)
    (hBg : T4.Reads 3 BgA) : (front4 zw BgA).OK :=
  ⟨zlm4_bits4, N4c.zlm4_indKinds, zlm4_etLocal _ _, hb, hz, wNLocal4, hBg⟩

/-- **Revision 4.1's statement on a log**: a node's `StmtN4` on `f⁽⁰⁾` (L rows `lr`, indexed M rows
`er`, public digests `pv es = (vk, c₁, c₂)`), a segment's Z and S truths. -/
def Stmt4 (R : P4b.FSrc) (zw : Wit) (lr : Rev4.NodeKind → List Circ.Row)
    (er : Rev4.NodeKind → List (ℕ × Circ.Row)) (pv : Log → Digest × Digest × Digest) (L es : Log) :
    Prop :=
  match kindOfC es with
  | .node ν => N4c.StmtN4 ν (lr ν) (er ν) (pv es).1 (pv es).2.1 (pv es).2.2 (R.fz L es)
  | .seg _ => ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es ∧ truthS (truthSN4 zw) zw L es

/-- The node's parts that phases 13 … 25 reduce (P4b's): the L rows, the M rows, the public cells. -/
def NodeRest4 (R : P4b.FSrc) (lr : Rev4.NodeKind → List Circ.Row)
    (er : Rev4.NodeKind → List (ℕ × Circ.Row)) (pv : Log → Digest × Digest × Digest) (ν : Rev4.NodeKind)
    (L es : Log) : Prop :=
  (∀ r ∈ lr ν, r.Holds (R.fz L es)) ∧ P4b.truthEI (er ν) (R.fz L es) ∧
    N4c.PubCells4 ν (R.fz L es) (pv es).1 (pv es).2.1 (pv es).2.2

/-- **A false statement is phase 2's doom** (3.x's `stmt_split`, D6): the node's Z and S parts
are `ZHolds`/`truthS` (`zHolds_iff_truthZ4`, `truthS4_iff`), its other parts are in `BgA`. -/
theorem stmt_split4 {R : P4b.FSrc} {zw : Wit} (hzw : WitOf R zw) (hb : WitBits zw)
    {BgA : Log → Log → Prop} {lr : Rev4.NodeKind → List Circ.Row}
    {er : Rev4.NodeKind → List (ℕ × Circ.Row)} {pv : Log → Digest × Digest × Digest} {L es : Log}
    (hBg : ∀ ν, kindOfC es = .node ν → ¬ NodeRest4 R lr er pv ν L es → BgA L es)
    (h : ¬ Stmt4 R zw lr er pv L es) : DF4a (front4 zw BgA) 2 L es := by
  show (BgA L es ∨ ¬ truthS (truthSN4 zw) zw L es) ∨ ¬ ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es
  unfold Stmt4 at h
  cases hk : kindOfC es with
  | seg σ =>
    rw [hk] at h
    rcases not_and_or.mp h with h | h
    · exact .inr h
    · exact .inl (.inr h)
  | node ν =>
    rw [hk] at h
    unfold N4c.StmtN4 at h
    have hS : truthS (truthSN4 zw) zw L es ↔ N4c.truthS4 ν (R.fz L es) := by
      rw [truthS4_iff hzw hk, truthS, hk]; rfl
    by_cases hZ : N4c.truthZ4 ν (R.fz L es)
    · by_cases hS' : N4c.truthS4 ν (R.fz L es)
      · exact .inl (.inl (hBg ν hk fun hr => h ⟨hZ, hS', hr⟩))
      · exact .inl (.inr (hS.not.mpr hS'))
    · exact .inr ((zHolds_iff_truthZ4 hzw hb hk).not.mpr hZ)

/-! ## Controls -/

/-- (+) On a segment the statement is its Z and S truths. -/
theorem stmt4_seg_iff {R : P4b.FSrc} {zw : Wit} {lr : Rev4.NodeKind → List Circ.Row}
    {er : Rev4.NodeKind → List (ℕ × Circ.Row)} {pv : Log → Digest × Digest × Digest} {L es : Log}
    {σ : Rev4.SegKind} (hk : kindOfC es = .seg σ) :
    Stmt4 R zw lr er pv L es ↔
      ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es ∧ truthS (truthSN4 zw) zw L es := by
  unfold Stmt4; rw [hk]

/-- (+) On a node the statement is S-E12a's `StmtN4`. -/
theorem stmt4_node_iff {R : P4b.FSrc} {zw : Wit} {lr : Rev4.NodeKind → List Circ.Row}
    {er : Rev4.NodeKind → List (ℕ × Circ.Row)} {pv : Log → Digest × Digest × Digest} {L es : Log}
    {ν : Rev4.NodeKind} (hk : kindOfC es = .node ν) :
    Stmt4 R zw lr er pv L es ↔
      N4c.StmtN4 ν (lr ν) (er ν) (pv es).1 (pv es).2.1 (pv es).2.2 (R.fz L es) := by
  unfold Stmt4; rw [hk]

/-- (−) A segment whose Z rows fail does not meet the statement, and is doomed at phase 2. -/
theorem not_stmt4_seg {R : P4b.FSrc} {zw : Wit} {lr : Rev4.NodeKind → List Circ.Row}
    {er : Rev4.NodeKind → List (ℕ × Circ.Row)} {pv : Log → Digest × Digest × Digest} {L es : Log}
    {σ : Rev4.SegKind} (hk : kindOfC es = .seg σ) (hz : ¬ ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es) :
    ¬ Stmt4 R zw lr er pv L es := fun h => hz ((stmt4_seg_iff hk).mp h).1

end FR.Snd.P4a
