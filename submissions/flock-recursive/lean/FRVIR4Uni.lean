-- New for `flock-recursive` (BLUEPRINT revision 4.3, changes 28, route (A); stage INT-8).
import FRVIR4Mux

/-!
# The group program read at an index is the kind's program (revision 4.3, route (A))

A node slot's rows certify a run of a group program (`progNodeGK cells`, `progSegG`) at the
selector index `ι` (S-E12c §1). Revision 4.3 makes the kinds of a group differ in kind tables only;
this module proves that **the group program read at `ι` is `gen4 (G ι)`'s program**, op for op:

* **`skeletonG_at`**: the group's skeleton read at `ι` (`Op.at h true ι`: tables at `ι`, the
  segment operand's `packFK` as `packF`) is `skeleton4 S (G ι)`'s ops, with the same context
  (registers, outputs); structural, every step definitional, generic in `S`, `G`, `ι`.
* **`progNodeGK_ops`**, **`progSegG_ops`**: the program's ops are skeleton, finals, `accept`, and
  each part read at `ι` (the finals with `Op.at h false ι`) is the kind's program's part
  (`progNode (nodeAt ι) (cells (nodeAt ι))`, `progSeg (segAt ι)`). The group programs contain no
  `hashStmt` (`noHash_*`, from two readings).
* **`progNodeGK_exec`**, **`progSegG_exec`**: the group program run at `ι` under `impl` is the kind's
  program run at its own table index (`p.tix`) under any `impl'` that reads at `p.tix` what `impl`
  reads at `ι` (`OpImpl.fixK`).
* **Controls**: the op counts are equal within each group (`progNodeGK_length`, `progSegG_length`),
  a reading that keeps a table differs from the kind's program (`at_ctl`), and the two `hashStmt`
  readings differ (`noHash_ctl`).
-/

namespace FR
namespace Rev4
open RecursionFast

/-! ## The skeleton's generators read at `ι` -/

section Skel
variable (h : Reg → Op) (pf : Bool) (ι : Kind)

theorem map_at_seedOpsG (G : Grp) (b : ℕ) : (seedOpsG G b).map (Op.at h pf ι) = seedOps4 (G ι) b := by
  simp only [seedOpsG, seedOps4, kt_eq]; rfl

theorem map_at_absorbOps (f o len st b : ℕ) :
    (absorbOps f o len st b).map (Op.at h pf ι) = absorbOps f o len st b := rfl

theorem map_at_stmtOps4 (p : KindP) (so msg b : ℕ) :
    (stmtOps4 p so msg b).map (Op.at h pf ι) = stmtOps4 p so msg b := by
  simp only [stmtOps4]; split <;> rfl

theorem stmtOps4_node {p p' : KindP} (hp : p.d.node = p'.d.node) : stmtOps4 p = stmtOps4 p' := by
  funext so msg b; simp only [stmtOps4, hp]

theorem map_at_lastOps (so b : ℕ) : (lastOps so b).map (Op.at h pf ι) = lastOps so b := by
  simp only [lastOps, List.map_append, List.map_flatMap]; rfl

theorem map_at_finalOps4 (S : Seq) (p : KindP) (fo b : ℕ) :
    (finalOps4 S p fo b).map (Op.at h pf ι) = finalOps4 S p fo b := rfl

theorem map_at_sqzCoordOps : ∀ k st b, (sqzCoordOps k st b).map (Op.at h pf ι) = sqzCoordOps k st b
  | 0, _, _ => rfl
  | k + 1, st, b => by rw [sqzCoordOps, List.map_append, map_at_sqzCoordOps k]; rfl

theorem map_at_sqzOps : ∀ k st b, (sqzOps k st b).map (Op.at h pf ι) = sqzOps k st b
  | 0, _, _ => rfl
  | k + 1, st, b => by rw [sqzOps, List.map_cons, map_at_sqzOps k]; rfl

theorem map_at_uniOps (f o st pt b : ℕ) : (uniOps f o st pt b).map (Op.at h pf ι) = uniOps f o st pt b := by
  simp only [uniOps, uniHead, uniElems, uniTail, List.map_append, List.map_map]; rfl

theorem map_at_initOps (init : Init) (f o : ℕ) (inK : Bool) (uni b : ℕ) :
    (initOps init f o inK uni b).1.map (Op.at h pf ι) = (initOps init f o inK uni b).1 := by
  cases init <;> simp only [initOps] <;> (try split) <;> rfl

theorem map_at_roundsOps (f o deg : ℕ) (inK : Bool) (real : KC ℕ) :
    ∀ n j st cl b, (roundsOps f o deg inK real n j st cl b).map (Op.at h pf ι) =
      roundsOps f o deg inK (fun _ => real ι) n j st cl b
  | 0, _, _, _, _ => rfl
  | n + 1, j, st, cl, b => by
    rw [roundsOps, roundsOps, List.map_append, map_at_roundsOps f o deg inK real n]
    congr 1
    cases inK
    · simp only [roundOpsF, Bool.false_eq_true, ite_false, List.map_append]; split <;> rfl
    · simp only [roundOpsK, ite_true]; rfl

theorem map_at_merkleOpsG (sib : Kind → ℕ) (i : ℕ) (j : Reg) :
    ∀ n hh cur so b, (merkleOpsG sib i j n hh cur so b).map (Op.at h pf ι) = merkleOps4 (sib ι) i j n hh cur so b
  | 0, _, _, _, _ => rfl
  | n + 1, hh, cur, so, b => by
    rw [merkleOpsG, merkleOps4, List.map_append, map_at_merkleOpsG sib i j n]
    simp only [kt_eq]; rfl

theorem map_at_posOpsG (S : Seq) (G : Grp) (i co so : ℕ) (ans : List Reg) (w : Reg) (p b : ℕ) :
    (posOpsG (S.lv i) (kt fun ι => S.lvK (G ι).d.m i) i co so ans w p b).map (Op.at h pf ι) =
      posOps4 S (G ι) i co so ans w p b := by
  simp only [posOpsG, posOps4, kt_eq, List.map_append, map_at_merkleOpsG]; rfl

end Skel

/-- **One phase of the group's skeleton read at `ι` is the phase of `gen4 (G ι)`**, with the same
context (the kinds of a group share their node flag). -/
theorem genPhaseG_at {h : Reg → Op} (hh : ∀ s, (h s).outs = 1) (S : Seq) (G : Grp) (ι : Kind)
    (hN : (G ι).d.node = G.rep.d.node) (n : ℕ) (ph : String × Sh) (c : GCtx) :
    (genPhaseG S G n ph c).1.map (Op.at h true ι) = (genPhase4 S (G ι) n ph c).1 ∧
      (genPhaseG S G n ph c).2 = (genPhase4 S (G ι) n ph c).2 := by
  have hst := stmtOps4_node hN.symm
  obtain ⟨name, sh⟩ := ph
  cases sh with
  | seed =>
    have e := map_at_seedOpsG h true ι G c.next
    simp only [genPhaseG, genPhase4]
    exact ⟨e, by rw [← e, opsOut_map_at hh]⟩
  | absorb f len =>
    simp only [genPhaseG, genPhase4, hN]
    split_ifs
    · have e : (absorbOps 0 (fieldOffOf S f + phaseOffOf S n f) len c.st c.next ++
          stmtOps4 G.rep (fieldOffOf S f + phaseOffOf S n f) c.next (c.next + 2)).map (Op.at h true ι) =
          absorbOps 0 (fieldOffOf S f + phaseOffOf S n f) len c.st c.next ++
          stmtOps4 (G ι) (fieldOffOf S f + phaseOffOf S n f) c.next (c.next + 2) := by
        rw [List.map_append, map_at_absorbOps, map_at_stmtOps4, hst]
      exact ⟨e, by rw [← e, opsOut_map_at hh]⟩
    · have e : (absorbOps 0 (fieldOffOf S f + phaseOffOf S n f) len c.st c.next ++
          stmtOps4 G.rep (fieldOffOf S f + phaseOffOf S n f) c.next (c.next + 2) ++
          lastOps (fieldOffOf S f + phaseOffOf S n f) (c.next + 2 + opsOut (stmtOps4 G.rep
            (fieldOffOf S f + phaseOffOf S n f) c.next (c.next + 2)))).map (Op.at h true ι) =
          absorbOps 0 (fieldOffOf S f + phaseOffOf S n f) len c.st c.next ++
          stmtOps4 (G ι) (fieldOffOf S f + phaseOffOf S n f) c.next (c.next + 2) ++
          lastOps (fieldOffOf S f + phaseOffOf S n f) (c.next + 2 + opsOut (stmtOps4 (G ι)
            (fieldOffOf S f + phaseOffOf S n f) c.next (c.next + 2))) := by
        rw [List.map_append, List.map_append, map_at_absorbOps, map_at_stmtOps4, map_at_lastOps, hst]
      exact ⟨e, by rw [← e, opsOut_map_at hh, hst]⟩
    · have e : (absorbOps 0 (fieldOffOf S f + phaseOffOf S n f) len c.st c.next ++
          finalOps4 S G.rep (fieldOffOf S f + phaseOffOf S n f) (c.next + 2)).map (Op.at h true ι) =
          absorbOps 0 (fieldOffOf S f + phaseOffOf S n f) len c.st c.next ++
          finalOps4 S (G ι) (fieldOffOf S f + phaseOffOf S n f) (c.next + 2) := rfl
      exact ⟨e, by rw [← e, opsOut_map_at hh]⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  | squeezes k ch =>
    cases ch <;> simp only [genPhaseG, genPhase4, List.map_append, List.map_cons, List.map_nil,
      map_at_sqzCoordOps, map_at_sqzOps] <;> trivial
  | uni f =>
    simp only [genPhaseG, genPhase4, hN]
    split_ifs
    · exact ⟨map_at_uniOps h true ι 0 _ c.st c.pt c.next, rfl⟩
    · have e : (segPtOpG S G c.outs :: uniOps 0 (fieldOffOf S f + phaseOffOf S n f) c.st c.next
          (c.next + 1)).map (Op.at h true ι) = segPtOp S (G ι) c.outs :: uniOps 0
          (fieldOffOf S f + phaseOffOf S n f) c.st c.next (c.next + 1) := by
        rw [List.map_cons, map_at_uniOps]; rfl
      exact ⟨e, by rw [← e, opsOut_map_at hh]⟩
  | rounds f k deg inK =>
    simp only [genPhaseG, genPhase4]
    have e : ((initOps (initClaim name) 0 (fieldOffOf S f + phaseOffOf S n f) inK c.uni c.next).1 ++
        roundsOps 0 (fieldOffOf S f + phaseOffOf S n f) deg inK (kt fun ι => realRounds (G ι) name k) k 0 c.st
          (initOps (initClaim name) 0 (fieldOffOf S f + phaseOffOf S n f) inK c.uni c.next).2
          (c.next + (initClaim name).width)).map (Op.at h true ι) =
        (initOps (initClaim name) 0 (fieldOffOf S f + phaseOffOf S n f) inK c.uni c.next).1 ++
        roundsOps 0 (fieldOffOf S f + phaseOffOf S n f) deg inK (fun _ => realRounds (G ι) name k) k 0 c.st
          (initOps (initClaim name) 0 (fieldOffOf S f + phaseOffOf S n f) inK c.uni c.next).2
          (c.next + (initClaim name).width) := by
      rw [List.map_append, map_at_initOps, map_at_roundsOps, kt_eq]
    exact ⟨e, by rw [← e, opsOut_map_at hh]⟩
  | queries i =>
    simp only [genPhaseG, genPhase4]
    have e : ([Op.packK c.foldR, Op.eqTableK c.next] ++ (List.range (S.lv i).t).flatMap fun q =>
        posOpsG (S.lv i) (kt fun ι => S.lvK (G ι).d.m i) i (fieldOffOf S fCols + phaseOffOf S n fCols)
          (fieldOffOf S fSibs + phaseOffOf S n fSibs) c.posAns
          (c.next + 1) q (c.next + 2 + posW4 S i * q)).map (Op.at h true ι) =
        [Op.packK c.foldR, Op.eqTableK c.next] ++ (List.range (S.lv i).t).flatMap fun q =>
        posOps4 S (G ι) i (fieldOffOf S fCols + phaseOffOf S n fCols)
          (fieldOffOf S fSibs + phaseOffOf S n fSibs) c.posAns
          (c.next + 1) q (c.next + 2 + posW4 S i * q) := by
      rw [List.map_append, List.map_flatMap]
      simp only [map_at_posOpsG]; rfl
    exact ⟨e, by rw [← e, opsOut_map_at hh]⟩

/-- **The group's skeleton read at `ι` is `skeleton4 S (G ι)`**, ops and context. -/
theorem skeletonG_at {h : Reg → Op} (hh : ∀ s, (h s).outs = 1) (S : Seq) (G : Grp) (ι : Kind)
    (hN : (G ι).d.node = G.rep.d.node) :
    (skeletonG S G).1.map (Op.at h true ι) = (skeleton4 S (G ι)).1 ∧ (skeletonG S G).2 = (skeleton4 S (G ι)).2 := by
  suffices ∀ ps n c, (genPhasesG S G ps n c).1.map (Op.at h true ι) = (genPhases4 S (G ι) ps n c).1 ∧
      (genPhasesG S G ps n c).2 = (genPhases4 S (G ι) ps n c).2 from this _ _ _
  intro ps
  induction ps with
  | nil => intro n c; exact ⟨rfl, rfl⟩
  | cons ph ps ih =>
    intro n c
    obtain ⟨h1, h2⟩ := genPhaseG_at hh S G ι hN n ph c
    simp only [genPhasesG, genPhases4, List.map_append, h1, h2]
    obtain ⟨i1, i2⟩ := ih (n + 1) (genPhase4 S (G ι) n ph c).2
    exact ⟨by rw [i1], i2⟩

/-! ## The group programs read at an index -/

theorem nodeGrp_node (ι : Kind) : (nodeGrp ι).d.node = nodeGrp.rep.d.node := by cases ι <;> rfl
theorem segGrp_node (ι : Kind) : (segGrp ι).d.node = segGrp.rep.d.node := by cases ι <;> rfl

/-- **Every index of the node group has index `L32`'s counts** (the kinds' cells of one length). -/
theorem nodeQ_counts (cells : NodeKind → List ℕ) (hl : ∀ κ, (cells κ).length = (cells .N4).length)
    (ι : Kind) : SameCounts (nodeQ cells .L32) (nodeQ cells ι) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  show (cells (nodeAt .L32)).length = (cells (nodeAt ι)).length
  rw [hl (nodeAt ι)]; rfl

theorem segQ_counts (ι : Kind) : SameCounts (segQ .L32) (segQ ι) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The kinds' tables are constant: read at their own index they are themselves. -/
theorem nodeQ_fix (cells : NodeKind → List ℕ) (ι : Kind) : finAt (nodeQ cells) ι = fun _ => nodeQ cells ι :=
  funext fun _ => fixKV_const _ ι (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem segQ_fix (ι : Kind) : finAt segQ ι = fun _ => segQ ι :=
  funext fun _ => fixKV_const _ ι (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

section Prog
variable {h : Reg → Op} (hh : ∀ s, (h s).outs = 1) (hr : ∀ S s, reloc S (h s) = h s)
include hh hr

/-- **The node group's finals read at `ι` are the finals of `nodeAt ι` with its cells.** -/
theorem nodeFin_at (cells : NodeKind → List ℕ) (hl : ∀ κ, (cells κ).length = (cells .N4).length) (ι : Kind)
    (outs : Array (List Reg)) (b : ℕ) :
    (finOps4F (nodeQ cells .L32) (nodeQ cells) outs b).map (Op.at h false ι) =
      finOps4 (nodeFinP (nodeAt ι) (cells (nodeAt ι))) outs b := by
  rw [finOps4F_eq, map_at_finOps4 hh ι _ _ rfl (hr _), nodeQ_fix, finOps4_counts (nodeQ_counts cells hl ι)]
  rfl

/-- **The segment group's finals read at `ι` are the finals of `segAt ι`.** -/
theorem segFin_at (ι : Kind) (outs : Array (List Reg)) (b : ℕ) :
    (finOps4F (segQ .L32) segQ outs b).map (Op.at h false ι) = finOps4 (segFinP (segAt ι)) outs b := by
  rw [finOps4F_eq, map_at_finOps4 hh ι _ _ rfl (hr _), segQ_fix, finOps4_counts (segQ_counts ι)]
  rfl

end Prog

/-- **`progNodeGK`'s parts**: skeleton, finals, `accept`. -/
theorem progNodeGK_ops (cells : NodeKind → List ℕ) : (progNodeGK cells).ops = (skeletonG seq4 nodeGrp).1 ++
    finOps4F (nodeQ cells .L32) (nodeQ cells) (skeletonG seq4 nodeGrp).2.outs (skeletonG seq4 nodeGrp).2.next ++
      [.accept] := rfl

theorem progSegG_ops : progSegG.ops = (skeletonG seq4 segGrp).1 ++
    finOps4F (segQ .L32) segQ (skeletonG seq4 segGrp).2.outs (skeletonG seq4 segGrp).2.next ++ [.accept] := rfl

/-- The relation of a group program's op and the kind program's (the skeleton read with `packF`, the
finals with `packFK`). -/
def UniRel (ι : Kind) (op op' : Op) : Prop :=
  op.isHash = false ∧ (op' = Op.at hKeep true ι op ∨ op' = Op.at hKeep false ι op)

theorem hKeep_outs (s : Reg) : (hKeep s).outs = 1 := rfl
theorem hDrop_outs (s : Reg) : (hDrop s).outs = 1 := rfl

/-- **A program of parts read at `ι`**: if the skeleton part read at `ι` (with `packF`) and the finals
part (with `packFK`) are the kind's, under both `hashStmt` readings, the programs are related op by
op. -/
theorem uniRel_of (ι : Kind) {A B A' B' : List Op}
    (hA : ∀ h : Reg → Op, (∀ s, (h s).outs = 1) → (∀ S s, reloc S (h s) = h s) → A.map (Op.at h true ι) = A')
    (hB : ∀ h : Reg → Op, (∀ s, (h s).outs = 1) → (∀ S s, reloc S (h s) = h s) → B.map (Op.at h false ι) = B') :
    List.Forall₂ (UniRel ι) (A ++ B ++ [.accept]) (A' ++ B' ++ [.accept]) := by
  have nA := noHash_of_at ((hA hKeep hKeep_outs fun _ _ => rfl).trans (hA hDrop hDrop_outs fun _ _ => rfl).symm)
  have nB := noHash_of_at ((hB hKeep hKeep_outs fun _ _ => rfl).trans (hB hDrop hDrop_outs fun _ _ => rfl).symm)
  rw [← hA hKeep hKeep_outs fun _ _ => rfl, ← hB hKeep hKeep_outs fun _ _ => rfl]
  refine forall₂_append (forall₂_append ((forall₂_at nA).imp fun _ _ r => ⟨r.1, .inl r.2⟩)
    ((forall₂_at nB).imp fun _ _ r => ⟨r.1, .inr r.2⟩)) (.cons ⟨rfl, .inl rfl⟩ .nil)

theorem exec_uni {impl impl' : OpImpl} {ι κ : Kind} (hI : impl'.fixK κ = impl.fixK ι) (inp : Input)
    {ops ops' : List Op} (hR : List.Forall₂ (UniRel ι) ops ops') (s : St) (tr : Trace) :
    exec impl ι inp ops s tr = exec impl' κ inp ops' s tr :=
  exec_forall₂ (fun op op' r regs => by
    rcases r with ⟨hn, rfl | rfl⟩ <;> exact evalOp_at hI _ _ inp regs op hn) hR s tr

theorem progNode_ops (κ : NodeKind) (c : List ℕ) : (progNode κ c).ops = (skeleton4 seq4 (.ofNode κ)).1 ++
    finOps4 (nodeFinP κ c) (skeleton4 seq4 (.ofNode κ)).2.outs (skeleton4 seq4 (.ofNode κ)).2.next ++ [.accept] := rfl

theorem progSeg_ops (κ : SegKind) : (progSeg κ).ops = (skeleton4 seq4 (.ofSeg κ)).1 ++
    finOps4 (segFinP κ) (skeleton4 seq4 (.ofSeg κ)).2.outs (skeleton4 seq4 (.ofSeg κ)).2.next ++ [.accept] := rfl

theorem nodeGrp_at (ι : Kind) : nodeGrp ι = .ofNode (nodeAt ι) := rfl
theorem segGrp_at (ι : Kind) : segGrp ι = .ofSeg (segAt ι) := rfl

/-- **The node group program at `ι` is the program of `nodeAt ι`, op for op.** -/
theorem progNodeGK_rel (cells : NodeKind → List ℕ) (hl : ∀ κ, (cells κ).length = (cells .N4).length)
    (ι : Kind) : List.Forall₂ (UniRel ι) (progNodeGK cells).ops (progNode (nodeAt ι) (cells (nodeAt ι))).ops := by
  have hsk := fun (h : Reg → Op) (hh : ∀ s, (h s).outs = 1) => skeletonG_at hh seq4 nodeGrp ι (nodeGrp_node ι)
  simp only [nodeGrp_at] at hsk
  rw [progNodeGK_ops, progNode_ops, (hsk hKeep hKeep_outs).2]
  exact uniRel_of ι (fun h hh _ => (hsk h hh).1)
    (fun h hh hr => nodeFin_at hh hr cells hl ι (skeleton4 seq4 (.ofNode (nodeAt ι))).2.outs
      (skeleton4 seq4 (.ofNode (nodeAt ι))).2.next)

/-- **The segment group program at `ι` is the program of `segAt ι`, op for op.** -/
theorem progSegG_rel (ι : Kind) : List.Forall₂ (UniRel ι) progSegG.ops (progSeg (segAt ι)).ops := by
  have hsk := fun (h : Reg → Op) (hh : ∀ s, (h s).outs = 1) => skeletonG_at hh seq4 segGrp ι (segGrp_node ι)
  simp only [segGrp_at] at hsk
  rw [progSegG_ops, progSeg_ops, (hsk hKeep hKeep_outs).2]
  exact uniRel_of ι (fun h hh _ => (hsk h hh).1)
    (fun h hh hr => segFin_at hh hr ι (skeleton4 seq4 (.ofSeg (segAt ι))).2.outs
      (skeleton4 seq4 (.ofSeg (segAt ι))).2.next)

/-- **The node group program run at `ι` is the kind's program run** at any kind `κ` (in `VnodeC`:
`(KindP.ofNode _).tix`) under any `impl'` that reads at `κ` what `impl` reads at `ι`. -/
theorem progNodeGK_exec (cells : NodeKind → List ℕ) (hl : ∀ κ, (cells κ).length = (cells .N4).length)
    {impl impl' : OpImpl} {ι κ : Kind} (hI : impl'.fixK κ = impl.fixK ι) (inp : Input) (s : St) (tr : Trace) :
    exec impl ι inp (progNodeGK cells).ops s tr = exec impl' κ inp (progNode (nodeAt ι) (cells (nodeAt ι))).ops s tr :=
  exec_uni hI inp (progNodeGK_rel cells hl ι) s tr

/-- **The segment group program run at `ι` is the kind's program run.** -/
theorem progSegG_exec {impl impl' : OpImpl} {ι κ : Kind} (hI : impl'.fixK κ = impl.fixK ι) (inp : Input)
    (s : St) (tr : Trace) : exec impl ι inp progSegG.ops s tr = exec impl' κ inp (progSeg (segAt ι)).ops s tr :=
  exec_uni hI inp (progSegG_rel ι) s tr

/-! ## Controls -/

/-- (+) **One op count per group**: the three kinds' programs have the group program's length (the
reading keeps the length), with the node kinds' own cells (`cells4`: nine each). -/
theorem progNodeGK_length (cells : NodeKind → List ℕ) (hl : ∀ κ, (cells κ).length = (cells .N4).length)
    (ι : Kind) : (progNode (nodeAt ι) (cells (nodeAt ι))).ops.length = (progNodeGK cells).ops.length :=
  (progNodeGK_rel cells hl ι).length_eq.symm

theorem progSegG_length (ι : Kind) : (progSeg (segAt ι)).ops.length = progSegG.ops.length :=
  (progSegG_rel ι).length_eq.symm

theorem node_lengths (cells : NodeKind → List ℕ) (hl : ∀ κ, (cells κ).length = (cells .N4).length) :
    (progNode .N2 (cells .N2)).ops.length = (progNode .N4 (cells .N4)).ops.length ∧
      (progNode .N8 (cells .N8)).ops.length = (progNode .N4 (cells .N4)).ops.length :=
  ⟨(progNodeGK_length cells hl .P30).trans (progNodeGK_length cells hl .L32).symm,
    (progNodeGK_length cells hl .N30).trans (progNodeGK_length cells hl .L32).symm⟩

theorem seg_lengths : (progSeg .L30).ops.length = (progSeg .L32).ops.length ∧
    (progSeg .L31).ops.length = (progSeg .L32).ops.length :=
  ⟨(progSegG_length .P30).trans (progSegG_length .L32).symm, (progSegG_length .N30).trans (progSegG_length .L32).symm⟩

/-- (−) **The index matters**: the node group's Lr point read at `L32` (`N4`: 17 coordinates) is not
the one read at `P30` (`N2`: 16), on any 17 coordinates. -/
theorem at_ctl (cells : NodeKind → List ℕ) (l : List Reg) (hl : 17 ≤ l.length) :
    Op.at hKeep false .L32 (.packFK fun κ => l.take (nodeQ cells κ).lrR) ≠
      Op.at hKeep false .P30 (.packFK fun κ => l.take (nodeQ cells κ).lrR) := by
  intro h
  simp only [Op.at, Bool.false_eq_true, ite_false, Op.packFK.injEq] at h
  have := congrArg List.length (congrFun h .L32)
  simp only [nodeQ, nodeFinP, nodeAt, NodeKind.dims, List.length_take] at this
  omega

/-- (−) **The two `hashStmt` readings differ**, so `noHash_of_at` is not vacuous. -/
theorem noHash_ctl (ι : Kind) : Op.at hKeep false ι (.hashStmt 0) ≠ Op.at hDrop false ι (.hashStmt 0) := by
  simp [Op.at]

end Rev4
end FR
