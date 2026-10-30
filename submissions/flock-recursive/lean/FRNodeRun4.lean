-- G6: this module also holds the former modules `FRVIR4Uni`, `FRNodeSound4`, `FRNodeRead4`, `FRNodeRead4W`, `FRNodeSound4R`, `FRNodeRows4Rep`, `FRNodeRows4RepS` (one section each, in import order).
import FRVIR4Mux
import FRNodeRows4Fit
import FRVerifierImplNode4F
import FRNodeReadCore

section G6_FRVIR4Uni

-- New for `flock-recursive` (BLUEPRINT revision 4.3, changes 28, route (A); stage INT-8).

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

theorem map_at_posOpsG (S : Seq) (G : Grp) (i co so dO : ℕ) (ans : List Reg) (w : Reg) (p b : ℕ) :
    (posOpsG (S.lv i) (kt fun ι => S.lvK (G ι).d.m i) i co so dO ans w p b).map (Op.at h pf ι) =
      posOps4 S (G ι) i co so dO ans w p b := by
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
          (fieldOffOf S fSibs + phaseOffOf S n fSibs) (dOff4 S i) c.posAns
          (c.next + 1) q (c.next + 2 + posW4 S i * q)).map (Op.at h true ι) =
        [Op.packK c.foldR, Op.eqTableK c.next] ++ (List.range (S.lv i).t).flatMap fun q =>
        posOps4 S (G ι) i (fieldOffOf S fCols + phaseOffOf S n fCols)
          (fieldOffOf S fSibs + phaseOffOf S n fSibs) (dOff4 S i) c.posAns
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
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  show (cells (nodeAt .L32)).length = (cells (nodeAt ι)).length
  rw [hl (nodeAt ι)]; rfl

theorem segQ_counts (ι : Kind) : SameCounts (segQ .L32) (segQ ι) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

end G6_FRVIR4Uni

section G6_FRNodeSound4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.3 `node_sound`, §4.4; stage S-N2, residual 3 of
-- `ks_rev4F`). The 3.x analogue is `FRNodeSoundA` (`SlotRest`, `slotHolds_of`).

/-!
# The slot interface of the revision 4.1 node circuit (`SlotIface4` at `lRows4`, `nodeIRows4`)

S-E12a's `N4c.SlotIface4` asks, per verifier slot `v` of a node of kind `κ`, for three predicates
(`imp`, `rep`, `tpl`), the kind selectors (`selN`, `selS`), and the soundness of the slot under
them. This module instantiates it at the compiled rows of S-E12b … S-E12f.

* **The rows.** Slot `v`'s rows are its prototype's (`protoOf κ v`: `0` the previous-node group,
  `1` the segment group) moved into region `v` (`slotRows4`). On the slot's assignment
  `slotAsg κ v w` they are the prototype's compiled rows and template rows (`slotIRows_snd`,
  `slotRows_hold`): **`tpl`** (`SlotRows`) is that both hold, and it follows from the node's M rows
  (`tpl_of_rows`).
* **The selectors.** `selN κ v w κ'`: `v` is the previous node's slot and its selector copies pick
  the index `ι` of the node group with `nodeAt ι = κ'`; `selS` likewise for the segment group
  (`segAt`). The copies are linked to L's selector bits and made one-hot by `linkRows4`
  (S-E12c's `selP_sel`, `selA_sel`).
* **`imp`** (`SlotImp`) is *exactly* what `protoCS_soundAt` asks beyond the rows, at every index
  the selectors may pick: the run of the group program at that index on the slot's input and trace
  exists and uses the trace up (`exec … = some (s, [])`), the auxiliary cells hold their registers'
  bits and field elements, every import register's cells hold its value, every foreign flag holds;
  and the statement fact `stmtOk4` that `VsegC`/`VnodeC` check after the run (INT-8). **No row of
  `nodeIRows4` or `lRows4` binds any of these** (the pack map, the replay `R` and the WOTS rows are
  not built): they are the node circuit's soundness gap (`S-N2-RESULT.md`).
* **`rep`** is `True`: the circuit has no replay `R`; the values it would replay are import
  registers, so they sit in `imp`.
* **`soundN`/`soundS`**: `protoCS_soundAt` at the slot's assignment, under the kind-blind ops
  `implP` (the kind's ops read at its table's kind, `OpImpl.fixK`), then INT-8's
  `progNodeGK_exec`/`progSegG_exec` (the group program at index `ι` runs as the kind's program),
  then `runStmt_iff`.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## The slot's rows -/

theorem map_snd_zipIdx_map {α β : Type*} (l : List α) (f : α × ℕ → ℕ) (g : α → β) :
    (l.zipIdx.map fun p => (f p, g p.1)).map Prod.snd = l.map g := by
  rw [List.map_map]
  show (l.zipIdx.map (g ∘ Prod.fst)) = _
  rw [← List.map_map, List.zipIdx_map_fst 0 l]

/-- An instance's indexed rows are its template rows. -/
theorem tinIRows_snd (L : TLay) (one : Lin) (off : ℕ) (t : Tpl.TKey × ℕ × List Lin) :
    (tinIRows L one off t).map Prod.snd = Tpl.instRows L.ctx one t := by
  have h : (tRows t.1).map (Tpl.instRowA one t.2.2.toArray (L.cb t.1 t.2.1)) = Tpl.instRows L.ctx one t := by
    rw [tRows_eq, show Tpl.instRowA one t.2.2.toArray (L.cb t.1 t.2.1) = Tpl.instRow one t.2.2 (L.cb t.1 t.2.1)
      from funext (Tpl.instRowA_eq one t.2.2 _)]; rfl
  unfold tinIRows
  split <;> rw [map_snd_zipIdx_map, h]

/-- **A slot's indexed rows are its compiled rows, then its template rows.** -/
theorem slotIRows_snd (L : TLay) (one : Lin) (off : ℕ) (cs : CS) :
    (slotIRows L one off cs).map Prod.snd = cs.rowList ++ cs.tplRows L.ctx one := by
  rw [slotIRows, List.map_append, CS.tplRows, List.map_flatMap]
  congr 1
  · exact (map_snd_zipIdx_map cs.rowList (fun p => off + p.2) id).trans (List.map_id _)
  · exact congrArg (List.flatMap · cs.tins) (funext fun t => tinIRows_snd L one off t)

/-- **Slot `v`'s rows**: its prototype's compiled rows and template rows hold at the slot's
assignment. -/
def SlotRows (κ : NodeKind) (v : ℕ) (w : Asg) : Prop :=
  (∀ r ∈ (protoCS (protoOf κ v)).rows, r.Holds (slotAsg κ v w)) ∧
    ∀ r ∈ (protoCS (protoOf κ v)).tplRows (protoLay (protoOf κ v)).ctx (protoP (protoOf κ v)).one,
      r.Holds (slotAsg κ v w)

/-- **The node's M rows give every slot's rows** (when the prototypes fit). -/
theorem slotRows_hold {κ : NodeKind} {v : ℕ} {w : Asg} (hF : ProtoFit) (hv : v < κ.vslots)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) : SlotRows κ v w := by
  have key : ∀ r ∈ (protoCS (protoOf κ v)).rowList ++
      (protoCS (protoOf κ v)).tplRows (protoLay (protoOf κ v)).ctx (protoP (protoOf κ v)).one,
      r.Holds (slotAsg κ v w) := by
    intro r hr
    rw [← slotIRows_snd] at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    have hm : (mvC (protoOf κ v) v p.1,
        rowMapC (· + κ.oneCell) (rowMapC (mvC (protoOf κ v) v) p.2)) ∈ nodeIRows4 κ := by
      refine mem_node_slot hF hv ?_
      simp only [slotRows4, absRows4, mvRows, List.map_map]
      exact List.mem_map.2 ⟨p, hp, rfl⟩
    have := hE _ hm
    rw [holds_rowMapC, holds_rowMapC] at this
    exact this
  refine ⟨fun r hr => key r (List.mem_append_left _ ?_), fun r hr => key r (List.mem_append_right _ hr)⟩
  simpa [CS.rowList] using hr

/-- **`tpl` from the statement's rows**: if the prototypes do not fit, the M rows are the rejecting
row `one · one = 0`, which fails at `one = 1`. -/
theorem slotRows_of {κ : NodeKind} {v : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (hv : v < κ.vslots)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) : SlotRows κ v w := by
  by_cases hF : ProtoFit
  · exact slotRows_hold hF hv hE
  · refine absurd (fun p hp => hE p ?_) (rejectRows_ctl κ w hone)
    rw [nodeIRows4, if_neg hF]; exact hp

/-! ## The ops a slot runs under -/

theorem implTF_fixK {F : TFilt} {impl : OpImpl} (h : ImplTF F impl) (κ : Kind) :
    ImplTF F (impl.fixK κ) := fun k hk => by
  have h' := h k hk
  cases k <;> simp only [KeyImpl, OpImpl.fixK] at h' ⊢ <;> first | exact h' | exact fun _ => h' κ | trivial

theorem routeOk_fixK {R : ShR} {impl : OpImpl} {κ : Kind} (h : RouteOk R impl κ) (κ' : Kind) :
    RouteOk R (impl.fixK κ') κ := by
  cases R <;> exact h

theorem implTF_implSeg {impl₀ : OpImpl} (hT : ImplT impl₀) : ImplTF keys41 (implSeg impl₀) :=
  fun k hk => by
    have h := hT.toF keys41 k hk
    cases k
    case shiftMask => exact absurd hk Bool.false_ne_true
    all_goals (simp only [KeyImpl, implSeg] at h ⊢; try first | exact h | exact fun _ => trivial)

/-- **The ops of prototype `π`'s run at index `ι`**: the kind's ops (`implN4F base (nodeAt ι)`, a
node; `implSeg impl₀`, a segment), read at the kind table's kind (`N30` for a node, `L32` for a
segment, the programs' `tix`), so that they do not read the run's index. -/
def implP (impl₀ : OpImpl) (base : NodeKind → OpImpl) (π : ℕ) (ι : Kind) : OpImpl :=
  if π = 0 then (NI4F.implN4F base (nodeAt ι)).fixK .N30 else (implSeg impl₀).fixK .L32

/-- The child kind prototype `π` replays at index `ι`. -/
def kindP (π : ℕ) (ι : Kind) : KindP := if π = 0 then .ofNode (nodeAt ι) else .ofSeg (segAt ι)

theorem nodeOf_eq (ι : Kind) : nodeOf ι = nodeAt ι := by cases ι <;> rfl

theorem implTF_implP {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) (π : ℕ) (ι : Kind) : ImplTF (protoF π) (implP impl₀ base π ι) := by
  unfold implP; split_ifs
  · exact implTF_fixK (NI4F.implTF_implN4F hT _) _
  · exact implTF_fixK (implTF_implSeg hT₀) _

theorem routeOk_implP (impl₀ : OpImpl) (base : NodeKind → OpImpl) {π : ℕ} (hπ : π ≤ 1) (ι : Kind) :
    RouteOk (protoR π) (implP impl₀ base π ι) ι := by
  unfold implP; split_ifs with h
  · subst h; exact routeOk_fixK (nodeOf_eq ι ▸ NI4F.routeOk_implN4F base ι) _
  · obtain rfl : π = 1 := by omega
    exact routeOk_fixK (routeOk_implSeg impl₀ ι) _

/-! ## The slot's run (`imp`) -/

/-- **The run-dependent facts of `protoCS_soundAt`** at prototype `π`, index `ι`, ops `impl`: the run
exists and uses the trace up, and the auxiliary, import and foreign facts hold at `w`. -/
def SlotRun (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) (tr : Trace) (w : Asg) : Prop :=
  ∃ s : St, exec impl ι inp (protoProg π).ops St.init tr = some (s, []) ∧
    (∀ a ∈ (protoCS π).aux, a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)) ∧
    (∀ i ∈ (protoCS π).imp, RepS w ((protoCS π).slot i) (rd s.regs i)) ∧
    (∀ p ∈ (protoCS π).fors, flagOf impl ι inp (s.regs.extract 0 p.2) p.1 = true)

/-- **Slot `v`'s imports** (the instance's `imp`): at every index its selectors may pick, the run
facts (`SlotRun`) at the slot's assignment and the statement fact. -/
def SlotImp (impl₀ : OpImpl) (base : NodeKind → OpImpl) (κ : NodeKind) (v : ℕ) (w : Asg) (inp : Input)
    (tr : Trace) : Prop :=
  ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
    SlotRun (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι inp tr (slotAsg κ v w) ∧
      stmtOk4 seq4 (kindP (protoOf κ v) ι) inp = true

/-- **The selectors**: the previous node's slot picks the node group's index of `κ'`. -/
def SelN (κ : NodeKind) (v : ℕ) (w : Asg) (κ' : NodeKind) : Prop :=
  isPrevSlot κ v = true ∧ ∃ ι, nodeAt ι = κ' ∧ SelOk (slotAsg κ v w) (protoP 0) ι

/-- A segment slot picks the segment group's index of `κ'`. -/
def SelS (κ : NodeKind) (v : ℕ) (w : Asg) (κ' : SegKind) : Prop :=
  isPrevSlot κ v = false ∧ ∃ ι, segAt ι = κ' ∧ SelOk (slotAsg κ v w) (protoP 1) ι

theorem protoOf_prev {κ : NodeKind} {v : ℕ} (h : isPrevSlot κ v = true) : protoOf κ v = 0 := by
  simp [protoOf, h]

theorem protoOf_seg {κ : NodeKind} {v : ℕ} (h : isPrevSlot κ v = false) : protoOf κ v = 1 := by
  simp [protoOf, h]

/-- The node programs' kind table index is `N30`, the segments' `L32`. -/
theorem kindOn_node (κ : NodeKind) (c : List ℕ) (inp : Input) : (progNode κ c).kindOn inp = .N30 := rfl
theorem kindOn_seg (κ : SegKind) (inp : Input) : (progSeg κ).kindOn inp = .L32 := rfl

theorem fixK_fixK (impl : OpImpl) (κ ι : Kind) : (impl.fixK κ).fixK ι = impl.fixK κ := rfl

theorem cells4_len (κ : NodeKind) : (N4c.cells4 κ).length = (N4c.cells4 .N4).length := by
  rw [(N4c.hcells4 κ).1, (N4c.hcells4 .N4).1]

/-- **A slot's soundness at index `ι`**: rows, selectors and the run facts give an accepting run of
the group program at `ι` under `implP`. -/
theorem slot_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) {κ : NodeKind} {v : ℕ} {w : Asg} {ι : Kind} {inp : Input} {tr : Trace}
    (hS : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι) (hR : SlotRows κ v w)
    (hI : SlotRun (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι inp tr (slotAsg κ v w)) :
    ∃ s : St, exec (implP impl₀ base (protoOf κ v) ι) ι inp (protoProg (protoOf κ v)).ops St.init tr =
      some (s, []) ∧ s.ok = true := by
  obtain ⟨s, he, hx, hi, hf⟩ := hI
  exact ⟨s, he, (protoCS_soundAt (protoOf κ v) (implTF_implP hT₀ hT _ ι)
    (routeOk_implP impl₀ base (protoOf_le' κ v) ι) hS he hR.1 hR.2 hx hi hf).1⟩

/-- **The slot interface at the 4.1 node rows** (`lRows4`, `nodeIRows4`), for bases meeting
`ImplT` (the templates' ops). -/
noncomputable def I4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) :
    N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) where
  lrows := lRows4
  irows := nodeIRows4
  imp κ v w inp tr := SlotImp impl₀ base κ v w inp tr
  rep _ _ _ _ _ := True
  tpl := SlotRows
  selN := SelN
  selS := SelS
  soundN κ v w inp tr κ' _ _ hsel himp _ htpl := by
    obtain ⟨hp, ι, rfl, hS⟩ := hsel
    have h0 := protoOf_prev hp
    replace hS : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι := by rw [h0]; exact hS
    obtain ⟨hrun, hst⟩ := himp ι hS
    obtain ⟨s, he, hok⟩ := slot_ok hT₀ hT hS htpl hrun
    simp only [h0, implP, kindP, ite_true] at he hst
    rw [show protoProg 0 = progNodeGK N4c.cells4 from rfl,
      progNodeGK_exec N4c.cells4 cells4_len (impl' := NI4F.implN4F base (nodeAt ι)) (κ := .N30)
        (fixK_fixK _ _ _).symm] at he
    obtain ⟨vk, c, π⟩ := inp
    rw [VnodeC, runStmt_iff, runSeq_runIR, semIR, kindOn_node, he]
    exact ⟨by simp [hok], hst⟩
  soundS κ v w inp tr κ' _ _ hsel himp _ htpl := by
    obtain ⟨hp, ι, rfl, hS⟩ := hsel
    have h1 := protoOf_seg hp
    replace hS : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι := by rw [h1]; exact hS
    obtain ⟨hrun, hst⟩ := himp ι hS
    obtain ⟨s, he, hok⟩ := slot_ok hT₀ hT hS htpl hrun
    simp only [h1, implP, kindP, one_ne_zero, if_false] at he hst
    rw [show protoProg 1 = progSegG from rfl,
      progSegG_exec (impl' := implSeg impl₀) (κ := .L32) (fixK_fixK _ _ _).symm] at he
    obtain ⟨vk, c, π⟩ := inp
    rw [VsegC, runStmt_iff, runSeq_runIR, semIR, kindOn_seg, he]
    exact ⟨by simp [hok], hst⟩

theorem I4_rows (impl₀ : OpImpl) (base : NodeKind → OpImpl) (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) :
    (I4 impl₀ base hT₀ hT).lrows = lRows4 ∧ (I4 impl₀ base hT₀ hT).irows = nodeIRows4 := ⟨rfl, rfl⟩

end N4s
end FR

end G6_FRNodeSound4

section G6_FRNodeRead4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.3, A.5, A.7; R-4-m2; stage S-N2: S-E12a's D6,
-- the concrete `N4c.Read4`). The 3.x analogue is `FRNodeRead` (`readTrace`, `readSig`, `readSigned`).

/-!
# The revision 4.1 node's reader: its children read off `f⁽⁰⁾`

`rd4 pf : N4c.Read4` reads a node's signed children and its verifier slots' inputs from the
committed witness `w`:

* **Each aggregate's segment count** `kAct κ a w` is the circuit's: the number of its sub-slots
  whose activity `S_σ = Σ_ι s′_ι` is `1`, counted up to the first inactive one (`Nat.find`). With
  the activity rows (S-E12c) this is S-E12c's `ActK` (`actK_kAct`): exactly the sub-slots `i < k`
  are active.
* **The traces** are read off H, as 3.x's `readTrace`: signed child `σ`'s chain hashes the stream
  `chainBytes4 κ σ k w` (S-E12a), and segment `i`'s trace is the item sequence `itemsOf seq4` read
  from stream offset `1 + i·strideB` (`segTr`; revision 4.4.1, R-A′: `strideB = segB − 1 + 129`, a
  trace and a spacer entry). A previous node's is segment 0 of its stream. An aggregate's trace is
  `V_A`'s: its active sub-slots' traces in order with the spacer entry `(spacerQ, a_i)` before
  sub-slot `i ≥ 1`, its answer `a_i` read off the stream (`spAns`, at the spacer's offset
  `i·strideB − 128`); its query is the constant `spacerQ`.
* **The proofs.** A slot's proof is `pf` of its trace (`pf`: the child proof its trace carries,
  A.5; for `seq4` this is S-H4's reassembly, a parameter here), fitted to `piSizeOf seq4` bytes.
  An aggregate's `π_A` is `hdrA = 'A' ‖ k ‖ 0⁶ ‖ enc64 n ‖ e` followed by its active sub-slots'
  proofs, with `(e, n)` read off its statement block `hashA` (`tagLeaf ‖ e ‖ enc64 n`, D2).
* **The signatures** are read off L as 3.x's `readSig`, at signed child `σ`'s `2^14` stride.

The reader fixes the format of what it reads (`π_A`'s header, the slot proofs' size), so
`NodeResid4`'s `aggFmt`, `aggTr`, `kOk` and `slotP` hold of it by construction
(`FRNodeSound4R`). What it does *not* fix (the children's kind bytes, that the stream is a trace's
encoding, the aggregate checks, the signature) is what the circuit must bind.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## The segment counts -/

/-- **Aggregate `a`'s segment count**: its first inactive sub-slot (or `maxK`). -/
noncomputable def kAct (κ : NodeKind) (a : ℕ) (w : Asg) : ℕ :=
  open Classical in
  Nat.find (⟨κ.maxK, Or.inl rfl⟩ : ∃ i, i = κ.maxK ∨ (selSum κ (N4c.sub κ a i)).ev w ≠ 1)

theorem kAct_le (κ : NodeKind) (a : ℕ) (w : Asg) : kAct κ a w ≤ κ.maxK := by
  classical
  exact Nat.find_min' _ (Or.inl rfl)

/-! ## The traces, proofs and signatures -/

/-- Segment `i`'s trace in signed child `σ`'s stream (`k` segments): `seq4`'s items from offset
`1 + i·strideB` (R-A′). -/
noncomputable def segTr (κ : NodeKind) (σ k i : ℕ) (w : Asg) : Trace :=
  Read.readItems (N4c.chainBytes4 κ σ k w) (1 + i * N4c.strideB) (itemsOf seq4)

/-- **The spacer's item** (`absorbQ 0³² 0⁴⁹`: an absorb of 49 bytes, 129 stream bytes). -/
def spItem : Item := .absorb 49

/-- The answer of the entry at offset `o` of the stream `B`, read as a spacer entry. -/
def spAnsB (B : List UInt8) (o : ℕ) : Digest := (Read.entryAt B o spItem).2

/-- **Spacer `i`'s answer** (`1 ≤ i < k`) in signed child `σ`'s stream: the last 32 bytes of the
spacer's entry at offset `i·strideB − 128` (before segment `i`). -/
noncomputable def spAns (κ : NodeKind) (σ k : ℕ) (w : Asg) (i : ℕ) : Digest :=
  spAnsB (N4c.chainBytes4 κ σ k w) (i * N4c.strideB - 128)

/-- The aggregate a segment slot belongs to. -/
def slotA (κ : NodeKind) (v : ℕ) : ℕ := if κ.hasPrev then 0 else v / 4

/-- **Slot `v`'s trace**: the previous node's stream, or its sub-slot's segment of its aggregate's. -/
noncomputable def slotTr4 (κ : NodeKind) (v : ℕ) (w : Asg) : Trace :=
  if isPrevSlot κ v then segTr κ 0 0 0 w
  else segTr κ (N4c.aggChild κ (slotA κ v)) (kAct κ (slotA κ v) w) (subIx κ v) w

/-- `b` padded with zeros or cut to `n` bytes. -/
def fitL (n : ℕ) (b : List UInt8) : List UInt8 := (b ++ List.replicate n 0).take n

theorem fitL_length (n : ℕ) (b : List UInt8) : (fitL n b).length = n := by
  simp [fitL]

/-- **Slot `v`'s proof bytes**: the proof its trace carries (`pf`), at `piSizeOf seq4` bytes. -/
noncomputable def slotPf (pf : Trace → Proof) (κ : NodeKind) (v : ℕ) (w : Asg) : List UInt8 :=
  fitL (piSizeOf seq4) (pf (slotTr4 κ v w)).data.toList

/-- Aggregate `a`'s statement block's message (`tagLeaf ‖ e ‖ enc64 n`, 41 bytes). -/
noncomputable def hA (κ : NodeKind) (a : ℕ) (w : Asg) : List UInt8 :=
  Stream.streamBytes (fun _ => N4c.bitsB4 w (N4c.cAB κ a)) 41

/-- The chain end `e` and the length `n` that aggregate `a`'s statement block hashes. -/
noncomputable def hAe (κ : NodeKind) (a : ℕ) (w : Asg) : Digest := Vector.ofFn fun i : Fin 32 => (hA κ a w).getD (1 + i) 0
noncomputable def hAn (κ : NodeKind) (a : ℕ) (w : Asg) : ℕ :=
  ((List.range 8).map fun i => ((hA κ a w).getD (33 + i) 0).toNat * 256 ^ i).sum

/-- **`π_A`**: `hdrA` with the circuit's `k`, then the active sub-slots' proofs. -/
noncomputable def aggPf (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) : Proof :=
  ⟨(aggHdr (kAct κ a w) (hAn κ a w) (hAe κ a w) ++
    ((List.range (kAct κ a w)).map fun i => slotPf pf κ (N4c.sub κ a i) w).flatten).toArray⟩

/-- Signed child `σ`'s L element `j` (its `2^14` stride, A.7). -/
def sigCell (κ : NodeKind) (σ j : ℕ) : ℕ := κ.lBase * 128 + σ * 2 ^ 14 + j

/-- **Signed child `σ`'s signature** (3.x's `readSig` at its stride: `idx`, the chain values, the
path). -/
def readSig4 (κ : NodeKind) (σ : ℕ) (w : Asg) : Sig where
  idx := (w (sigCell κ σ 0)).c₀.val.toNat
  ots := (List.range wotsLen).map fun j => Read.digestOf w (sigCell κ σ (1 + 2 * j)) (sigCell κ σ (2 + 2 * j))
  path := (List.range sigHeight).map fun t =>
    Read.digestOf w (sigCell κ σ (1 + 2 * wotsLen + 2 * t)) (sigCell κ σ (2 + 2 * wotsLen + 2 * t))

/-- **Signed child `σ`**: an aggregate's `π_A`, its sub-slots' traces in order with the spacer
entries between them (`V_A`'s trace, `FRAgg.aggTrace`); a previous node's
slot-0 proof and trace; the signature. -/
noncomputable def sgn4 (pf : Trace → Proof) (κ : NodeKind) (σ : ℕ) (w : Asg) : Signed :=
  if N4c.isAgg κ σ then
    ⟨aggPf pf κ (N4c.aggOf κ σ) w,
      aggTrace (spAns κ σ (kAct κ (N4c.aggOf κ σ) w) w)
        ((List.range (kAct κ (N4c.aggOf κ σ) w)).map fun i => slotTr4 κ (N4c.sub κ (N4c.aggOf κ σ) i) w),
      readSig4 κ σ w⟩
  else ⟨⟨(slotPf pf κ 0 w).toArray⟩, slotTr4 κ 0 w, readSig4 κ σ w⟩

/-- **The reader** (S-E12a's D6) with the proof decoder `pf`. -/
noncomputable def rd4 (pf : Trace → Proof) : N4c.Read4 where
  sgn := sgn4 pf
  slotπ κ v w := ⟨(slotPf pf κ v w).toArray⟩
  slotTr := slotTr4

/-! ## Facts -/

theorem byteAt_mk (l : List UInt8) (i : ℕ) : byteAt ⟨l.toArray⟩ i = l.getD i 0 := by
  unfold byteAt
  split_ifs with h
  · simp only [ByteArray.size, List.size_toArray] at h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    rfl
  · simp only [ByteArray.size, List.size_toArray, not_lt] at h
    simp [List.getElem?_eq_none h]

theorem aggHdr_length (k n : ℕ) (e : Digest) : (aggHdr k n e).length = 48 := by
  simp [aggHdr, enc64_length]

theorem sgn4_agg (pf : Trace → Proof) (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) (w : Asg) :
    sgn4 pf κ (N4c.aggChild κ a) w =
      ⟨aggPf pf κ a w, aggTrace (spAns κ (N4c.aggChild κ a) (kAct κ a w) w)
          ((List.range (kAct κ a w)).map fun i => slotTr4 κ (N4c.sub κ a i) w),
        readSig4 κ (N4c.aggChild κ a) w⟩ := by
  rw [sgn4, if_pos (N4c.isAgg_aggChild κ a), N4c.aggOf_aggChild κ ha]

/-- **The header's `k` is the circuit's.** -/
theorem kA_rd4 (pf : Trace → Proof) (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) (w : Asg) :
    N4c.kA (rd4 pf) κ w a = kAct κ a w := by
  have hk : kAct κ a w < 256 := lt_of_le_of_lt (kAct_le κ a w) (by cases κ <;> decide)
  simp only [N4c.kA, rd4, sgn4_agg pf κ ha, aggPf, byteAt_mk, aggHdr, List.cons_append,
    List.getD_cons_succ, List.getD_cons_zero]
  simp [Nat.toUInt8, UInt8.toNat_ofNat, Nat.mod_eq_of_lt hk]

end N4s
end FR

end G6_FRNodeRead4

section G6_FRNodeRead4W

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.5, A.7; stage S-N2): when the reader's traces
-- are the hashed stream. The 3.x analogue is `FRNodeRead.readTrace_of_stream` (the converse).

/-!
# A well-formed stream is the encoding of the trace the reader reads off it

The reader `rd4` reads signed child `σ`'s trace off its stream `B = chainBytes4 κ σ k w` at fixed
offsets (`segTr`). The query and answer bytes are whatever `B` holds; the stream is the trace's
encoding `0x54 ‖ traceBytes tr` iff its **constant bytes** are right: the tag `0x54` at byte 0 and,
at each item's offset, the 8-byte length word `enc64 |q|` (`WfAt`). **`chainMsg_of_wf`**: on such a
stream, `NodeResid4.chainMsg` holds for the reader. This reduces S-E12a's `chainMsg` to facts at
public positions of H.
-/

namespace FR
namespace N4s
open RecursionFast Rev4

/-- **The length words of `its` from offset `o`** (each item's 8 bytes are `enc64` of its query
length). -/
def WfAt (B : List UInt8) : ℕ → List Item → Prop
  | _, [] => True
  | o, it :: its => (B.drop o).take 8 = enc64 it.qlen ∧ WfAt B (o + it.slen) its

/-- The bytes `its` take. -/
def slenS (its : List Item) : ℕ := (its.map Item.slen).sum

theorem entry_bytes {B : List UInt8} {o : ℕ} {it : Item} (hl : o + it.slen ≤ B.length)
    (hw : (B.drop o).take 8 = enc64 it.qlen) :
    (B.drop o).take it.slen = enc64 (Read.entryAt B o it).1.size ++ (Read.entryAt B o it).1.data.toList ++
      (Read.entryAt B o it).2.toList := by
  have hs : it.slen = 8 + it.qlen + 32 := rfl
  have hq : (Read.entryAt B o it).1.size = it.qlen := by
    show ((B.drop (o + 8)).take it.qlen).toArray.size = _
    rw [List.size_toArray, List.length_take, List.length_drop]; omega
  have h1 : (Read.entryAt B o it).1.data.toList = ((B.drop o).drop 8).take it.qlen := by
    show ((B.drop (o + 8)).take it.qlen).toArray.toList = _
    rw [List.toList_toArray, List.drop_drop]
  have h2 : (Read.entryAt B o it).2.toList = ((B.drop o).drop (8 + it.qlen)).take 32 := by
    simp only [Read.entryAt, Vector.toList_ofFn]
    refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take, List.length_drop]; omega)
      fun i h₁ h₂ => ?_
    simp only [List.length_ofFn] at h₁
    rw [List.getElem_ofFn]
    simp only [Fin.val_mk]
    rw [List.getElem_take, List.getElem_drop, List.getElem_drop, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1; omega
  rw [hq, hs, List.take_add, List.take_add, hw, h1, h2, List.drop_drop]

/-- **On well-formed bytes, the items' span is the encoding of what `readItems` reads.** -/
theorem take_readItems (B : List UInt8) : ∀ (its : List Item) (o : ℕ), WfAt B o its →
    o + slenS its ≤ B.length → (B.drop o).take (slenS its) = traceBytes (Read.readItems B o its)
  | [], _, _, _ => by simp [slenS, Read.readItems, traceBytes]
  | it :: its, o, ⟨hw, hr⟩, hl => by
    have hs : slenS (it :: its) = it.slen + slenS its := by simp [slenS]
    rw [hs] at hl ⊢
    rw [List.take_add, entry_bytes (by omega) hw, List.drop_drop, take_readItems B its _ hr (by omega),
      Read.readItems, Read.traceBytes_cons']

theorem traceBytes_flatten (trs : List Trace) : traceBytes trs.flatten = (trs.map traceBytes).flatten := by
  induction trs with
  | nil => rfl
  | cons t ts ih => simp only [List.flatten_cons, traceBytes, List.flatMap_append, List.map_cons] at ih ⊢; rw [ih]

theorem take_mul_flatten (B : List UInt8) (o S : ℕ) : ∀ n : ℕ,
    (B.drop o).take (n * S) = ((List.range n).map fun i => (B.drop (o + i * S)).take S).flatten
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, List.take_add, take_mul_flatten B o S n, List.range_succ, List.map_append,
      List.flatten_append, List.drop_drop]
    simp

/-- `seq4`'s items take `segB − 1` bytes. -/
theorem slenS_seq4 : slenS (itemsOf seq4) = N4c.segB - 1 := by
  rw [N4c.segB_eq, streamBytesOf, slenS, Nat.add_sub_cancel_left]
  rfl

/-! ## The spacers (R-A′) -/

/-- **The spacer's constant bytes** at stream offset `o`: its length word and its query,
`enc64 89 ‖ spacerQ` (97 bytes; its answer, the 32 bytes after, is free). -/
def SpAt (B : List UInt8) (o : ℕ) : Prop := (B.drop o).take 97 = enc64 89 ++ spacerQ.data.toList

theorem spItem_slen : spItem.slen = 129 := rfl

/-- **On its constant bytes, a spacer's 129 bytes are the spacer entry** with the answer read off the
stream (`spAnsB`). -/
theorem spacer_bytes {B : List UInt8} {o : ℕ} (hl : o + 129 ≤ B.length) (hs : SpAt B o) :
    (B.drop o).take 129 = traceBytes [spEntry (spAnsB B o)] := by
  have hq97 : (enc64 89 ++ spacerQ.data.toList).length = 97 := by
    rw [List.length_append, enc64_length, Array.length_toList]; exact congrArg (8 + ·) spacerQ_size
  have hw : (B.drop o).take 8 = enc64 spItem.qlen := by
    have : ((B.drop o).take 97).take 8 = (B.drop o).take 8 := by rw [List.take_take]; rfl
    rw [← this, hs, List.take_left' (enc64_length _)]; rfl
  have hq : (Read.entryAt B o spItem).1 = spacerQ := by
    have h2 : ((B.drop o).take 97).drop 8 = (B.drop (o + 8)).take 89 := by
      rw [List.drop_take, List.drop_drop, Nat.add_comm]
    have h3 : (B.drop (o + 8)).take 89 = spacerQ.data.toList := by
      rw [← h2, hs, List.drop_left' (enc64_length _)]
    show (⟨((B.drop (o + 8)).take spItem.qlen).toArray⟩ : ByteArray) = spacerQ
    rw [show spItem.qlen = 89 from rfl, h3]
  rw [← spItem_slen, entry_bytes (by rw [spItem_slen]; exact hl) hw, hq, traceBytes, List.flatMap_singleton]
  rfl

theorem traceBytes_append (a b : Trace) : traceBytes (a ++ b) = traceBytes a ++ traceBytes b := by
  simp [traceBytes]

/-- **A well-formed aggregate stream of `n` segments is `0x54 ‖ V_A`'s trace** (R-A′): the
segments' traces read at `1 + i·strideB`, the spacer entry before segment `i ≥ 1` (its constant bytes
at `i·strideB − 128`, its answer read off the stream). For `n = 1` (a single proof's stream) there is
no spacer. -/
theorem stream_of_wf {B : List UInt8} {n : ℕ} (hl : B.length = N4c.aggB n)
    (h0 : B.head? = some tagTrace)
    (hw : ∀ i < n, WfAt B (1 + i * N4c.strideB) (itemsOf seq4))
    (hs : ∀ i < n, 0 < i → SpAt B (i * N4c.strideB - 128)) :
    B = tagTrace :: traceBytes (aggTrace (fun i => spAnsB B (i * N4c.strideB - 128))
      ((List.range n).map fun i => Read.readItems B (1 + i * N4c.strideB) (itemsOf seq4))) := by
  rw [aggTrace_range]
  set g : ℕ → Trace := fun i => (if i = 0 then [] else [spEntry (spAnsB B (i * N4c.strideB - 128))]) ++
    Read.readItems B (1 + i * N4c.strideB) (itemsOf seq4) with hg
  have hmono : ∀ m m', m ≤ m' → N4c.aggB m ≤ N4c.aggB m' := fun m m' h => by
    simp only [N4c.aggB]
    have := Nat.mul_le_mul_right (N4c.segB - 1) h
    have := Nat.mul_le_mul_right N4c.spacerB (Nat.sub_le_sub_right h 1)
    omega
  have key : ∀ m ≤ n, B.take (N4c.aggB m) = tagTrace :: traceBytes ((List.range m).map g).flatten := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨b, B', rfl⟩ : ∃ b B', B = b :: B' := by
        cases B with
        | nil => simp at h0
        | cons b B' => exact ⟨b, B', rfl⟩
      simp only [List.head?_cons, Option.some.injEq] at h0
      subst h0
      simp [N4c.aggB, traceBytes]
    | succ m ih =>
      intro hm
      have hle := hmono (m + 1) n hm
      rw [List.range_succ, List.map_append, List.flatten_append, traceBytes_append, ← List.cons_append,
        ← ih (by omega), List.map_singleton, List.flatten_singleton]
      have hsplit : N4c.aggB (m + 1) = N4c.aggB m + (N4c.aggB (m + 1) - N4c.aggB m) := by
        have := hmono m (m + 1) (by omega); omega
      rw [hsplit, List.take_add]
      congr 1
      have hT : slenS (itemsOf seq4) = N4c.segB - 1 := slenS_seq4
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · -- segment 0, no spacer
        have hd : N4c.aggB 1 - N4c.aggB 0 = slenS (itemsOf seq4) := by
          rw [hT]; simp [N4c.aggB]
        rw [hd, hg]
        simp only [Nat.zero_mul, Nat.add_zero]
        rw [show N4c.aggB 0 = 1 by simp [N4c.aggB]]
        refine take_readItems B _ 1 (by simpa using hw 0 (by omega)) ?_
        rw [hl, hT]
        have := hmono 1 n (by omega)
        simp only [N4c.aggB] at this ⊢; omega
      · -- spacer `m`, then segment `m`
        obtain ⟨hB, -, hB'⟩ := N4c.aggB_blocks (k := m) (by omega)
        have hs1 := N4c.aggB_succ m (by omega)
        have hd : N4c.aggB (m + 1) - N4c.aggB m = 129 + slenS (itemsOf seq4) := by
          rw [hs1, hT]; simp only [N4c.spacerB]; omega
        have hst : N4c.strideB = N4c.segB - 1 + 129 := rfl
        have ho : m * N4c.strideB - 128 = N4c.aggB m := by rw [hB']
        have hsp : SpAt B (N4c.aggB m) := by rw [← ho]; exact hs m (by omega) hm0
        have hl' : N4c.aggB m + 129 ≤ B.length := by rw [hl]; omega
        rw [hd, List.take_add, hg]
        simp only [if_neg (Nat.pos_iff_ne_zero.1 hm0)]
        rw [traceBytes_append, ho, spacer_bytes hl' hsp, List.drop_drop]
        refine congrArg (traceBytes [spEntry (spAnsB B (N4c.aggB m))] ++ ·) ?_
        have hoff : N4c.aggB m + 129 = 1 + m * N4c.strideB := by
          have : 128 ≤ m * N4c.strideB := by
            have : N4c.strideB ≤ m * N4c.strideB := Nat.le_mul_of_pos_left _ hm0
            simp only [N4c.strideB, N4c.segB, N4c.spacerB] at this ⊢; omega
          omega
        rw [hoff]
        refine take_readItems B _ _ (hw m (by omega)) ?_
        rw [hl]; omega
  have := key n le_rfl
  rwa [List.take_of_length_le (by rw [hl])] at this

end N4s
end FR

end G6_FRNodeRead4W

section G6_FRNodeSound4R

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.3; R-4-m2; stage S-N2, residual 4 of `ks_rev4F`).
-- The 3.x analogue is `FRNodeSoundA` (`NodeResid`, O2/O2b).

/-!
# `hRes` item by item: `StmtN4` and the circuit's gaps give `NodeResid4` at `I4`, `rd4`

`resid4_of` proves `N4c.NodeResid4 (I4 …) (rd4 pf)` from the node's truths `StmtN4` (at
`lRows4`, `nodeIRows4`) and **`Gap4`**, which lists, field by field, what no row of the circuit
binds. Item by item:

| `NodeResid4` field | Source |
|---|---|
| `tpl` | the M rows (`slotRows_of`; `one = 1` from `PubCells4` rules out the rejecting rows) |
| `rep` | `True` in `I4`: the circuit has no replay `R` |
| `selP`, `selA` (selectors) | the link and activity rows (S-E12c's `selP_sel`, `selA_sel`, with `ActK` from the reader's `kAct`: `actK_kAct`) |
| `selP`, `selA` (kind byte) | **gap** `kindN`, `kindS`: no row ties the selector copies to the child proof's byte 0 |
| `slotP`, `aggTr`, `aggFmt`, `kOk` | the reader (`rd4`): `π_A`'s header with the circuit's `k`, fitted slot proofs |
| `pack` | the reader: sizes, trace lengths `≤ qV4` (`traces_le_qV`), queries `≤ queryCap` (`itemsOf_qlen_le`, one `decide` over `seq4`'s phase shapes) |
| `imp` | **gap**: the run on the trace, the auxiliary/import/foreign facts and the statement fact (`SlotImp`): no pack map, no `R` |
| `chainMsg` | `chainMsg_of_wf` from **gap** `wf`: the stream's tag byte, the items' length words and (R-A′) the spacers' length words and queries (constant bytes at fixed stream offsets) are not pinned by any target or row |
| `aggChk` | **gap**: no row checks `V_A`'s checks against `c_A` (statement, `1 ≤ k ≤ 4`, lengths, sum, end, chaining) |
| `aggPad` | **gap**: no row links the candidate final block `F_{a,k}` (R-4-m2) to the main chain at `k` |
| `wots` | **gap**: the WOTS rows (the `k`-mux, the digits, the mirrors) are not built (O2b) |
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## Facts from the statement's rows -/

theorem one_of_pubCells {κ : NodeKind} {w : Asg} {vk c₁ c₂ : Digest} (h : N4c.PubCells4 κ w vk c₁ c₂) :
    w κ.oneCell = 1 := by
  unfold N4c.PubCells4 at h
  have := congrArg List.head? h
  simpa [N4c.cells4, Node.pubVals] using this

/-- On `one = 1`, the M rows are the prototypes' (the rejecting row fails). -/
theorem protoFit_of {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) : ProtoFit := by
  by_contra hF
  refine rejectRows_ctl κ w hone fun p hp => hE p ?_
  rw [nodeIRows4, if_neg hF]; exact hp

theorem map_snd_zipIdx_map' {α : Type*} (l : List α) (f : α × ℕ → ℕ) :
    (l.zipIdx.map fun p => (f p, p.1)).map Prod.snd = l :=
  (map_snd_zipIdx_map l f id).trans (List.map_id _)

/-- **A slot's link rows hold** (they are in the M rows). -/
theorem linkRows_hold {κ : NodeKind} {σ : ℕ} {w : Asg} (hF : ProtoFit) (hσ : σ < κ.vslots)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) : ∀ r ∈ linkRows4 κ σ, r.Holds w := by
  intro r hr
  have hm : r ∈ (linkIRows4 κ σ).map Prod.snd := by
    rw [linkIRows4, map_snd_zipIdx_map']; exact hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
  exact hE p (mem_node_link hF hσ hp)

/-- **The reader's segment count meets `ActK`**: the activity rows make the sub-slots below the
first inactive one active, the first sub-slot is active, and the activity is a bit. -/
theorem actK_kAct {κ : NodeKind} {a : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (ha : a < N4c.nAgg κ)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w) :
    ActK κ a (kAct κ a w) w := by
  classical
  have h2 : 2 ≤ κ.maxK := by cases κ <;> decide
  have hspec := Nat.find_spec (⟨κ.maxK, Or.inl rfl⟩ : ∃ i, i = κ.maxK ∨ (selSum κ (N4c.sub κ a i)).ev w ≠ 1)
  have hmin := fun j (hj : j < kAct κ a w) =>
    Nat.find_min (⟨κ.maxK, Or.inl rfl⟩ : ∃ i, i = κ.maxK ∨ (selSum κ (N4c.sub κ a i)).ev w ≠ 1) hj
  have hle := kAct_le κ a w
  change _ ∨ _ at hspec
  have h0 : (selSum κ (N4c.sub κ a 0)).ev w = 1 := by
    obtain ⟨hv, hx, -, -⟩ := sub_facts κ ha (by omega : 0 < κ.maxK)
    exact act_first hone hv hL (hk 0 (by omega)) (Or.inr hx)
  have hpos : 1 ≤ kAct κ a w := by
    by_contra h
    have hz : kAct κ a w = 0 := by omega
    unfold kAct at hz; rw [hz] at hspec
    rcases hspec with h | h
    · omega
    · exact h h0
  refine ⟨hpos, hle, ?_, fun hlt => ?_⟩
  · have := hmin (kAct κ a w - 1) (by omega)
    simp only [not_or, ne_eq, not_not] at this
    exact this.2
  · unfold kAct at hlt ⊢
    rcases hspec with h | h
    · omega
    · obtain ⟨hv, -, -, -⟩ := sub_facts κ ha hlt
      rcases selSum_bit hone hv hL (hk _ hlt) with h' | h'
      · exact h'
      · exact absurd h' h

/-! ## Format facts of the read proofs -/

theorem kindOf4_of {π : Proof} {ν : NodeKind} (hb : byteAt π 0 = ν.byte) (hs : π.size = piSizeOf seq4) :
    kindOf4 π = .node ν := by
  unfold kindOf4
  dsimp only
  rw [hb, NodeKind.ofByte?_byte]
  dsimp only
  rw [if_pos hs]
  cases ν <;> rfl

theorem segView_of {π : Proof} {κ : SegKind} (hb : byteAt π 0 = κ.byte) :
    ∃ v, segView π = some v ∧ v.kind = κ :=
  ⟨⟨κ, bytesAt π 16 32, bytesAt π 49 32, rdLE64 π 81⟩,
    by simp only [segView, hb, SegKind.ofByte?_byte, Option.map_some], rfl⟩

theorem segTr_length (κ : NodeKind) (σ k i : ℕ) (w : Asg) : (segTr κ σ k i w).length = 8783 := by
  rw [segTr, Read.readItems_length, itemsOf_seq4_length]

theorem slotTr4_length (κ : NodeKind) (v : ℕ) (w : Asg) : (slotTr4 κ v w).length = 8783 := by
  unfold slotTr4; split_ifs <;> exact segTr_length ..

theorem slotPf_length (pf : Trace → Proof) (κ : NodeKind) (v : ℕ) (w : Asg) :
    (slotPf pf κ v w).length = piSizeOf seq4 := fitL_length _ _

theorem aggPf_size (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) :
    (aggPf pf κ a w).size = 48 + kAct κ a w * piSizeOf seq4 := by
  simp only [aggPf, ByteArray.size, List.size_toArray, List.length_append, aggHdr_length,
    List.length_flatten, List.map_map, Function.comp_def, slotPf_length, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]

/-- **An aggregate's read trace length** (R-A′): `k` segments and `k − 1` spacer entries. -/
theorem aggTr_length (κ : NodeKind) (k : ℕ) (f : ℕ → ℕ) (ans : ℕ → Digest) (w : Asg) :
    (aggTrace ans ((List.range k).map fun i => slotTr4 κ (f i) w)).length = k * 8783 + (k - 1) :=
  aggTrace_length ans _ 8783 (fun i => slotTr4_length κ (f i) w) k

/-- A `seq4` phase shape's largest query (3.x's `shapeQ` on `Sh`). -/
def shQ4 : Sh → ℕ
  | .seed => 119
  | .absorb _ len => 40 + len
  | .squeezes _ _ => 40
  | .uni _ => 40 + uniBytes
  | .rounds _ _ _ inK => 40 + roundBytes inK
  | .queries i => max (8 + colBytes i) 72

theorem sh_qlen4 (lv : ℕ → Level) (sh : Sh) : ∀ it ∈ sh.itemsL lv, it.qlen ≤ shQ4 sh := by
  intro it hit
  cases sh with
  | seed => simp [Sh.itemsL] at hit; subst hit; rfl
  | absorb f len => simp [Sh.itemsL] at hit; subst hit; simp [Item.qlen, shQ4]
  | squeezes n ch =>
    simp only [Sh.itemsL, List.mem_replicate] at hit; rw [hit.2]; simp [Item.qlen, shQ4]
  | uni f =>
    simp only [Sh.itemsL, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> simp [Item.qlen, shQ4] <;> omega
  | rounds f n deg inK =>
    simp only [Sh.itemsL, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp [Item.qlen, shQ4] <;> omega
  | queries i =>
    simp only [Sh.itemsL, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
    simp only [posItemsL, List.mem_cons, List.mem_map, List.mem_range] at hl
    rcases hl with rfl | ⟨h, -, rfl⟩ <;> simp [Item.qlen, shQ4]

/-- Every `seq4` phase's largest query is within `queryCap` (its shape parameters only). -/
theorem phasesOf_shQ4 : (phasesOf seq4).all (fun p => decide (shQ4 p.2 ≤ queryCap)) = true := by
  rw [seq4_eq]; decide +kernel

/-- **Every `seq4` item's query is within `queryCap`.** -/
theorem itemsOf_qlen_le : ∀ it ∈ itemsOf seq4, it.qlen ≤ queryCap := by
  intro it hit
  simp only [itemsOf, List.mem_flatMap] at hit
  obtain ⟨p, hp, hit⟩ := hit
  have := List.all_eq_true.1 phasesOf_shQ4 p hp
  simp only [decide_eq_true_eq] at this
  exact (sh_qlen4 _ _ it hit).trans this

theorem slotTr4_qcap (κ : NodeKind) (v : ℕ) (w : Asg) : ∀ e ∈ slotTr4 κ v w, e.1.size ≤ queryCap := by
  intro e he
  have h : ∀ σ k i, ∀ e ∈ segTr κ σ k i w, e.1.size ≤ queryCap := fun σ k i e he => by
    obtain ⟨it, hit, hle⟩ := Snd.readItems_qlen _ _ _ e he
    exact hle.trans (itemsOf_qlen_le it hit)
  unfold slotTr4 at he; split_ifs at he <;> exact h _ _ _ e he

/-- **A read child's queries are within `queryCap`.** -/
theorem sgn4_qcap (pf : Trace → Proof) (κ : NodeKind) (σ : ℕ) (w : Asg) :
    ∀ e ∈ (sgn4 pf κ σ w).tr, e.1.size ≤ queryCap := by
  intro e he
  unfold sgn4 at he
  split_ifs at he
  · rcases mem_aggTrace he with ⟨i, -, he⟩ | ⟨i, rfl⟩
    · exact slotTr4_qcap κ _ w e he
    · show spacerQ.size ≤ queryCap
      rw [spacerQ_size]; decide
  · exact slotTr4_qcap κ 0 w e he

/-! ## The chain's message from the stream's constant bytes -/

/-- Signed child `σ`'s segment count as read (`1` for a previous node). -/
noncomputable def nSeg (κ : NodeKind) (σ : ℕ) (w : Asg) : ℕ :=
  if N4c.isAgg κ σ then kAct κ (N4c.aggOf κ σ) w else 1

theorem slotA_sub (κ : NodeKind) {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) :
    slotA κ (N4c.sub κ a i) = a := by
  cases κ <;> simp only [slotA, N4c.sub, N4c.nAgg, NodeKind.hasPrev, NodeKind.maxK, if_true,
    Bool.false_eq_true, if_false] at ha hi ⊢ <;> omega

theorem slotTr4_sub (κ : NodeKind) {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) (w : Asg) :
    slotTr4 κ (N4c.sub κ a i) w = segTr κ (N4c.aggChild κ a) (kAct κ a w) i w := by
  obtain ⟨-, hx, hp, -⟩ := sub_facts κ ha hi
  rw [slotTr4, if_neg (by simp [hp]), slotA_sub κ ha hi, hx]

/-- **`NodeResid4.chainMsg` from the streams' constant bytes**: if signed child `σ`'s stream starts
with the tag and has every item's length word and (R-A′) every spacer's length word and query in
place, it is `0x54 ‖ traceBytes` of the read trace. -/
theorem chainMsg_of_wf (pf : Trace → Proof) {κ : NodeKind} {σ : ℕ} {w : Asg} (hσ : σ < 2)
    (h0 : (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w).head? = some tagTrace)
    (hw : ∀ i < nSeg κ σ w, WfAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (1 + i * N4c.strideB)
      (itemsOf seq4) ∧ (0 < i → SpAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (i * N4c.strideB - 128))) :
    N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w = tagTrace :: traceBytes ((rd4 pf).sgn κ σ w).tr := by
  have hlen : ∀ k, (N4c.chainBytes4 κ σ k w).length = N4c.streamB κ σ k := fun k =>
    Stream.streamBytes_length _ _
  by_cases hA : N4c.isAgg κ σ = true
  · obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
    have hk : N4c.kOf (rd4 pf) κ w σ = kAct κ (N4c.aggOf κ σ) w := by
      rw [N4c.kOf, if_pos hA, kA_rd4 pf κ ha]
    have hn : nSeg κ σ w = kAct κ (N4c.aggOf κ σ) w := by rw [nSeg, if_pos hA]
    rw [hk] at h0 hw ⊢
    rw [hn] at hw
    rw [stream_of_wf (by rw [hlen, N4c.streamB, if_pos hA]) h0 (fun i hi => (hw i hi).1)
      (fun i hi => (hw i hi).2)]
    congr 2
    conv_rhs => rw [← hc]
    show _ = (sgn4 pf κ (N4c.aggChild κ (N4c.aggOf κ σ)) w).tr
    rw [sgn4_agg pf κ ha]
    dsimp only
    rw [hc]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [slotTr4_sub κ ha (lt_of_lt_of_le hi' (kAct_le κ _ w)) w, hc]
    rfl
  · have hp : κ.hasPrev = true ∧ σ = 0 := by
      cases κ <;> simp_all [N4c.isAgg, NodeKind.hasPrev]
    obtain ⟨hp, rfl⟩ := hp
    have hk : N4c.kOf (rd4 pf) κ w 0 = 0 := by rw [N4c.kOf, if_neg hA]
    have hn : nSeg κ 0 w = 1 := by rw [nSeg, if_neg hA]
    rw [hk] at h0 hw ⊢
    rw [hn] at hw
    rw [stream_of_wf (n := 1) (by rw [hlen, N4c.streamB, if_neg hA]; rfl) h0 (fun i hi => (hw i hi).1)
      (fun i hi => (hw i hi).2)]
    simp only [rd4, sgn4, if_neg hA, slotTr4, isPrevSlot, hp, Bool.true_and, beq_self_eq_true, if_true,
      List.range_one, List.map_cons, List.map_nil, aggTrace, aggTrAt, List.nil_append, List.append_nil,
      zero_mul, add_zero]
    rfl

/-! ## The gaps -/

/-- **What no row of the 4.1 node circuit binds** (S-N2's soundness gap), field by field, for the
reader `rd4 pf` and the slot interface `I4`'s `imp` (`SlotImp`). -/
structure Gap4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (pf : Trace → Proof) (κ : NodeKind)
    (vk c₁ c₂ : Digest) (w : Asg) : Prop where
  /-- Every active slot's run on its trace, its auxiliary/import/foreign facts and the statement
  fact (the pack map, the `input` alias, the replay `R`). -/
  imp : ∀ v, N4c.Active4 (rd4 pf) κ w v →
    SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)
  /-- The previous node's proof has the selected node kind's byte. -/
  kindN : κ.hasPrev = true → ∀ ι, SelOk (slotAsg κ 0 w) (protoP 0) ι →
    byteAt ((rd4 pf).sgn κ 0 w).π 0 = (nodeAt ι).byte
  /-- An active sub-slot's proof has the selected segment kind's byte. -/
  kindS : ∀ a < N4c.nAgg κ, ∀ i < kAct κ a w, ∀ ι, SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι →
    byteAt ((rd4 pf).slotπ κ (N4c.sub κ a i) w) 0 = (segAt ι).byte
  /-- H's streams' constant bytes (for `NodeResid4.chainMsg`): the tag `0x54` at byte 0, each read
  item's 8-byte length word `enc64 |q|` at its offset, and (R-A′) before each later segment the
  spacer's length word and query `enc64 89 ‖ spacerQ`. -/
  wf : ∀ σ < 2, (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w).head? = some tagTrace ∧
    ∀ i < nSeg κ σ w, WfAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (1 + i * N4c.strideB)
      (itemsOf seq4) ∧ (0 < i → SpAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (i * N4c.strideB - 128))
  /-- `NodeResid4.aggChk`: `V_A`'s checks against `c_A`. -/
  aggChk : ∀ a < N4c.nAgg κ, ∃ vs, (aggSegs (piSizeOf seq4) (N4c.kA (rd4 pf) κ w a)
      ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π).mapM segView = some vs ∧
    aggChecks (N4c.stOf c₁ c₂ (N4c.aggChild κ a)) (rdLE64 ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 8)
      (bytesAt ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 16 32) vs = true
  /-- `NodeResid4.aggPad` (R-4-m2): the `k`-gated final block. -/
  aggPad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf) κ w a) w
  /-- `NodeResid4.wots`: WOTS on the `k`-selected H digest. -/
  wots : ∀ σ < 2, SigOk vk (N4c.hDig4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) ((rd4 pf).sgn κ σ w).σ = true

/-! ## `hRes` -/

section Resid
variable {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν))
  (pf : Trace → Proof) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}

theorem vslots_pos (κ : NodeKind) : 0 < κ.vslots := by cases κ <;> decide

theorem active_lt {v : ℕ} (h : N4c.Active4 (rd4 pf) κ w v) : v < κ.vslots := by
  rcases h with ⟨-, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · exact vslots_pos κ
  · rw [kA_rd4 pf κ ha] at hi
    exact (sub_facts κ ha (lt_of_lt_of_le hi (kAct_le κ a w))).1

theorem isAgg_zero {κ : NodeKind} (hp : κ.hasPrev = true) : N4c.isAgg κ 0 = false := by
  simp [N4c.isAgg, hp]

theorem protoOf_zero {κ : NodeKind} (hp : κ.hasPrev = true) : protoOf κ 0 = 0 := by
  simp [protoOf, isPrevSlot, hp]

/-- **`hRes`**: the node's truths and the circuit's gaps give `NodeResid4` at `I4`, `rd4 pf`. -/
theorem resid4_of (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hG : Gap4 impl₀ base pf κ vk c₁ c₂ w) : N4c.NodeResid4 (I4 impl₀ base hT₀ hT) (rd4 pf) κ vk c₁ c₂ w := by
  obtain ⟨-, -, hL, hE, hP⟩ := hS
  have hone := one_of_pubCells hP
  have hF := protoFit_of hone hE
  have hk : ∀ a < N4c.nAgg κ, N4c.kA (rd4 pf) κ w a = kAct κ a w := fun a ha => kA_rd4 pf κ ha w
  have hlk : ∀ a < N4c.nAgg κ, ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w :=
    fun a ha i hi => linkRows_hold hF (sub_facts κ ha hi).1 hE
  refine ⟨hG.imp, fun _ _ => trivial, fun v hv => slotRows_of hone (active_lt pf hv) hE, ?_, ?_, ?_, ?_,
    fun σ hσ => chainMsg_of_wf pf hσ (hG.wf σ hσ).1 (hG.wf σ hσ).2, ?_, ?_, hG.aggChk, ?_, hG.aggPad, hG.wots⟩
  · -- selP
    intro hp
    obtain ⟨ι, hι⟩ := selP_sel hone hp hL (linkRows_hold hF (vslots_pos κ) hE)
    rw [protoOf_zero hp] at hι
    refine ⟨nodeAt ι, ⟨by simp [isPrevSlot, hp], ι, rfl, hι⟩, kindOf4_of (hG.kindN hp ι hι) ?_⟩
    simp only [rd4, sgn4, isAgg_zero hp, Bool.false_eq_true, ite_false, ByteArray.size, List.size_toArray,
      slotPf_length]
  · -- slotP
    intro hp
    simp only [rd4, sgn4, isAgg_zero hp, Bool.false_eq_true, ite_false, and_self]
  · -- selA
    intro a ha i hi
    rw [hk a ha] at hi
    obtain ⟨ι, hι⟩ := selA_sel hone ha hL (hlk a ha) (actK_kAct hone ha hL (hlk a ha)) i hi
    obtain ⟨-, -, hp, -⟩ := sub_facts κ ha (lt_of_lt_of_le hi (kAct_le κ a w))
    rw [protoOf_seg hp] at hι
    obtain ⟨v, hv, hk'⟩ := segView_of (hG.kindS a ha i hi ι hι)
    exact ⟨v, hv, hp, ι, hk'.symm, hι⟩
  · -- pack
    intro σ hσ
    refine ⟨?_, ?_, sgn4_qcap pf κ σ w⟩
    · by_cases hA : N4c.isAgg κ σ = true
      · obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
        rw [← hc]
        simp only [rd4, sgn4_agg pf κ ha, aggPf_size, piSizeOf_seq4]
        have := kAct_le κ (N4c.aggOf κ σ) w
        have h4 : κ.maxK ≤ 4 := by cases κ <;> decide
        omega
      · simp only [rd4, sgn4, hA, Bool.false_eq_true, ite_false, ByteArray.size, List.size_toArray,
          slotPf_length, piSizeOf_seq4]
        norm_num
    · have hq := traces_spacers_le_qV
      rw [itemsOf_seq4_length] at hq
      by_cases hA : N4c.isAgg κ σ = true
      · obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
        rw [← hc]
        simp only [rd4, sgn4_agg pf κ ha, aggTr_length]
        have := kAct_le κ (N4c.aggOf κ σ) w
        have h4 : κ.maxK ≤ 4 := by cases κ <;> decide
        have h48 := Nat.mul_le_mul_right 8783 (this.trans h4)
        exact le_trans (Nat.add_le_add h48 (Nat.sub_le_sub_right (this.trans h4) 1)) hq
      · simp only [rd4, sgn4, hA, Bool.false_eq_true, ite_false, slotTr4_length]
        omega
  · -- aggFmt
    intro a ha
    rw [hk a ha]
    simp only [rd4, sgn4_agg pf κ ha]
    refine ⟨aggPf_size pf κ a w, ?_, ?_, ?_⟩
    · simp [aggPf, aggHdr]
    · refine Vector.ext fun i hi => ?_
      simp only [bytesAt, Vector.getElem_ofFn, Vector.getElem_replicate, aggPf, byteAt_mk, aggHdr]
      interval_cases i <;> rfl
    · rw [aggPf, aggSegs_flat _ _ (aggHdr_length _ _ _)
        (fun s hs => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
          exact slotPf_length pf κ _ w) (by simp), List.map_map]
      rfl
  · -- aggTr
    intro a ha
    rw [hk a ha]
    exact ⟨spAns κ (N4c.aggChild κ a) (kAct κ a w) w, by simp only [rd4, sgn4_agg pf κ ha]⟩
  · -- kOk
    intro a ha
    rw [hk a ha]; exact kAct_le κ a w

end Resid

end N4s
end FR

end G6_FRNodeSound4R

section G6_FRNodeRows4Rep

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4 "the replay fixed point", A.11's replay
-- templates; stage S-E14, track L-circ).

/-!
# The replay `R`: imports discharged by rows, inside the compile's induction

The compiled slot programs leave the six replayed ops (`targetS`, `shiftTarget`, `linkWAll`,
`rsWeight`, `evalM`, `evalL`) as **imports** (`FRVIRCompile.opOut`): fresh cells that no row
constrains, assumed by `compileX_soundK` at the final run (`hi`). A replay row can only say
`cell(out) = f(cells(args))`; it gives `RepS` of the output only if the operands' cells already
represent their registers **at the op**. So the discharge is a staged soundness:

* **`RT`** (a replay template): which ops it covers, and per compile state, op and output slots its
  rows. **`RTOk impl X rt κ`**: a covered op never asks, and its rows, the invariant `InvK` at the
  op and the selector give `RepS` of its outputs at the op's value.
* **`repRowsX`**, **`impRX`**: the rows of every covered op along the compile's trail, and the import
  registers of the ops it does not cover (defined by the same fold as `compileFromX`, so nothing
  evaluates a program).
* **`compileFromX_soundR`**: `compileFromX_soundK`'s induction with `hi` restricted to `impRX` and
  the rows `repRowsX`; **`compileX_soundR`**.
* (C1) **`RTOkW`**, **`compileFromX_soundRW`**, **`compileX_soundRW`**: the same with the replay rows at
  a second assignment `w'` that agrees with `w` below a bound (`Agree`): a template's own cells
  (locals) then live outside the slot's region.

At the node (namespace `N4s`): `repRowsP rt π` (prototype `π`'s replay rows, its frame),
**`SlotRunR`**/**`SlotImpR`** (S-N2's `SlotRun`/`SlotImp` with the covered imports removed),
**`slotImp_of_rep`** (the rows and `SlotImpR` give `SlotImp`), the node's indexed rows `repIRows4`
in each slot region's replay rows (`repBase`, JOURNAL §0) and **`gap4Imp_of_rep`** (`Gap4.imp` from
`StmtN4`, the fold `hfold` and `SlotImpR`).
-/

namespace FR
namespace Circ
open RecursionFast

/-! ## Replay templates -/

/-- **A replay template is sound at kind `κ`**: a covered op never asks, and where it is an import,
its rows with the invariant at the op give its outputs' representation. -/
def RTOk (impl : OpImpl) (X : Ext) (rt : RT) (κ : Kind) : Prop :=
  ∀ P cs op, rt.cov op = true →
    (∀ inp regs q, evalOp impl κ inp regs op ≠ .ask q) ∧
    ∀ inp w regs vs ok, SelOk w P κ → InvK w cs regs κ →
      (∀ r ∈ rt.rows P cs op (stepOut X P cs op).slots, r.Holds w) →
      evalOp impl κ inp regs op = .vals vs ok → (stepOut X P cs op).imp = true →
      List.Forall₂ (RepS w) (stepOut X P cs op).slots vs

theorem RT.none_ok (impl : OpImpl) (X : Ext) (κ : Kind) : RTOk impl X RT.none κ :=
  fun _ _ _ h => absurd h Bool.false_ne_true

/-- **The import registers the template does not cover**, along the trail. -/
def impRX (X : Ext) (P : Params) (rt : RT) : CS → List Op → List ℕ
  | _, [] => []
  | cs, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if (stepOut X P c op).imp && !rt.cov op then List.range' c.slots.size (stepOut X P c op).slots.length
      else []) ++ impRX X P rt (c.add op (stepOut X P c op)) ops

theorem repRowsX_cons (X : Ext) (P : Params) (rt : RT) (cs : CS) (op : Op) (ops : List Op) :
    repRowsX X P rt cs (op :: ops) =
      (if rt.cov op then rt.rows P (cs.align (alignOf op ops)) op
          (stepOut X P (cs.align (alignOf op ops)) op).slots else []) ++
        repRowsX X P rt ((cs.align (alignOf op ops)).add op (stepOut X P (cs.align (alignOf op ops)) op)) ops :=
  rfl

theorem impRX_cons (X : Ext) (P : Params) (rt : RT) (cs : CS) (op : Op) (ops : List Op) :
    impRX X P rt cs (op :: ops) =
      (if (stepOut X P (cs.align (alignOf op ops)) op).imp && !rt.cov op then
          List.range' (cs.align (alignOf op ops)).slots.size
            (stepOut X P (cs.align (alignOf op ops)) op).slots.length else []) ++
        impRX X P rt ((cs.align (alignOf op ops)).add op (stepOut X P (cs.align (alignOf op ops)) op)) ops :=
  rfl

/-- **Every uncovered import is an import of the compile** (so `impRX` asks nothing new). -/
theorem impRX_sub (X : Ext) (P : Params) (rt : RT) :
    ∀ (ops : List Op) (cs : CS), ∀ i ∈ impRX X P rt cs ops, i ∈ (compileFromX X P cs ops).imp
  | [], _, i, h => by simp [impRX] at h
  | op :: ops, cs, i, h => by
    rw [impRX_cons, List.mem_append] at h
    rw [compileFromX_cons]
    rcases h with h | h
    · obtain ⟨_, _, -, -, hm, -⟩ := compileFromX_mono X P ops
        ((cs.align (alignOf op ops)).add op (stepOut X P (cs.align (alignOf op ops)) op))
      refine hm ?_
      split_ifs at h with hc
      · simp only [Bool.and_eq_true] at hc
        simp only [CS.add, hc.1, if_true]
        exact List.mem_append_left _ h
      · simp at h
    · exact impRX_sub X P rt ops _ i h

/-- The template that covers nothing leaves every import. -/
theorem impRX_none (X : Ext) (P : Params) :
    ∀ (ops : List Op) (cs : CS), ∀ i ∈ (compileFromX X P cs ops).imp, i ∈ cs.imp ∨ i ∈ impRX X P RT.none cs ops
  | [], cs, i, h => .inl (by simpa [compileFromX] using h)
  | op :: ops, cs, i, h => by
    rw [compileFromX_cons] at h
    rcases impRX_none X P ops _ i h with h' | h'
    · simp only [CS.add, CS.align_imp] at h'
      split_ifs at h' with hc
      · rcases List.mem_append.1 h' with h'' | h''
        · refine .inr ?_
          rw [impRX_cons]
          refine List.mem_append_left _ ?_
          simp only [RT.none, hc, Bool.not_false, Bool.and_self, if_true]
          exact h''
        · exact .inl h''
      · exact .inl h'
    · exact .inr (by rw [impRX_cons]; exact List.mem_append_right _ h')

/-! ## The staged soundness -/

/-- **`compileFromX_soundK` with replay rows**: the imports of covered ops are discharged by their
rows at the op (`RTOk`), the others are assumed (`impRX`). -/
theorem compileFromX_soundR {impl : OpImpl} {κ : Kind} {inp : Input} {w : Asg} {P : Params}
    {tc : Tpl.TCtx} {X : Ext} {rt : RT} (hX : ExtOkK impl tc X κ) (hP : SelOk w P κ)
    (hR : RTOk impl X rt κ) :
    ∀ (ops : List Op) (cs : CS) (s s' : St) (tr tr' : Trace),
    InvK w cs s.regs κ → exec impl κ inp ops s tr = some (s', tr') →
    (∀ r ∈ (compileFromX X P cs ops).rows, r.Holds w) →
    (∀ t ∈ (compileFromX X P cs ops).tins, ∀ r ∈ Tpl.instRows tc P.one t, r.Holds w) →
    (∀ a ∈ (compileFromX X P cs ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s'.regs.extract 0 a.2) a.1.2.1)) →
    (∀ i ∈ impRX X P rt cs ops, RepS w ((compileFromX X P cs ops).slot i) (rd s'.regs i)) →
    (∀ r ∈ repRowsX X P rt cs ops, r.Holds w) →
    (∀ p ∈ (compileFromX X P cs ops).fors,
      flagOf impl κ inp (s'.regs.extract 0 p.2) p.1 = true) →
    s'.ok = s.ok ∧ InvK w (compileFromX X P cs ops) s'.regs κ
  | [], cs, s, s', tr, tr', hI, he, _, _, _, _, _, _ => by
    simp [exec] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨rfl, hI⟩
  | op :: ops, cs, s, s', tr, tr', hI, he, hr, ht, hx, hi, hrr, hf => by
    rw [impRX_cons] at hi
    rw [repRowsX_cons] at hrr
    rw [compileFromX_cons] at hr ht hx hi hf ⊢
    have hI' : InvK w (cs.align (alignOf op ops)) s.regs κ :=
      ⟨⟨by simp [hI.1.1], fun i => by rw [CS.align_slot]; exact hI.1.2 i⟩,
        fun p hp => by rw [CS.align_kslots] at hp; rw [CS.align_slots]; exact hI.2.1 p hp,
        fun i => by rw [CS.align_slotK]; exact hI.2.2 i⟩
    generalize cs.align (alignOf op ops) = cs at hI' hr ht hx hi hrr hf ⊢
    clear hI
    rename' hI' => hI
    set o := stepOut X P cs op with ho
    obtain ⟨ss, rs, hsl, hrw, -, hfor, htin, haux⟩ := compileFromX_mono X P ops (cs.add op o)
    have hro : ∀ r ∈ o.rows, r.Holds w := fun r h =>
      hr r (by
        rw [hrw]; simp only [CS.add, List.reverseAux_eq]
        exact List.mem_append_right _ (List.mem_append_left _ (List.mem_reverse.2 h)))
    have hto : ∀ t ∈ o.tin, ∀ r ∈ Tpl.instRows tc P.one (t.1, cs.tcount t.1, t.2), r.Holds w :=
      fun t htm r hr' => ht _ (htin (by simp only [CS.add, Option.mem_def.1 htm]; simp)) r hr'
    have hpre : ∀ (m : Array Val), (s.regs ++ m).extract 0 cs.slots.size = s.regs := fun m => by
      rw [hI.1.1, Array.extract_append_left, Array.extract_size]
    -- an uncovered import's registers: from `hi`
    have fin : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) → o.imp = true → rt.cov op = false →
        (hl : o.slots.length = vs.length) →
        ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
      intro vs s1 hs1 ⟨m, hm⟩ hio hc hl j hj
      have := hi (cs.slots.size + j) (List.mem_append_left _ (by
        simp only [← ho, hio, hc, Bool.not_false, Bool.and_self, if_true, List.mem_range'_1]; omega))
      have hs := slot_append_right cs.slots o.slots ss hj
      have hv := rd_append_right s.regs vs m (by omega : j < vs.length)
      rw [CS.slot, hsl] at this; simp only [CS.add] at this
      rw [hs, hm, hs1, hI.1.1, hv] at this; exact this
    have flag : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) → o.foreign = true →
        flagOf impl κ inp s.regs op = true := by
      intro vs s1 hs1 ⟨m, hm⟩ hfo
      have := hf (op, cs.slots.size) (hfor (by simp [CS.add, hfo]))
      rwa [hm, hs1, Array.append_assoc, hpre] at this
    have hauxo : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) →
        ∀ a ∈ o.aux, a.1.map (Lin.ev w) = a.2.2.val (rd s.regs a.2.1) := by
      intro vs s1 hs1 ⟨m, hm⟩ a ha
      have := hx (a, cs.slots.size) (haux (by simp [CS.add, ha]))
      rwa [hm, hs1, Array.append_assoc, hpre] at this
    have hstep : (∀ q, evalOp impl κ inp s.regs op ≠ .ask q) ∨ X P cs op = none := by
      rcases hXo : X P cs op with _ | o'
      · exact .inr rfl
      · exact .inl ((hX P cs op o' hXo).2.2 inp w s.regs hP hI.1.2 hI.2.2).1
    have hpos : o.kin.isSome → 0 < o.slots.length := by
      rcases hXo : X P cs op with _ | o'
      · simp [ho, stepOut, hXo, opOut_kin]
      · simp only [ho, stepOut, hXo, Option.getD_some]; exact (hX P cs op o' hXo).2.1
    have hlen : o.slots.length = op.nOut := by
      rcases hXo : X P cs op with _ | o'
      · simp only [ho, stepOut, hXo, Option.getD_none]; exact opOut_len P cs op
      · simp only [ho, stepOut, hXo, Option.getD_some]; exact (hX P cs op o' hXo).1
    have hrr' : ∀ r ∈ repRowsX X P rt (cs.add op o) ops, r.Holds w :=
      fun r h => hrr r (List.mem_append_right _ h)
    have hi' : ∀ i ∈ impRX X P rt (cs.add op o) ops,
        RepS w ((compileFromX X P (cs.add op o) ops).slot i) (rd s'.regs i) :=
      fun i h => hi i (List.mem_append_right _ h)
    simp only [exec] at he
    split at he
    · rename_i vs ok hev
      have hl := hlen.trans (evalOp_len hev).symm
      have hm := exec_prefix ops _ _ he
      have hsnd : (o.imp = false → List.Forall₂ (RepS w) o.slots vs) ∧ (o.foreign = false → ok = true) ∧
          (∀ f v, o.kin = some f → vs.head? = some v → RepS w (f κ) v) := by
        rcases hXo : X P cs op with _ | o'
        · simp only [ho, stepOut, hXo, Option.getD_none] at hro ⊢
          exact ⟨(opOut_sound hP hI.1.2 op hro hev).1, (opOut_sound hP hI.1.2 op hro hev).2,
            fun f v hf => by rw [opOut_kin] at hf; cases hf⟩
        · have eo : o = o' := by simp [ho, stepOut, hXo]
          rw [eo] at hro hto ⊢
          exact ((hX P cs op o' hXo).2.2 inp w s.regs hP hI.1.2 hI.2.2).2 hro hto
            (eo ▸ hauxo vs _ rfl hm) vs ok hev
      have hnew : ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
        cases hio : o.imp
        · exact fun j hj => (List.forall₂_iff_get.1 (hsnd.1 hio)).2 j hj _
        · cases hc : rt.cov op
          · exact fin vs _ rfl hm hio hc hl
          · have hrows : ∀ r ∈ rt.rows P cs op o.slots, r.Holds w :=
              fun r h => hrr r (List.mem_append_left _ (by rw [if_pos hc]; exact h))
            exact fun j hj => (List.forall₂_iff_get.1
              ((hR P cs op hc).2 inp w s.regs vs ok hP hI hrows hev hio)).2 j hj _
      have hok : ok = true := by
        cases hfo : o.foreign
        · exact hsnd.2.1 hfo
        · have := flag vs _ rfl hm hfo; simpa [flagOf, hev] using this
      have ih := compileFromX_soundR hX hP hR ops _ _ s' tr tr'
        (invK_add hI o op hl hnew hsnd.2.2 hpos) he hr ht hx hi' hrr' hf
      exact ⟨by rw [ih.1, hok, Bool.and_true], ih.2⟩
    · rename_i q hev
      have hXn : X P cs op = none := hstep.resolve_left fun h => h q hev
      have ho' : o = opOut P cs op := by simp [ho, stepOut, hXn]
      have hc : rt.cov op = false := by
        cases hc : rt.cov op
        · rfl
        · exact absurd hev ((hR P cs op hc).1 inp s.regs q)
      split at he
      · simp at he
      · rename_i q' a tr0
        split at he
        · have hio : o.imp = true := ho' ▸ ask_imp P cs hev
          have hl : o.slots.length = [Val.d a].length := by
            rw [hlen, ask_nOut hev]; rfl
          have hm := exec_prefix ops _ _ he
          have hnew := fin [.d a] ⟨s.regs.push (.d a), s.ok⟩ rfl hm hio hc hl
          exact compileFromX_soundR hX hP hR ops _ ⟨s.regs.push (.d a), s.ok⟩ s' tr0 tr'
            (invK_add hI o op hl hnew (fun f v hf => by rw [ho', opOut_kin] at hf; cases hf) hpos)
            he hr ht hx hi' hrr' hf
        · simp at he

/-- **`compileX_soundK` with replay rows.** -/
theorem compileX_soundR {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w : Asg} {P : Params} {tc : Tpl.TCtx} {X : Ext} {rt : RT} (hX : ExtOkK impl tc X κ)
    (hR : RTOk impl X rt κ) (base : ℕ) (hP : SelOk w P κ)
    (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileX X P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileX X P base ops).tplRows tc P.one, r.Holds w)
    (hx : ∀ a ∈ (compileX X P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ impRX X P rt (CS.init base) ops, RepS w ((compileX X P base ops).slot i) (rd s.regs i))
    (hrr : ∀ r ∈ repRowsX X P rt (CS.init base) ops, r.Holds w)
    (hf : ∀ p ∈ (compileX X P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compileX X P base ops).slot i) (rd s.regs i) := by
  have h := compileFromX_soundR hX hP hR ops (CS.init base) St.init s tr tr'
    ⟨⟨rfl, fun i => by simp [CS.slot, CS.init, RepS]⟩, fun p hp => by simp [CS.init] at hp,
      fun i => by simp [CS.slotK, CS.slot, CS.init, RepS]⟩ he hr
    (fun t htm r hr' => ht r (List.mem_flatMap.2 ⟨t, htm, hr'⟩)) hx hi hrr hf
  exact ⟨h.1, h.2.1.2⟩

/-! ## Replay rows at a second assignment

The replay's own cells (a template's locals) are not the prototype's: the fold puts them in slot 0's
spare region, so the replay rows hold at an assignment `w'` that **agrees** with the slot's `w`
below the frame bound `B` (every cell of the compile) and reads the spare region above it.
**`RTOkW`** is `RTOk` with the rows at `w'`; each template checks at compile time that the forms
it reads have their cells below `B` (`linLt`). -/

/-- Two assignments agree below `B`. -/
def Agree (B : ℕ) (w w' : Asg) : Prop := ∀ c < B, w' c = w c

theorem ev_agree {B : ℕ} {w w' : Asg} (hA : Agree B w w') {l : Lin} (h : linLt B l = true) :
    l.ev w' = l.ev w := by
  have hm : ∀ t ∈ l, t.1 < B := fun t ht => of_decide_eq_true (List.all_eq_true.1 h t ht)
  unfold Lin.ev
  exact congrArg List.sum (List.map_congr_left fun t ht => by rw [hA _ (hm t ht)])

theorem map_ev_agree {B : ℕ} {w w' : Asg} (hA : Agree B w w') {ls : List Lin}
    (h : ls.all (linLt B) = true) : ls.map (Lin.ev w') = ls.map (Lin.ev w) :=
  List.map_congr_left fun l hl => ev_agree hA (List.all_eq_true.1 h l hl)

/-- **A replay template is sound at kind `κ`, its rows at an assignment agreeing below `B`.** -/
def RTOkW (impl : OpImpl) (X : Ext) (rt : RT) (κ : Kind) (B : ℕ) : Prop :=
  ∀ P cs op, rt.cov op = true →
    (∀ inp regs q, evalOp impl κ inp regs op ≠ .ask q) ∧
    ∀ inp w w' regs vs ok, SelOk w P κ → SelOk w' P κ → InvK w cs regs κ → Agree B w w' →
      (∀ r ∈ rt.rows P cs op (stepOut X P cs op).slots, r.Holds w') →
      evalOp impl κ inp regs op = .vals vs ok → (stepOut X P cs op).imp = true →
      List.Forall₂ (RepS w) (stepOut X P cs op).slots vs

theorem RT.none_okW (impl : OpImpl) (X : Ext) (κ : Kind) (B : ℕ) : RTOkW impl X RT.none κ B :=
  fun _ _ _ h => absurd h Bool.false_ne_true

/-- **`compileFromX_soundR` with the replay rows at `w'`** (agreeing with `w` below `B`, `RTOkW`). -/
theorem compileFromX_soundRW {impl : OpImpl} {κ : Kind} {inp : Input} {w : Asg} {P : Params}
    {tc : Tpl.TCtx} {X : Ext} {rt : RT} {w' : Asg} {B : ℕ} (hX : ExtOkK impl tc X κ) (hP : SelOk w P κ)
    (hP' : SelOk w' P κ) (hA : Agree B w w') (hR : RTOkW impl X rt κ B) :
    ∀ (ops : List Op) (cs : CS) (s s' : St) (tr tr' : Trace),
    InvK w cs s.regs κ → exec impl κ inp ops s tr = some (s', tr') →
    (∀ r ∈ (compileFromX X P cs ops).rows, r.Holds w) →
    (∀ t ∈ (compileFromX X P cs ops).tins, ∀ r ∈ Tpl.instRows tc P.one t, r.Holds w) →
    (∀ a ∈ (compileFromX X P cs ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s'.regs.extract 0 a.2) a.1.2.1)) →
    (∀ i ∈ impRX X P rt cs ops, RepS w ((compileFromX X P cs ops).slot i) (rd s'.regs i)) →
    (∀ r ∈ repRowsX X P rt cs ops, r.Holds w') →
    (∀ p ∈ (compileFromX X P cs ops).fors,
      flagOf impl κ inp (s'.regs.extract 0 p.2) p.1 = true) →
    s'.ok = s.ok ∧ InvK w (compileFromX X P cs ops) s'.regs κ
  | [], cs, s, s', tr, tr', hI, he, _, _, _, _, _, _ => by
    simp [exec] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨rfl, hI⟩
  | op :: ops, cs, s, s', tr, tr', hI, he, hr, ht, hx, hi, hrr, hf => by
    rw [impRX_cons] at hi
    rw [repRowsX_cons] at hrr
    rw [compileFromX_cons] at hr ht hx hi hf ⊢
    have hI' : InvK w (cs.align (alignOf op ops)) s.regs κ :=
      ⟨⟨by simp [hI.1.1], fun i => by rw [CS.align_slot]; exact hI.1.2 i⟩,
        fun p hp => by rw [CS.align_kslots] at hp; rw [CS.align_slots]; exact hI.2.1 p hp,
        fun i => by rw [CS.align_slotK]; exact hI.2.2 i⟩
    generalize cs.align (alignOf op ops) = cs at hI' hr ht hx hi hrr hf ⊢
    clear hI
    rename' hI' => hI
    set o := stepOut X P cs op with ho
    obtain ⟨ss, rs, hsl, hrw, -, hfor, htin, haux⟩ := compileFromX_mono X P ops (cs.add op o)
    have hro : ∀ r ∈ o.rows, r.Holds w := fun r h =>
      hr r (by
        rw [hrw]; simp only [CS.add, List.reverseAux_eq]
        exact List.mem_append_right _ (List.mem_append_left _ (List.mem_reverse.2 h)))
    have hto : ∀ t ∈ o.tin, ∀ r ∈ Tpl.instRows tc P.one (t.1, cs.tcount t.1, t.2), r.Holds w :=
      fun t htm r hr' => ht _ (htin (by simp only [CS.add, Option.mem_def.1 htm]; simp)) r hr'
    have hpre : ∀ (m : Array Val), (s.regs ++ m).extract 0 cs.slots.size = s.regs := fun m => by
      rw [hI.1.1, Array.extract_append_left, Array.extract_size]
    -- an uncovered import's registers: from `hi`
    have fin : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) → o.imp = true → rt.cov op = false →
        (hl : o.slots.length = vs.length) →
        ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
      intro vs s1 hs1 ⟨m, hm⟩ hio hc hl j hj
      have := hi (cs.slots.size + j) (List.mem_append_left _ (by
        simp only [← ho, hio, hc, Bool.not_false, Bool.and_self, if_true, List.mem_range'_1]; omega))
      have hs := slot_append_right cs.slots o.slots ss hj
      have hv := rd_append_right s.regs vs m (by omega : j < vs.length)
      rw [CS.slot, hsl] at this; simp only [CS.add] at this
      rw [hs, hm, hs1, hI.1.1, hv] at this; exact this
    have flag : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) → o.foreign = true →
        flagOf impl κ inp s.regs op = true := by
      intro vs s1 hs1 ⟨m, hm⟩ hfo
      have := hf (op, cs.slots.size) (hfor (by simp [CS.add, hfo]))
      rwa [hm, hs1, Array.append_assoc, hpre] at this
    have hauxo : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) →
        ∀ a ∈ o.aux, a.1.map (Lin.ev w) = a.2.2.val (rd s.regs a.2.1) := by
      intro vs s1 hs1 ⟨m, hm⟩ a ha
      have := hx (a, cs.slots.size) (haux (by simp [CS.add, ha]))
      rwa [hm, hs1, Array.append_assoc, hpre] at this
    have hstep : (∀ q, evalOp impl κ inp s.regs op ≠ .ask q) ∨ X P cs op = none := by
      rcases hXo : X P cs op with _ | o'
      · exact .inr rfl
      · exact .inl ((hX P cs op o' hXo).2.2 inp w s.regs hP hI.1.2 hI.2.2).1
    have hpos : o.kin.isSome → 0 < o.slots.length := by
      rcases hXo : X P cs op with _ | o'
      · simp [ho, stepOut, hXo, opOut_kin]
      · simp only [ho, stepOut, hXo, Option.getD_some]; exact (hX P cs op o' hXo).2.1
    have hlen : o.slots.length = op.nOut := by
      rcases hXo : X P cs op with _ | o'
      · simp only [ho, stepOut, hXo, Option.getD_none]; exact opOut_len P cs op
      · simp only [ho, stepOut, hXo, Option.getD_some]; exact (hX P cs op o' hXo).1
    have hrr' : ∀ r ∈ repRowsX X P rt (cs.add op o) ops, r.Holds w' :=
      fun r h => hrr r (List.mem_append_right _ h)
    have hi' : ∀ i ∈ impRX X P rt (cs.add op o) ops,
        RepS w ((compileFromX X P (cs.add op o) ops).slot i) (rd s'.regs i) :=
      fun i h => hi i (List.mem_append_right _ h)
    simp only [exec] at he
    split at he
    · rename_i vs ok hev
      have hl := hlen.trans (evalOp_len hev).symm
      have hm := exec_prefix ops _ _ he
      have hsnd : (o.imp = false → List.Forall₂ (RepS w) o.slots vs) ∧ (o.foreign = false → ok = true) ∧
          (∀ f v, o.kin = some f → vs.head? = some v → RepS w (f κ) v) := by
        rcases hXo : X P cs op with _ | o'
        · simp only [ho, stepOut, hXo, Option.getD_none] at hro ⊢
          exact ⟨(opOut_sound hP hI.1.2 op hro hev).1, (opOut_sound hP hI.1.2 op hro hev).2,
            fun f v hf => by rw [opOut_kin] at hf; cases hf⟩
        · have eo : o = o' := by simp [ho, stepOut, hXo]
          rw [eo] at hro hto ⊢
          exact ((hX P cs op o' hXo).2.2 inp w s.regs hP hI.1.2 hI.2.2).2 hro hto
            (eo ▸ hauxo vs _ rfl hm) vs ok hev
      have hnew : ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
        cases hio : o.imp
        · exact fun j hj => (List.forall₂_iff_get.1 (hsnd.1 hio)).2 j hj _
        · cases hc : rt.cov op
          · exact fin vs _ rfl hm hio hc hl
          · have hrows : ∀ r ∈ rt.rows P cs op o.slots, r.Holds w' :=
              fun r h => hrr r (List.mem_append_left _ (by rw [if_pos hc]; exact h))
            exact fun j hj => (List.forall₂_iff_get.1
              ((hR P cs op hc).2 inp w w' s.regs vs ok hP hP' hI hA hrows hev hio)).2 j hj _
      have hok : ok = true := by
        cases hfo : o.foreign
        · exact hsnd.2.1 hfo
        · have := flag vs _ rfl hm hfo; simpa [flagOf, hev] using this
      have ih := compileFromX_soundRW hX hP hP' hA hR ops _ _ s' tr tr'
        (invK_add hI o op hl hnew hsnd.2.2 hpos) he hr ht hx hi' hrr' hf
      exact ⟨by rw [ih.1, hok, Bool.and_true], ih.2⟩
    · rename_i q hev
      have hXn : X P cs op = none := hstep.resolve_left fun h => h q hev
      have ho' : o = opOut P cs op := by simp [ho, stepOut, hXn]
      have hc : rt.cov op = false := by
        cases hc : rt.cov op
        · rfl
        · exact absurd hev ((hR P cs op hc).1 inp s.regs q)
      split at he
      · simp at he
      · rename_i q' a tr0
        split at he
        · have hio : o.imp = true := ho' ▸ ask_imp P cs hev
          have hl : o.slots.length = [Val.d a].length := by
            rw [hlen, ask_nOut hev]; rfl
          have hm := exec_prefix ops _ _ he
          have hnew := fin [.d a] ⟨s.regs.push (.d a), s.ok⟩ rfl hm hio hc hl
          exact compileFromX_soundRW hX hP hP' hA hR ops _ ⟨s.regs.push (.d a), s.ok⟩ s' tr0 tr'
            (invK_add hI o op hl hnew (fun f v hf => by rw [ho', opOut_kin] at hf; cases hf) hpos)
            he hr ht hx hi' hrr' hf
        · simp at he

/-- **`compileX_soundR` with the replay rows at `w'`.** -/
theorem compileX_soundRW {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w w' : Asg} {B : ℕ} {P : Params} {tc : Tpl.TCtx} {X : Ext} {rt : RT} (hX : ExtOkK impl tc X κ)
    (hR : RTOkW impl X rt κ B) (base : ℕ) (hP : SelOk w P κ) (hP' : SelOk w' P κ) (hA : Agree B w w')
    (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileX X P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileX X P base ops).tplRows tc P.one, r.Holds w)
    (hx : ∀ a ∈ (compileX X P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ impRX X P rt (CS.init base) ops, RepS w ((compileX X P base ops).slot i) (rd s.regs i))
    (hrr : ∀ r ∈ repRowsX X P rt (CS.init base) ops, r.Holds w')
    (hf : ∀ p ∈ (compileX X P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compileX X P base ops).slot i) (rd s.regs i) := by
  have h := compileFromX_soundRW hX hP hP' hA hR ops (CS.init base) St.init s tr tr'
    ⟨⟨rfl, fun i => by simp [CS.slot, CS.init, RepS]⟩, fun p hp => by simp [CS.init] at hp,
      fun i => by simp [CS.slotK, CS.slot, CS.init, RepS]⟩ he hr
    (fun t htm r hr' => ht r (List.mem_flatMap.2 ⟨t, htm, hr'⟩)) hx hi hrr hf
  exact ⟨h.1, h.2.1.2⟩

end Circ

/-! ## At the node's slots -/

namespace N4s
open RecursionFast Rev4 Circ

theorem protoCS_X (π : ℕ) : protoCS π = compileX (Xof π) (protoP π) (baseR π) (protoProg π).ops := rfl

/-- Prototype `π`'s import registers `rt` does not cover. -/
def impRP (rt : RT) (π : ℕ) : List ℕ := impRX (Xof π) (protoP π) rt (CS.init (baseR π)) (protoProg π).ops

/-- **`SlotRun` with the covered imports removed**: only the registers of `impRP` are assumed. -/
def SlotRunR (rt : RT) (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) (tr : Trace) (w : Asg) : Prop :=
  ∃ s : St, exec impl ι inp (protoProg π).ops St.init tr = some (s, []) ∧
    (∀ a ∈ (protoCS π).aux, a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)) ∧
    (∀ i ∈ impRP rt π, RepS w ((protoCS π).slot i) (rd s.regs i)) ∧
    (∀ p ∈ (protoCS π).fors, flagOf impl ι inp (s.regs.extract 0 p.2) p.1 = true)

/-- **`SlotImp` with the covered imports removed** (`rt π` per prototype). -/
def SlotImpR (rt : ℕ → RT) (impl₀ : OpImpl) (base : NodeKind → OpImpl) (κ : NodeKind) (v : ℕ) (w : Asg)
    (inp : Input) (tr : Trace) : Prop :=
  ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
    SlotRunR (rt (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι inp tr (slotAsg κ v w) ∧
      stmtOk4 seq4 (kindP (protoOf κ v) ι) inp = true

/-- **The replay rows hold** at slot `v` (in its prototype's frame; REPF: at the replay assignment
`w ∘ repMapC κ v`, C1's `repAsg`: the slot's frame below `repB`, the spare region above). -/
def RepHolds (rt : ℕ → RT) (κ : NodeKind) (v : ℕ) (w : Asg) : Prop :=
  ∀ r ∈ repRowsP (rt (protoOf κ v)) (protoOf κ v), r.Holds (w ∘ repMapC κ v)

/-- **The templates are sound** for every prototype and index (under `implP`; REPF: `RTOkW` at
`repB`, the rows at an assignment agreeing with the slot's below the frame bound). -/
def RepOk (rt : ℕ → RT) (impl₀ : OpImpl) (base : NodeKind → OpImpl) : Prop :=
  ∀ π ≤ 1, ∀ ι, RTOkW (implP impl₀ base π ι) (Xof π) (rt π) ι repB

/-- (+) The converse: `SlotImp` gives `SlotImpR` (an uncovered import is an import), so
`SlotImpR` asks nothing `SlotImp` does not. -/
theorem slotImpR_of_imp (rt : ℕ → RT) {impl₀ : OpImpl} {base : NodeKind → OpImpl} {κ : NodeKind}
    {v : ℕ} {w : Asg} {inp : Input} {tr : Trace} (h : SlotImp impl₀ base κ v w inp tr) :
    SlotImpR rt impl₀ base κ v w inp tr := by
  intro ι hS
  obtain ⟨⟨s, he, hx, hi, hf⟩, hst⟩ := h ι hS
  exact ⟨⟨s, he, hx, fun i hm => hi i (impRX_sub _ _ _ _ _ i hm), hf⟩, hst⟩

/-! ## The node's indexed replay rows (JOURNAL §0) -/

/-- **Slot `v`'s replay rows** (absolute cells; REPF: `repIRowsW`'s placement, slot 0's in the spare
region, a segment slot's at `v·2^20 + segRow k` (SEG-R2), cells by `repMapC`). -/
def repIRows4 (rt : ℕ → RT) (κ : NodeKind) (v : ℕ) : List (ℕ × Row) :=
  (repRowsP (rt (protoOf κ v)) (protoOf κ v)).zipIdx.map fun p =>
    (repRowI κ v p.2, rowMapC (repMapC κ v) p.1)

/-- Every element of `l` has its image in `l.zipIdx.map g` (generic, so that no list is evaluated). -/
theorem mem_zipIdx_map {α β : Type*} {l : List α} {r : α} (hr : r ∈ l) (g : α × ℕ → β) :
    ∃ k, g (r, k) ∈ l.zipIdx.map g := by
  obtain ⟨k, hkl, hrk⟩ := List.mem_iff_getElem.1 hr
  refine ⟨k, List.mem_map_of_mem (List.mem_iff_getElem.2 ⟨k, by rw [List.length_zipIdx]; exact hkl, ?_⟩)⟩
  rw [List.getElem_zipIdx, hrk]; simp

end N4s
end FR

end G6_FRNodeRows4Rep

section G6_FRNodeRows4RepS

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.11's replay templates; stage S-E14, track
-- L-circ).

/-!
# The first replay template: a segment slot's `linkWAll`

A segment slot runs its ops at `L32` (`implP … 1 ι = (implSeg impl₀).fixK .L32`), and a leaf kind's
`linkWAll` is `0^8` (`Impl.implCWith`: the WOTS link families exist only in a node). So the replay
of prototype 1's `linkWAll` import is eight rows `one · out_j = 0` on its `af 8` output cells
(**`zeroRows`**; any other output slot gets the rejecting row `one · one = 0`).

* **`rtLinkSeg`** covers `linkWAll`; **`rtSeg π`** is it at prototype 1 and `RT.none` at prototype 0
  (the previous node's `linkWAll` is `linkWAll4I ν`, JOURNAL §1.4).
* **`rtLinkSeg_ok`**: `RTOk` at every index, given that the base's `linkWAll` at `L32` is `0^8`
  (**`LinkZero impl₀`**; `linkZero_implC`: it holds at the submission's `implC`).
* (REPF: `repOk_rtSeg` removed: `RepOk` is now the `RTOkW` form, which `rtLinkSeg`, without its
  output cells' bound check, does not meet; `FRNodeRows4RepN.rtLinkSegW` is its checked form.)
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ

/-- **The segment's `linkWAll` replay.** -/
def rtLinkSeg : RT := ⟨isLinkW, fun P _ op outs => if isLinkW op then zeroRows P outs else []⟩

/-- **The replay templates per prototype**: the segment's `linkWAll` at prototype 1. -/
def rtSeg (π : ℕ) : RT := if π = 1 then rtLinkSeg else RT.none

/-- The base reads a leaf kind's `linkWAll` as `0^8`. -/
def LinkZero (impl₀ : OpImpl) : Prop := ∀ tt rr, impl₀.linkWAll .L32 tt rr = Array.replicate nLinkFam 0

theorem linkZero_implC (fin : Finals) (lRows : List Row) (κs₀ : F) : LinkZero (Impl.implC fin lRows κs₀) :=
  fun _ _ => rfl

/-- The rejecting row does not hold where `one = 1`. -/
theorem rej_not {P : Params} {w : Asg} (hone : P.one.ev w = 1) : ¬ (⟨P.one, P.one, []⟩ : Row).Holds w := by
  simp [Row.Holds, hone]

/-- **`zeroRows` gives `0^8`**: where they hold (with `one = 1`), the slot list represents
`[af 0^8]`. -/
theorem zeroRows_sound {P : Params} {w : Asg} (hone : P.one.ev w = 1) {outs : List Slot}
    (h : ∀ r ∈ zeroRows P outs, r.Holds w) :
    List.Forall₂ (RepS w) outs [.af (Array.replicate nLinkFam 0)] := by
  have rej : ∀ {l : List Row}, (⟨P.one, P.one, []⟩ : Row) ∈ l → (∀ r ∈ l, r.Holds w) → False :=
    fun hm h' => rej_not hone (h' _ hm)
  match outs, h with
  | [some (t, ls)], h =>
    by_cases hl : t = .af 8 ∧ ls.length = 8
    · obtain ⟨rfl, hl⟩ := hl
      simp only [zeroRows, hl, and_self, if_true] at h
      refine List.Forall₂.cons ⟨by simp [tyOf, nLinkFam], ?_⟩ List.Forall₂.nil
      have hz : ∀ l ∈ ls, l.ev w = 0 := fun l hm => by
        have := h _ (List.mem_map_of_mem hm); simpa [Row.Holds, hone] using this
      simp only [encV, Array.toList_replicate, nLinkFam]
      refine List.ext_getElem (by simp [hl]) fun j h1 h2 => ?_
      simp only [List.getElem_map, List.getElem_replicate]
      exact hz _ (List.getElem_mem _)
    · simp only [zeroRows, hl, if_false] at h
      exact (rej (List.mem_singleton_self _) h).elim
  | [], h => exact (rej (by simp [zeroRows]) h).elim
  | [none], h => exact (rej (by simp [zeroRows]) h).elim
  | _ :: _ :: _, h => exact (rej (by simp [zeroRows]) h).elim

/-- **The segment's `linkWAll` replay is sound** at every index, under `LinkZero`. -/
theorem rtLinkSeg_ok {impl₀ : OpImpl} (base : NodeKind → OpImpl) (hZ : LinkZero impl₀) (ι : Kind) :
    RTOk (implP impl₀ base 1 ι) (Xof 1) rtLinkSeg ι := by
  intro P cs op hc
  cases op
  all_goals first
    | (simp [rtLinkSeg, isLinkW] at hc)
    | skip
  rename_i t p
  refine ⟨fun inp regs q => by simp [evalOp], fun inp w regs vs ok hP _ hrows hev _ => ?_⟩
  simp only [evalOp, Res.vals.injEq] at hev
  obtain ⟨rfl, -⟩ := hev
  have hv : (implP impl₀ base 1 ι).linkWAll ι (rd regs t).toAF (rd regs p).toAF =
      Array.replicate nLinkFam 0 := by
    simp only [implP, one_ne_zero, if_false, OpImpl.fixK, implSeg]; exact hZ _ _
  rw [hv]
  exact zeroRows_sound hP.1 (fun r hr => hrows r (by simp only [rtLinkSeg, isLinkW, if_true]; exact hr))

end N4s
end FR

end G6_FRNodeRows4RepS

section G6_FRNodeRun4

-- New for `flock-recursive` (PACK-4.4 §4, B4's theorem; track B3). The trace-building twin of
-- S-E14's `compileFromX_soundR` (`FRNodeRows4Rep`).

/-!
# The run's existence on a read trace (`compileFromX_run`)

S-N2's `SlotRun` asks for `exec impl ι inp ops St.init tr = some (s, [])` on the trace `tr` the
reader takes off H. `exec` stops only at an ask whose computed query differs from the trace entry's
(or when the trace runs out). So the run exists iff every ask's query, computed from the registers,
is the trace's. This module proves it along the compile's trail, never by evaluating a program:

* **`execA`**, the **answer-driven run**: `exec` without the query comparison (each ask binds the
  trace entry's answer). It exists as soon as the trace has an entry per ask (`execA_some`), and
  its final state is a function of the trace alone, so the run facts `SlotRun` needs (auxiliary,
  import, foreign) are stated on it.
* **`AT`** (an ask template: rows per compile state, previous op, op and ask index; `cov` the
  non-ask ops whose imports it binds) and **`ATOk = ATAsk ∧ ATImp`**: at an ask whose rows hold,
  with the invariant `InvK` at the op and the previous op's results last in the registers
  (`PrevOk`), the trace entry's query is the computed one and the answer slots represent its answer
  (`ATAsk`); at a covered op, its import slots represent its results at the fixed input (`ATImp`:
  the proof fields, challenge halves, bits and inputs of PACK-4.4 §1.3, which S-E14's `RTOk`, being
  quantified over every input, cannot bind). **`AskBound`** is `ATAsk` split per ask constructor
  (`seed`, `absorb`, `squeeze`, `node`, `col`, and the answer `ans`; `atAsk_of_askBound`). Its
  fields are the interface the row side (FS links, Merkle mux rows, pins and the H bridge) meets;
  `rd_of_cells`, `rd_of_piField`, `absorbQ_of_links`, `squeezeQ_of_links`, `nodeQ_of_mux`,
  `seedQ_of_pre`, `colQ_of_pre`, `ans_of_cells` reduce each field to a per-item fact on cells.
* **`askRowsX`**, **`impAX`**: the template's rows along the trail, and the import registers that
  are neither asks nor covered by `A` or by a replay template `RT`.
* **`compileFromX_run`** (the induction) and **`compileX_run`**: with the rows, the templates, the
  replay rows, the ask rows and the residual facts on `execA`'s final state, `exec` runs to that
  state and every register is represented.

The previous op is passed because an ask's byte operand (`hdr`, an absorb's message, a column) is an
untracked register (a `Val.b`): in every generator it is the `piField` just before the ask
(`prev_piField` reads it).
-/

namespace FR
namespace Circ
open RecursionFast

/-! ## The answer-driven run -/

/-- **The answer-driven run**: `exec`, except that an ask binds the trace entry's answer without
comparing its query. -/
def execA (impl : OpImpl) (κ : Kind) (inp : Input) : List Op → St → Trace → Option (St × Trace)
  | [], s, tr => some (s, tr)
  | op :: ops, s, tr =>
    match evalOp impl κ inp s.regs op with
    | .vals vs ok => execA impl κ inp ops ⟨s.regs ++ vs.toArray, s.ok && ok⟩ tr
    | .ask _ =>
      match tr with
      | [] => none
      | (_, a) :: tr' => execA impl κ inp ops ⟨s.regs.push (.d a), s.ok⟩ tr'

section Run
variable {impl : OpImpl} {κ : Kind} {inp : Input}

theorem ask_item {regs : Array Val} {op : Op} {q : ByteArray} (h : evalOp impl κ inp regs op = .ask q) :
    op.item?.isSome = true := by
  cases op <;> simp only [evalOp, reduceCtorEq] at h <;> rfl

theorem vals_item' {regs : Array Val} {op : Op} {vs : List Val} {ok : Bool}
    (h : evalOp impl κ inp regs op = .vals vs ok) : op.item?.isSome = false := by
  cases op <;> simp only [evalOp, reduceCtorEq] at h <;> rfl

/-- (+) **A run is the answer-driven run**: `execA` assumes nothing `exec` does not. -/
theorem execA_of_exec : ∀ (ops : List Op) (s : St) (tr : Trace) {r : St × Trace},
    exec impl κ inp ops s tr = some r → execA impl κ inp ops s tr = some r
  | [], s, tr, r, h => h
  | op :: ops, s, tr, r, h => by
    simp only [exec] at h
    simp only [execA]
    split at h
    · next vs ok hv => rw [hv]; exact execA_of_exec ops _ tr h
    · next q hq =>
      rw [hq]
      rcases tr with _ | ⟨⟨q', a⟩, tr'⟩
      · cases h
      · simp only at h ⊢
        split_ifs at h
        exact execA_of_exec ops _ tr' h

/-- **The answer-driven run exists** when the trace has an entry per ask; it leaves the rest. -/
theorem execA_some : ∀ (ops : List Op) (s : St) (tr : Trace),
    (ops.filterMap Op.item?).length ≤ tr.length →
    ∃ s', execA impl κ inp ops s tr = some (s', tr.drop (ops.filterMap Op.item?).length)
  | [], s, tr, _ => ⟨s, rfl⟩
  | op :: ops, s, tr, hl => by
    simp only [execA]
    split
    · next vs ok hv =>
      have hi : op.item? = none := by simpa using vals_item' hv
      simp only [List.filterMap_cons, hi] at hl ⊢
      exact execA_some ops _ tr hl
    · next q hq =>
      obtain ⟨it, hit⟩ := Option.isSome_iff_exists.1 (ask_item hq)
      simp only [List.filterMap_cons, hit, List.length_cons] at hl ⊢
      rcases tr with _ | ⟨⟨q', a⟩, tr'⟩
      · simp at hl
      · simp only [List.length_cons, add_le_add_iff_right] at hl
        simpa using execA_some ops _ tr' hl

theorem execA_prefix : ∀ (ops : List Op) (s : St) (tr : Trace) {s' : St} {tr' : Trace},
    execA impl κ inp ops s tr = some (s', tr') → ∃ more : Array Val, s'.regs = s.regs ++ more
  | [], s, tr, s', tr', h => by simp [execA] at h; exact ⟨#[], by simp [← h.1]⟩
  | op :: ops, s, tr, s', tr', h => by
    simp only [execA] at h
    split at h
    · next vs _ _ =>
      obtain ⟨m, hm⟩ := execA_prefix ops _ _ h
      exact ⟨vs.toArray ++ m, by rw [hm, Array.append_assoc]⟩
    · rcases tr with _ | ⟨⟨q', a⟩, tr0⟩
      · cases h
      · obtain ⟨m, hm⟩ := execA_prefix ops _ _ h
        exact ⟨#[.d a] ++ m, by rw [hm, Array.push_eq_append, Array.append_assoc]⟩

end Run

/-! ## Ask templates and their obligation -/

/-- **The previous op's results are the last registers** (`none`: no previous op). -/
def PrevOk (impl : OpImpl) (κ : Kind) (inp : Input) : Option Op → Array Val → Prop
  | none, _ => True
  | some p, regs => ∃ r₀ : Array Val,
      (∃ vs ok, evalOp impl κ inp r₀ p = .vals vs ok ∧ regs = r₀ ++ vs.toArray) ∨
      (∃ q a, evalOp impl κ inp r₀ p = .ask q ∧ regs = r₀.push (.d a))

/-- **An ask template**: for a compile state, the previous op, an op and the asks before it (an
ask's entry in the trace), rows. At an ask they bind the query to the entry and the answer slots to
its answer; at a covered op (`cov`, not an ask) they bind its import slots to its results. -/
structure AT where
  cov : Op → Bool
  rows : Params → CS → Option Op → Op → ℕ → List Row

/-- The template with no rows, covering nothing. -/
def AT.none : AT := ⟨fun _ => false, fun _ _ _ _ _ => []⟩

/-- **The context of a templated op**: the selector, the invariant at the op, the previous op's
results last, the template's rows. -/
def AskCtx (impl : OpImpl) (A : AT) (κ : Kind) (inp : Input) (w : Asg) (P : Params) (cs : CS)
    (pre : Option Op) (op : Op) (k : ℕ) (regs : Array Val) : Prop :=
  SelOk w P κ ∧ InvK w cs regs κ ∧ PrevOk impl κ inp pre regs ∧ ∀ r ∈ A.rows P cs pre op k, r.Holds w

/-- **The asks are sound for the trace `tr`**: at every ask in its context, entry `k` of `tr` has
the computed query, and the answer slots represent its answer. -/
def ATAsk (impl : OpImpl) (X : Ext) (A : AT) (κ : Kind) (inp : Input) (w : Asg) (tr : Trace) : Prop :=
  ∀ P cs pre op k regs q e, AskCtx impl A κ inp w P cs pre op k regs →
    evalOp impl κ inp regs op = .ask q → tr[k]? = some e →
    e.1 = q ∧ List.Forall₂ (RepS w) (stepOut X P cs op).slots [.d e.2]

/-- **The covered imports are sound at the input `inp`**: a covered op's import slots represent
its results in its context. -/
def ATImp (impl : OpImpl) (X : Ext) (A : AT) (κ : Kind) (inp : Input) (w : Asg) : Prop :=
  ∀ P cs pre op k regs vs ok, A.cov op = true → AskCtx impl A κ inp w P cs pre op k regs →
    evalOp impl κ inp regs op = .vals vs ok → (stepOut X P cs op).imp = true →
    List.Forall₂ (RepS w) (stepOut X P cs op).slots vs

/-- **An ask template is sound for `inp` and the trace `tr`.** -/
def ATOk (impl : OpImpl) (X : Ext) (A : AT) (κ : Kind) (inp : Input) (w : Asg) (tr : Trace) : Prop :=
  ATAsk impl X A κ inp w tr ∧ ATImp impl X A κ inp w

/-- **`ATAsk` per ask constructor**: what the rows of each ask (with the H bridge) must give. The
query facts are `evalOp`'s queries at the registers; `ans` is the answer's representation. -/
structure AskBound (impl : OpImpl) (X : Ext) (A : AT) (κ : Kind) (inp : Input) (w : Asg) (tr : Trace) :
    Prop where
  /-- The seed: `"FRSEED0" ‖ vk ‖ c ‖ hdr`. -/
  seed : ∀ P cs pre h k regs e, AskCtx impl A κ inp w P cs pre (.askSeed h) k regs → tr[k]? = some e →
    e.1 = seedQ inp.vk inp.c (rd regs h).toB
  /-- An absorb: its state register's digest and its message. -/
  absorb : ∀ P cs pre st m len k regs e, AskCtx impl A κ inp w P cs pre (.askAbsorb st m len) k regs →
    tr[k]? = some e → e.1 = absorbQ (rd regs st).toD (rd regs m).toB
  /-- A squeeze: its state register's digest. -/
  squeeze : ∀ P cs pre st k regs e, AskCtx impl A κ inp w P cs pre (.askSqueeze st) k regs →
    tr[k]? = some e → e.1 = squeezeQ (rd regs st).toD
  /-- A Merkle node: its halves (`0^64` where the depth is inactive). -/
  node : ∀ P cs pre i h l r act k regs e, AskCtx impl A κ inp w P cs pre (.askNode i h l r act) k regs →
    tr[k]? = some e →
    e.1 = if act κ then nodeQF i (rd regs l).toD (rd regs r).toD else nodeQF i zeroD zeroD
  /-- A column: its bytes. -/
  col : ∀ P cs pre i c k regs e, AskCtx impl A κ inp w P cs pre (.askCol i c) k regs →
    tr[k]? = some e → e.1 = colQ i (rd regs c).toB
  /-- Every ask's answer slots represent the entry's answer. -/
  ans : ∀ P cs pre op k regs e, op.item?.isSome = true → AskCtx impl A κ inp w P cs pre op k regs →
    tr[k]? = some e → List.Forall₂ (RepS w) (stepOut X P cs op).slots [.d e.2]

/-- **The per-constructor obligations give `ATAsk`.** -/
theorem atAsk_of_askBound {impl : OpImpl} {X : Ext} {A : AT} {κ : Kind} {inp : Input} {w : Asg}
    {tr : Trace} (h : AskBound impl X A κ inp w tr) : ATAsk impl X A κ inp w tr := by
  intro P cs pre op k regs q e hc hq he
  refine ⟨?_, h.ans P cs pre op k regs e (ask_item hq) hc he⟩
  cases op <;> simp only [evalOp, reduceCtorEq, Res.ask.injEq] at hq <;> subst hq
  · exact h.seed _ _ _ _ _ _ _ hc he
  · exact h.absorb _ _ _ _ _ _ _ _ _ hc he
  · exact h.squeeze _ _ _ _ _ _ _ hc he
  · exact h.node _ _ _ _ _ _ _ _ _ _ _ hc he
  · exact h.col _ _ _ _ _ _ _ _ hc he

/-- (+) The converse: `ATAsk` gives every field, so `AskBound` asks nothing more. -/
theorem askBound_of_atAsk {impl : OpImpl} {X : Ext} {A : AT} {κ : Kind} {inp : Input} {w : Asg}
    {tr : Trace} (h : ATAsk impl X A κ inp w tr) : AskBound impl X A κ inp w tr where
  seed _ _ _ _ _ _ _ hc he := (h _ _ _ _ _ _ _ _ hc rfl he).1
  absorb _ _ _ _ _ _ _ _ _ hc he := (h _ _ _ _ _ _ _ _ hc rfl he).1
  squeeze _ _ _ _ _ _ _ hc he := (h _ _ _ _ _ _ _ _ hc rfl he).1
  node _ _ _ _ _ _ _ _ _ _ _ hc he := (h _ _ _ _ _ _ _ _ hc rfl he).1
  col _ _ _ _ _ _ _ _ hc he := (h _ _ _ _ _ _ _ _ hc rfl he).1
  ans P cs pre op k regs e hi hc he := by
    obtain ⟨it, hit⟩ := Option.isSome_iff_exists.1 hi
    cases op <;> simp only [Op.item?, reduceCtorEq] at hit <;>
      exact (h _ _ _ _ _ _ _ _ hc rfl he).2

/-! ## Facts a template uses -/

/-- **A byte operand read off the previous `piField`**: the last register holds its bytes. -/
theorem prev_piField {impl : OpImpl} {κ : Kind} {inp : Input} {f o len : ℕ} {regs : Array Val}
    (h : PrevOk impl κ inp (some (.piField f o len)) regs) :
    rd regs (regs.size - 1) = .b (inp.π.extract (absOff f o) (absOff f o + len)) := by
  obtain ⟨r₀, ⟨vs, ok, hv, rfl⟩ | ⟨q, a, hq, -⟩⟩ := h
  · simp only [evalOp, Res.vals.injEq] at hv
    obtain ⟨rfl, -⟩ := hv
    simp [rd]
  · simp [evalOp] at hq

/-- **A register's slot at `κ` represents it** (the invariant, read at one register). -/
theorem rep_of_invK {w : Asg} {cs : CS} {regs : Array Val} {κ : Kind} (h : InvK w cs regs κ) (i : ℕ) :
    RepS w (cs.slotK i κ) (rd regs i) :=
  h.2.2 i

/-- **A digest slot's two cells determine the digest.** -/
theorem digest_of_rep {w : Asg} {l₀ l₁ : Lin} {v : Val} {x : Digest}
    (h : RepS w (some (.d, [l₀, l₁])) v) (h₀ : l₀.ev w = dlo x) (h₁ : l₁.ev w = dhi x) : v = .d x := by
  obtain ⟨ht, he⟩ := h
  cases v <;> simp only [tyOf, Option.some.injEq, reduceCtorEq] at ht
  rename_i y
  simp only [List.map_cons, List.map_nil, encV, List.cons.injEq, and_true] at he
  rw [digest_ext (he.1.symm.trans h₀) (he.2.symm.trans h₁)]

/-! ## The per-item facts that meet `AskBound`

Each field of `AskBound` reduces to a fact about the trace entry and the cells (the row side's
FS links, Merkle mux rows and pins, with the H bridge): a digest operand is read off its slot's two
cells (`rd_of_cells`), a byte operand off the `piField` before the ask (`prev_piField`), and the
answer slot's cells carry the entry's answer (`ans_of_cells`). -/

section Items
variable {impl : OpImpl} {A : AT} {κ : Kind} {inp : Input} {w : Asg} {P : Params} {cs : CS}
  {pre : Option Op} {op : Op} {k : ℕ} {regs : Array Val}

/-- **A digest operand is the digest its cells carry.** -/
theorem rd_of_cells (hc : AskCtx impl A κ inp w P cs pre op k regs) {i : ℕ} {l₀ l₁ : Lin} {x : Digest}
    (hs : cs.slotK i κ = some (.d, [l₀, l₁])) (h₀ : l₀.ev w = dlo x) (h₁ : l₁.ev w = dhi x) :
    rd regs i = .d x :=
  digest_of_rep (hs ▸ rep_of_invK hc.2.1 i) h₀ h₁

/-- **The byte operand just appended by the previous `piField`.** -/
theorem rd_of_piField {f o len : ℕ} (hc : AskCtx impl A κ inp w P cs (some (.piField f o len)) op k regs) {m : ℕ}
    (hm : m + 1 = cs.slots.size) : rd regs m = .b (inp.π.extract (absOff f o) (absOff f o + len)) := by
  have := prev_piField hc.2.2.1
  rwa [show regs.size - 1 = m by rw [← hc.2.1.1.1]; omega] at this

/-- **The FS link at an absorb**: its state cells carry `x` and its message is the previous
`piField`'s, so its query is `absorbQ x (π's bytes)`. -/
theorem absorbQ_of_links {f o len' st m len : ℕ}
    (hc : AskCtx impl A κ inp w P cs (some (.piField f o len')) (.askAbsorb st m len) k regs)
    (hm : m + 1 = cs.slots.size) {l₀ l₁ : Lin} {x : Digest} (hs : cs.slotK st κ = some (.d, [l₀, l₁]))
    (h₀ : l₀.ev w = dlo x) (h₁ : l₁.ev w = dhi x) :
    absorbQ (rd regs st).toD (rd regs m).toB = absorbQ x (inp.π.extract (absOff f o) (absOff f o + len')) := by
  rw [rd_of_cells hc hs h₀ h₁, rd_of_piField hc hm]; rfl

/-- **The FS link at a squeeze.** -/
theorem squeezeQ_of_links {st : ℕ} (hc : AskCtx impl A κ inp w P cs pre (.askSqueeze st) k regs)
    {l₀ l₁ : Lin} {x : Digest} (hs : cs.slotK st κ = some (.d, [l₀, l₁])) (h₀ : l₀.ev w = dlo x)
    (h₁ : l₁.ev w = dhi x) : squeezeQ (rd regs st).toD = squeezeQ x := by
  rw [rd_of_cells hc hs h₀ h₁]; rfl

/-- **The Merkle mux at a node**: its halves' cells carry `x`, `y` (the half at the index bit is
the previous answer, the other the sibling), so its query is `nodeQF i x y`. -/
theorem nodeQ_of_mux {i h l r : ℕ} {act : KC Bool}
    (hc : AskCtx impl A κ inp w P cs pre (.askNode i h l r act) k regs) {l₀ l₁ r₀ r₁ : Lin} {x y : Digest}
    (hl : cs.slotK l κ = some (.d, [l₀, l₁])) (hl₀ : l₀.ev w = dlo x) (hl₁ : l₁.ev w = dhi x)
    (hr : cs.slotK r κ = some (.d, [r₀, r₁])) (hr₀ : r₀.ev w = dlo y) (hr₁ : r₁.ev w = dhi y) :
    nodeQF i (rd regs l).toD (rd regs r).toD = nodeQF i x y := by
  rw [rd_of_cells hc hl hl₀ hl₁, rd_of_cells hc hr hr₀ hr₁]; rfl

/-- **The seed's header is the previous `piField`'s bytes.** -/
theorem seedQ_of_pre {f o len hd : ℕ} (hc : AskCtx impl A κ inp w P cs (some (.piField f o len)) (.askSeed hd) k regs)
    (hm : hd + 1 = cs.slots.size) :
    seedQ inp.vk inp.c (rd regs hd).toB = seedQ inp.vk inp.c (inp.π.extract (absOff f o) (absOff f o + len)) := by
  rw [rd_of_piField hc hm]; rfl

/-- **A column is the previous `piField`'s bytes.** -/
theorem colQ_of_pre {f o len i c : ℕ} (hc : AskCtx impl A κ inp w P cs (some (.piField f o len)) (.askCol i c) k regs)
    (hm : c + 1 = cs.slots.size) :
    colQ i (rd regs c).toB = colQ i (inp.π.extract (absOff f o) (absOff f o + len)) := by
  rw [rd_of_piField hc hm]; rfl

/-- **The answer's cells carry the entry's answer.** -/
theorem ans_of_cells {X : Ext} {l₀ l₁ : Lin} {a : Digest}
    (hs : (stepOut X P cs op).slots = [some (.d, [l₀, l₁])]) (h₀ : l₀.ev w = dlo a) (h₁ : l₁.ev w = dhi a) :
    List.Forall₂ (RepS w) (stepOut X P cs op).slots [.d a] := by
  rw [hs]; exact .cons ⟨rfl, by simp [encV, h₀, h₁]⟩ .nil

end Items

/-! ## Along the trail -/

/-- **The ask rows along the compile's trail** (the alignment and the step exactly as
`compileFromX`; `pre` the previous op, `k` the asks so far). -/
def askRowsX (X : Ext) (P : Params) (A : AT) : CS → Option Op → ℕ → List Op → List Row
  | _, _, _, [] => []
  | cs, pre, k, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if op.item?.isSome || A.cov op then A.rows P c pre op k else []) ++
      askRowsX X P A (c.add op (stepOut X P c op)) (some op) (if op.item?.isSome then k + 1 else k) ops

/-- **The import registers neither an ask nor covered by `rt` or `A`**, along the trail. -/
def impAX (X : Ext) (P : Params) (rt : RT) (A : AT) : CS → List Op → List ℕ
  | _, [] => []
  | cs, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if (stepOut X P c op).imp && !rt.cov op && !A.cov op && !op.item?.isSome then
        List.range' c.slots.size (stepOut X P c op).slots.length else []) ++
      impAX X P rt A (c.add op (stepOut X P c op)) ops

theorem askRowsX_cons (X : Ext) (P : Params) (A : AT) (cs : CS) (pre : Option Op) (k : ℕ) (op : Op)
    (ops : List Op) :
    askRowsX X P A cs pre k (op :: ops) =
      (if op.item?.isSome || A.cov op then A.rows P (cs.align (alignOf op ops)) pre op k else []) ++
        askRowsX X P A ((cs.align (alignOf op ops)).add op (stepOut X P (cs.align (alignOf op ops)) op))
          (some op) (if op.item?.isSome then k + 1 else k) ops :=
  rfl

theorem impAX_cons (X : Ext) (P : Params) (rt : RT) (A : AT) (cs : CS) (op : Op) (ops : List Op) :
    impAX X P rt A cs (op :: ops) =
      (if (stepOut X P (cs.align (alignOf op ops)) op).imp && !rt.cov op && !A.cov op && !op.item?.isSome then
          List.range' (cs.align (alignOf op ops)).slots.size
            (stepOut X P (cs.align (alignOf op ops)) op).slots.length else []) ++
        impAX X P rt A ((cs.align (alignOf op ops)).add op (stepOut X P (cs.align (alignOf op ops)) op)) ops :=
  rfl

/-- **The residual imports are uncovered imports** (`impAX ⊆ impRX`), so they ask nothing new. -/
theorem impAX_sub (X : Ext) (P : Params) (rt : RT) (A : AT) :
    ∀ (ops : List Op) (cs : CS), ∀ i ∈ impAX X P rt A cs ops, i ∈ impRX X P rt cs ops
  | [], _, i, h => by simp [impAX] at h
  | op :: ops, cs, i, h => by
    rw [impAX_cons, List.mem_append] at h
    rw [impRX_cons, List.mem_append]
    rcases h with h | h
    · refine .inl ?_
      split_ifs at h with hc
      · simp only [Bool.and_eq_true] at hc
        rw [if_pos (by simp only [Bool.and_eq_true]; exact hc.1.1)]; exact h
      · simp at h
    · exact .inr (impAX_sub X P rt A ops _ i h)

theorem drop_cons_get {tr : Trace} {k : ℕ} {e : ByteArray × Digest} {t : Trace}
    (h : tr.drop k = e :: t) : tr[k]? = some e ∧ t = tr.drop (k + 1) := by
  constructor
  · rw [← List.head?_drop, h]; rfl
  · rw [← List.drop_drop, h]; rfl

/-! ## The run -/

/-- **The run along the compile's trail** (`compileFromX_soundR` with the trace threaded): the
answer-driven run from entry `k` is `exec`'s, and the invariant holds at its end. -/
theorem compileFromX_run {impl : OpImpl} {κ : Kind} {inp : Input} {w w' : Asg} {B : ℕ} {P : Params}
    {tc : Tpl.TCtx} {X : Ext} {rt : RT} {A : AT} {tr : Trace} (hX : ExtOkK impl tc X κ)
    (hP : SelOk w P κ) (hP' : SelOk w' P κ) (hAg : Agree B w w') (hR : RTOkW impl X rt κ B)
    (hA : ATOk impl X A κ inp w tr) :
    ∀ (ops : List Op) (cs : CS) (pre : Option Op) (k : ℕ) (s s' : St) (tr' : Trace),
    InvK w cs s.regs κ → PrevOk impl κ inp pre s.regs →
    execA impl κ inp ops s (tr.drop k) = some (s', tr') →
    (∀ r ∈ (compileFromX X P cs ops).rows, r.Holds w) →
    (∀ t ∈ (compileFromX X P cs ops).tins, ∀ r ∈ Tpl.instRows tc P.one t, r.Holds w) →
    (∀ a ∈ (compileFromX X P cs ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s'.regs.extract 0 a.2) a.1.2.1)) →
    (∀ i ∈ impAX X P rt A cs ops, RepS w ((compileFromX X P cs ops).slot i) (rd s'.regs i)) →
    (∀ r ∈ repRowsX X P rt cs ops, r.Holds w') →
    (∀ r ∈ askRowsX X P A cs pre k ops, r.Holds w) →
    (∀ p ∈ (compileFromX X P cs ops).fors,
      flagOf impl κ inp (s'.regs.extract 0 p.2) p.1 = true) →
    exec impl κ inp ops s (tr.drop k) = some (s', tr') ∧ s'.ok = s.ok ∧
      InvK w (compileFromX X P cs ops) s'.regs κ
  | [], cs, pre, k, s, s', tr', hI, _, he, _, _, _, _, _, _, _ => by
    simp [execA] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨rfl, rfl, hI⟩
  | op :: ops, cs, pre, k, s, s', tr', hI, hpv, he, hr, ht, hx, hi, hrr, hra, hf => by
    rw [impAX_cons] at hi
    rw [repRowsX_cons] at hrr
    rw [askRowsX_cons] at hra
    rw [compileFromX_cons] at hr ht hx hi hf ⊢
    have hI' : InvK w (cs.align (alignOf op ops)) s.regs κ :=
      ⟨⟨by simp [hI.1.1], fun i => by rw [CS.align_slot]; exact hI.1.2 i⟩,
        fun p hp => by rw [CS.align_kslots] at hp; rw [CS.align_slots]; exact hI.2.1 p hp,
        fun i => by rw [CS.align_slotK]; exact hI.2.2 i⟩
    generalize cs.align (alignOf op ops) = cs at hI' hr ht hx hi hrr hra hf ⊢
    clear hI
    rename' hI' => hI
    set o := stepOut X P cs op with ho
    obtain ⟨ss, rs, hsl, hrw, -, hfor, htin, haux⟩ := compileFromX_mono X P ops (cs.add op o)
    have hro : ∀ r ∈ o.rows, r.Holds w := fun r h =>
      hr r (by
        rw [hrw]; simp only [CS.add, List.reverseAux_eq]
        exact List.mem_append_right _ (List.mem_append_left _ (List.mem_reverse.2 h)))
    have hto : ∀ t ∈ o.tin, ∀ r ∈ Tpl.instRows tc P.one (t.1, cs.tcount t.1, t.2), r.Holds w :=
      fun t htm r hr' => ht _ (htin (by simp only [CS.add, Option.mem_def.1 htm]; simp)) r hr'
    have hpre : ∀ (m : Array Val), (s.regs ++ m).extract 0 cs.slots.size = s.regs := fun m => by
      rw [hI.1.1, Array.extract_append_left, Array.extract_size]
    have flag : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) → o.foreign = true →
        flagOf impl κ inp s.regs op = true := by
      intro vs s1 hs1 ⟨m, hm⟩ hfo
      have := hf (op, cs.slots.size) (hfor (by simp [CS.add, hfo]))
      rwa [hm, hs1, Array.append_assoc, hpre] at this
    have hauxo : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) →
        ∀ a ∈ o.aux, a.1.map (Lin.ev w) = a.2.2.val (rd s.regs a.2.1) := by
      intro vs s1 hs1 ⟨m, hm⟩ a ha
      have := hx (a, cs.slots.size) (haux (by simp [CS.add, ha]))
      rwa [hm, hs1, Array.append_assoc, hpre] at this
    have hstep : (∀ q, evalOp impl κ inp s.regs op ≠ .ask q) ∨ X P cs op = none := by
      rcases hXo : X P cs op with _ | o'
      · exact .inr rfl
      · exact .inl ((hX P cs op o' hXo).2.2 inp w s.regs hP hI.1.2 hI.2.2).1
    have hpos : o.kin.isSome → 0 < o.slots.length := by
      rcases hXo : X P cs op with _ | o'
      · simp [ho, stepOut, hXo, opOut_kin]
      · simp only [ho, stepOut, hXo, Option.getD_some]; exact (hX P cs op o' hXo).2.1
    have hlen : o.slots.length = op.nOut := by
      rcases hXo : X P cs op with _ | o'
      · simp only [ho, stepOut, hXo, Option.getD_none]; exact opOut_len P cs op
      · simp only [ho, stepOut, hXo, Option.getD_some]; exact (hX P cs op o' hXo).1
    have hrr' : ∀ r ∈ repRowsX X P rt (cs.add op o) ops, r.Holds w' :=
      fun r h => hrr r (List.mem_append_right _ h)
    have hi' : ∀ i ∈ impAX X P rt A (cs.add op o) ops,
        RepS w ((compileFromX X P (cs.add op o) ops).slot i) (rd s'.regs i) :=
      fun i h => hi i (List.mem_append_right _ h)
    simp only [execA] at he
    split at he
    · rename_i vs ok hev
      have hit := vals_item' hev
      rw [hit, Bool.false_or] at hra
      have hra' : ∀ r ∈ askRowsX X P A (cs.add op o) (some op) k ops, r.Holds w :=
        fun r h => hra r (List.mem_append_right _ h)
      have hl := hlen.trans (evalOp_len hev).symm
      have hm := execA_prefix ops _ _ he
      -- an uncovered non-ask import's registers: from `hi`
      have fin : o.imp = true → rt.cov op = false → A.cov op = false →
          ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
        intro hio hc hac j hj
        obtain ⟨m, hm'⟩ := hm
        have := hi (cs.slots.size + j) (List.mem_append_left _ (by
          simp only [hio, hc, hac, hit, Bool.not_false, Bool.and_self, if_true, List.mem_range'_1]; omega))
        have hs := slot_append_right cs.slots o.slots ss hj
        have hv := rd_append_right s.regs vs m (by omega : j < vs.length)
        rw [CS.slot, hsl] at this; simp only [CS.add] at this
        rw [hs, hm', hI.1.1, hv] at this; exact this
      have hsnd : (o.imp = false → List.Forall₂ (RepS w) o.slots vs) ∧ (o.foreign = false → ok = true) ∧
          (∀ f v, o.kin = some f → vs.head? = some v → RepS w (f κ) v) := by
        rcases hXo : X P cs op with _ | o'
        · simp only [ho, stepOut, hXo, Option.getD_none] at hro ⊢
          exact ⟨(opOut_sound hP hI.1.2 op hro hev).1, (opOut_sound hP hI.1.2 op hro hev).2,
            fun f v hf => by rw [opOut_kin] at hf; cases hf⟩
        · have eo : o = o' := by simp [ho, stepOut, hXo]
          rw [eo] at hro hto ⊢
          exact ((hX P cs op o' hXo).2.2 inp w s.regs hP hI.1.2 hI.2.2).2 hro hto
            (eo ▸ hauxo vs _ rfl hm) vs ok hev
      have hnew : ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
        cases hio : o.imp
        · exact fun j hj => (List.forall₂_iff_get.1 (hsnd.1 hio)).2 j hj _
        · cases hc : rt.cov op
          · cases hac : A.cov op
            · exact fin hio hc hac
            · have hctx : AskCtx impl A κ inp w P cs pre op k s.regs :=
                ⟨hP, hI, hpv, fun r h => hra r (List.mem_append_left _ (by rw [if_pos hac]; exact h))⟩
              exact fun j hj => (List.forall₂_iff_get.1
                (hA.2 P cs pre op k s.regs vs ok hac hctx hev hio)).2 j hj _
          · have hrows : ∀ r ∈ rt.rows P cs op o.slots, r.Holds w' :=
              fun r h => hrr r (List.mem_append_left _ (by rw [if_pos hc]; exact h))
            exact fun j hj => (List.forall₂_iff_get.1
              ((hR P cs op hc).2 inp w w' s.regs vs ok hP hP' hI hAg hrows hev hio)).2 j hj _
      have hok : ok = true := by
        cases hfo : o.foreign
        · exact hsnd.2.1 hfo
        · have := flag vs _ rfl hm hfo; simpa [flagOf, hev] using this
      have ih := compileFromX_run hX hP hP' hAg hR hA ops _ (some op) k _ s' tr'
        (invK_add hI o op hl hnew hsnd.2.2 hpos) ⟨s.regs, .inl ⟨vs, ok, hev, rfl⟩⟩ he hr ht hx hi' hrr'
        hra' hf
      refine ⟨?_, by rw [ih.2.1, hok, Bool.and_true], ih.2.2⟩
      simp only [exec, hev]; exact ih.1
    · rename_i q hev
      have hit := ask_item hev
      rw [hit, Bool.true_or] at hra
      simp only [if_true] at hra
      have hXn : X P cs op = none := hstep.resolve_left fun h => h q hev
      have ho' : o = opOut P cs op := by simp [ho, stepOut, hXn]
      rcases hd : tr.drop k with _ | ⟨⟨q', a⟩, tr0⟩
      · rw [hd] at he; cases he
      rw [hd] at he
      obtain ⟨hk, rfl⟩ := drop_cons_get hd
      have hc : AskCtx impl A κ inp w P cs pre op k s.regs :=
        ⟨hP, hI, hpv, fun r h => hra r (List.mem_append_left _ h)⟩
      obtain ⟨hq, hans⟩ := hA.1 P cs pre op k s.regs q (q', a) hc hev hk
      have hl : o.slots.length = [Val.d a].length := by rw [hlen, ask_nOut hev]; rfl
      have hnew : ∀ j (hj : j < o.slots.length), RepS w o.slots[j] ([Val.d a][j]'(hl ▸ hj)) :=
        fun j hj => (List.forall₂_iff_get.1 hans).2 j hj _
      have ih := compileFromX_run hX hP hP' hAg hR hA ops _ (some op) (k + 1) ⟨s.regs.push (.d a), s.ok⟩ s' tr'
        (invK_add hI o op hl hnew (fun f v hf => by rw [ho', opOut_kin] at hf; cases hf) hpos)
        ⟨s.regs, .inr ⟨q, a, hev, rfl⟩⟩ he hr ht hx hi' hrr' (fun r h => hra r (List.mem_append_right _ h)) hf
      refine ⟨?_, ih.2.1, ih.2.2⟩
      simp only [exec, hev]
      simp only at hq
      rw [if_pos hq]; exact ih.1

/-- **The run of a compiled program exists** (`compileX_soundR`'s twin): the answer-driven run on
`tr`, with the rows, templates, replay and ask rows and the residual facts at its final state, is
`exec`'s run; its flag is set and every register is represented. -/
theorem compileX_run {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w w' : Asg} {B : ℕ} {P : Params} {tc : Tpl.TCtx} {X : Ext} {rt : RT} {A : AT}
    (hX : ExtOkK impl tc X κ) (hR : RTOkW impl X rt κ B) (hA : ATOk impl X A κ inp w tr) (base : ℕ)
    (hP : SelOk w P κ) (hP' : SelOk w' P κ) (hAg : Agree B w w')
    (he : execA impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileX X P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileX X P base ops).tplRows tc P.one, r.Holds w)
    (hx : ∀ a ∈ (compileX X P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ impAX X P rt A (CS.init base) ops, RepS w ((compileX X P base ops).slot i) (rd s.regs i))
    (hrr : ∀ r ∈ repRowsX X P rt (CS.init base) ops, r.Holds w')
    (hra : ∀ r ∈ askRowsX X P A (CS.init base) none 0 ops, r.Holds w)
    (hf : ∀ p ∈ (compileX X P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    exec impl κ inp ops St.init tr = some (s, tr') ∧ s.ok = true ∧
      ∀ i, RepS w ((compileX X P base ops).slot i) (rd s.regs i) := by
  have h := compileFromX_run hX hP hP' hAg hR hA ops (CS.init base) none 0 St.init s tr'
    ⟨⟨rfl, fun i => by simp [CS.slot, CS.init, RepS]⟩, fun p hp => by simp [CS.init] at hp,
      fun i => by simp [CS.slotK, CS.slot, CS.init, RepS]⟩ trivial (by simpa using he) hr
    (fun t htm r hr' => ht r (List.mem_flatMap.2 ⟨t, htm, hr'⟩)) hx hi hrr hra hf
  exact ⟨by simpa using h.1, h.2.1, h.2.2.1.2⟩

end Circ
end FR

end G6_FRNodeRun4
