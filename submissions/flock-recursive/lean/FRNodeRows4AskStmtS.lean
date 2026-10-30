-- G6: this module also holds the former modules `FRSoundness4RsvHM`, `FRSoundness4XRun`, `FRSoundness4XRunG`, `FRNodeSound4K`, `FRNodeRows4PackSound`, `FRNodeRows4AggChkG` (one section each, in import order).
import FRVerifierImplNode4F
import FRSoundness4R4FrE
import FRSoundness4R4W0R
import FRSoundness4R4Qv
import FRSoundness4R4PfFin
import FRSoundness4R4Stmt
import FRSoundness4XLaws
import FRNodeStmtR4
import FRNodeRun4
import FRNodeRows4ArenaPlace
import FRNodeRows4Agg
import FRNodeRows4Ext

section G6_FRSoundness4RsvHM

-- New for `flock-recursive` (revision 4.4.2, the reserve; track RSV-S2a): the node implementation's
-- stacked `evalM` in the form `FRSoundness4R4FrE.e_fin4` takes (`hM`).

/-!
# `hM` for `implN4F` (RSV2 §2.2)

`NI4F.implN4F_hMX` gives the stacked call at a 32-entry row point as `Σ_κ ⟨s_κ, M̃_κ⟩` with
`dot3`/`sOf`; **`implN4F_hMS`** restates it as `P4b.mStack` of the point's entries (`s` the entries
`23 …`, the row point the entries `0 …`, the column point `σ`), the form of `e_fin4`'s `hM`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

theorem implN4F_hMS (base : NodeKind → OpImpl) (ν : NodeKind) :
    ∀ τ σ : Array F, τ.size = 32 → (NI4F.implN4F base ν).evalM τ σ =
      (P4b.mStack NI4F.srcE4 (fun i => τ.getD (23 + i) 0) (fun j => τ.getD j 0) (fun j => σ.getD j 0), 0, 0) :=
  fun τ σ h => by
    rw [NI4F.implN4F_hMX base ν τ σ h]
    simp only [P4b.mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      NI4F.dot3, NI4F.sOf, NodeKind.ix]
    rfl

end FR.Snd.R4

end G6_FRSoundness4RsvHM

section G6_FRSoundness4XRun

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9, A.10, B-12; track R4i): X4's residual 2
-- (`RunFacts4`) from the program layer, at the concrete ops.

/-!
# X4's `RunFacts4` from the program layer

At the concrete ops (`implSeg (implC fin lRows κs₀)` for the segments,
`implN4F (fun _ => implC fin lRows κs₀)` for the nodes):

* **`acceptRun4_seg`**, **`acceptRun4_node`**: an accepted run of a kind's program, on a log
  without bad events, has a chain `j` that is an `AcceptTail` of the composed front
  (`RejFX`, `W0X`, `c0X`), whose entries are the run's. `¬ RejFX` from P4a's and P4b's `not_rej*`;
  `FinRest4` from `finRest4_full` with `hW` discharged (`wV4_of_fields`).
* **The statement views**: `segLog4` (`SegLog` from `segView` and the run, for `n ≤ cap`),
  `vkOf_node4` (the node's `stmtOps4` assert `piDigest 0 16 = input 0`, i.e. `X.vkOf π = vk`;
  X4's F4), `nodeLog4` (`NodeLog` from the run and `stmtOk4`).
* **`runFacts4_node`**: `RunFacts4.node`, unconditionally. **`runFacts4S`**: `RunFacts4.seg` for
  the segment proofs `V_A` runs (`π.size = piSizeOf seq4`, `n ≤ cap`): the two values
  `RunFacts4.seg` asks without them are asserted by no op of the segment program (finding F1).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset X4

/-! ## The concrete ops' parameters -/

section Ops
variable (fin : Finals) (lRows : List Circ.Row) (κs₀ : F)

theorem tensorW_segC : ∀ j r, (implSeg (Impl.implC fin lRows κs₀)).tensorW j r = Impl.tensorWS j r :=
  fun j r => by
    rw [(implSegC_meets fin lRows κs₀).2.2.2.1 j r]
    simp only [specSeg, Impl.specC, Impl.specCWith]

theorem rsWeight_segC (σ : SegKind) : ∀ r ps k β ρ, r.size = 7 → 23 ≤ ρ.size →
    (implSeg (Impl.implC fin lRows κs₀)).rsWeight r ps k β ρ = rsSpec4 (.seg σ) r ps k β ρ :=
  fun r ps k β ρ hr hρ => by
    rw [(implSegC_meets fin lRows κs₀).2.2.2.2.1 r ps k β ρ hr hρ]
    simp only [specSeg, Impl.specC, Impl.specCWith, rsSpec4]

/-- The node ops meet their specification (INT-9's `implN4F_meets` at 3.x's base). -/
theorem implNodeC_meets (ν : NodeKind) :
    (NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν).Meets
      (NI4F.specN4F (fun _ => Impl.specC fin lRows κs₀) ν) :=
  NI4F.implN4F_meets ν (Impl.implC_meets fin lRows κs₀)

theorem tensorW_nodeC (ν : NodeKind) :
    ∀ j r, (NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν).tensorW j r = Impl.tensorWS j r :=
  fun j r => by
    rw [(implNodeC_meets fin lRows κs₀ ν).2.2.2.1 j r]
    simp only [NI4F.specN4F, NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]

theorem rsWeight_nodeC (ν : NodeKind) : ∀ r ps k β ρ, r.size = 7 → 23 ≤ ρ.size →
    (NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν).rsWeight r ps k β ρ = rsSpec4 (.node ν) r ps k β ρ :=
  fun r ps k β ρ hr hρ => by
    rw [(implNodeC_meets fin lRows κs₀ ν).2.2.2.2.1 r ps k β ρ hr hρ]
    simp only [NI4F.specN4F, NI4.specN4, Impl.withRS4S, rsSpec4]

/-- (+) **INT-9's node ops (`implN4F` over 3.x's `implC`) meet every op parameter of R4e's node
statements** (`nodeC_params` at `implN4F`, through `implNodeC_meets`). -/
theorem nodeF_params (ν : NodeKind) :
    let impl := NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν
    (∀ a b, impl.eqZ a b = Impl.eqZS a b) ∧
      (∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe) ∧
      (∀ r, impl.targetS (KindP.ofNode ν).tix r = NT4.targetSNode4S ν r) ∧
      (∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = Impl.shiftTargetS k a b c) ∧
      (∀ a b, impl.shiftMask a b = NT4.shiftMask4S ν a b) ∧ (∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b) ∧
      (∀ tt rr, impl.linkWAll (KindP.ofNode ν).tix tt rr = NT4.linkWAll4S ν tt rr) ∧
      (∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
        impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw)) ∧
      ∀ l a, impl.rowW l a = Impl.rowWS l a := by
  intro impl
  obtain ⟨h1, h2, h3, -, -, -, h7, -, -, -, h11, h12, -, h14, h15, h16, -⟩ := implNodeC_meets fin lRows κs₀ ν
  have hn : (KindP.ofNode ν).tix.isNode = true := rfl
  refine ⟨fun a b => ?_, fun v l pe hv => ?_, fun r => ?_, fun k a b c hc => ?_, fun a b => ?_,
    fun κ s a b => ?_, fun tt rr => ?_, fun rw cw h1' h2' => ?_, fun l a => ?_⟩
  · rw [h3]; simp only [NI4F.specN4F, NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]
  · rw [h1 v l pe hv]; simp only [NI4F.specN4F, NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]
  · rw [h2]; simp only [NI4F.specN4F, NI4.specN4, hn, if_true]
  · rw [h11 k a b c hc]; simp only [NI4F.specN4F, NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]
  · rw [h15]; simp only [NI4F.specN4F, NI4.specN4]
  · rw [h12]; simp only [NI4F.specN4F, NI4.specN4]
  · rw [h14]; simp only [NI4F.specN4F, NI4.specN4, hn, if_true]
  · rw [h7 rw cw h1' h2']; simp only [NI4F.specN4F, NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]
  · rw [h16]; simp only [NI4F.specN4F, NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]

end Ops

/-! ## The composed front's checks on an accepted run -/

theorem not_rejFX_seg (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) {σ : SegKind} {inp : Input}
    {tr : Trace}
    (h : semIR (implSeg (Impl.implC fin lRows κs₀)) (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr =
      some true) (L : Log) : ¬ RejFX L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨hZ, hLS, hTS, hST, hSM, hSW, hLW, hW, hR⟩ := segC_params fin lRows κs₀ σ
  rintro (h4a | h1 | h2 | h3 | h4 | h5)
  · exact not_rejF4a_seg4 hLS hTS hW hR hZ hST N4c.indN4 N4c.etN4 h L h4a
  · exact not_rejEndLr4_seg h L h1
  · exact not_rejEndE4_seg h L h2
  · exact not_rejInE4_seg h L h3
  · exact not_rejFinE4_seg NI4F.srcE4 NI4F.srcL4 h L h4
  · exact not_rejRS4_seg hZ hLS hST hSM hSW hLW P4a.wNS4 h L h5

theorem not_rejFX_node (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) {ν : NodeKind} {cells : List ℕ}
    {inp : Input} {tr : Trace}
    (h : semIR (NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν)
      (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ RejFX L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨hZ, hLS, hTS, hST, hSM, hSW, hLW, hW, hR⟩ := nodeF_params fin lRows κs₀ ν
  rintro (h4a | h1 | h2 | h3 | h4 | h5)
  · exact not_rejF4a_node4 hLS hTS hW hR hZ hST h L h4a
  · exact not_rejEndLr4_node h L h1
  · exact not_rejEndE4_node h L h2
  · exact not_rejInE4_node h L h3
  · exact not_rejFinE4_node NI4F.srcE4 NI4F.srcL4 (implN4F_hMS _ ν) (NI4F.implN4F_hL _ ν) h L h4
  · exact not_rejRS4_node hZ hLS hST hSM hSW hLW h L h5

/-! ## `AcceptTail` from an accepted run, with the run's entries -/

/-- B′'s cells (`X4.cellsX`: the nine public cells and the reserve's) lie inside level 0. -/
theorem hcellsX (ν : NodeKind) : ∀ c ∈ X4.cellsX ν, c < 2 ^ P4b.ncR ν := fun c hc => by
  rcases List.mem_append.1 hc with h | h
  · exact (N4c.hcells4P4b ν).2 c h
  · exact (N4c.rsvCells_ctl.2.2.2.1 ν c h).2.2

/-- **An accepted segment run's chain is an `AcceptTail` of the composed front**, and its entries
are the run's. -/
theorem acceptRun4_seg (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (σ : SegKind) {inp : Input}
    {L : Log} (hb : ¬ Bad L) (hπ : inp.π.size = piSizeOf seq4)
    (hrun : (runIR (implSeg (Impl.implC fin lRows κs₀)) (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ)))
      inp).runLog L = some true) :
    ∃ tr y j, SkRun4 (implSeg (Impl.implC fin lRows κs₀)) (.ofSeg σ) inp tr y ∧
      semIR (implSeg (Impl.implC fin lRows κs₀)) (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr =
        some true ∧
      entriesOf L (pathOf L j) = fsOf tr (itemsOf seq4) ∧ T4.AcceptTail RejFX W0X c0X L j := by
  obtain ⟨tr, hsem, hin, j, hci, hes, hlen⟩ := runLog_chain4 _ _ _ hb hπ hrun
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) hsem
  have hk := kindOfC_acc_seg hsem
  have hT : FinTabs4 (segFinP σ) (KindP.ofSeg σ).tix (kindOfC (fsOf tr (itemsOf seq4))) := by
    rw [hk]; exact finTabs4_seg σ _
  have hW := wV4_of_fields hF hk (finTabs4_seg σ _) (ptIx_seg4 σ _ _) (cells := X4.cellsX)
    hcellsX rfl rfl rfl (show seq4.mStar - 7 = 25 by rw [seq4_mStar]) (rsWeight_segC fin lRows κs₀ σ)
    (tensorW_segC fin lRows κs₀) hb hin (dm_seg4 hF.sk)
  have hFR := finRest4_full (phiRS_segC fin lRows κs₀) (tensorW_segC fin lRows κs₀) hF hT (dm_seg4 hF.sk)
    hb hin hπ hW
  obtain ⟨hrnd, hrndPf⟩ := rounds_of_run4 hF.sk
  refine ⟨tr, y, j, hF.sk, hsem, hes, acceptTail4_of_finLog (y := yv4 (KindP.ofSeg σ) (#[] ++ y.1.toArray)) hb hci hlen
    (hes ▸ not_rejFX_seg fin lRows κs₀ hsem L) ?_⟩
  rw [hes]
  exact ⟨hrnd, hrndPf, hFR.start, hFR.cols, hFR.link, hFR.pf0, hFR.enc, hFR.fin, hFR.cap⟩

/-- **… and an accepted node run's** (at `cells4`). -/
theorem acceptRun4_node (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (ν : NodeKind) {inp : Input}
    {L : Log} (hb : ¬ Bad L) (hπ : inp.π.size = piSizeOf seq4)
    (hrun : (runIR (NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν)
      (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν (N4c.cells4 ν)))) inp).runLog L = some true) :
    ∃ tr y j, SkRun4 (NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν) (.ofNode ν) inp tr y ∧
      semIR (NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν)
        (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν (N4c.cells4 ν)))) inp tr = some true ∧
      entriesOf L (pathOf L j) = fsOf tr (itemsOf seq4) ∧ T4.AcceptTail RejFX W0X c0X L j := by
  obtain ⟨tr, hsem, hin, j, hci, hes, hlen⟩ := runLog_chain4 _ _ _ hb hπ hrun
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν (N4c.cells4 ν)) hsem
  have hk := kindOfC_acc_node hsem
  have hT : FinTabs4 (nodeFinP ν (N4c.cells4 ν)) (KindP.ofNode ν).tix (kindOfC (fsOf tr (itemsOf seq4))) := by
    rw [hk]; exact finTabs4_node ν _ _
  have hW := wV4_of_fields hF hk (finTabs4_node ν _ _) (ptIx_node4 ν _ _ _) (cells := X4.cellsX)
    hcellsX rfl rfl (by cases ν <;> rfl) (show seq4.mStar - 7 = 25 by rw [seq4_mStar])
    (rsWeight_nodeC fin lRows κs₀ ν)
    (tensorW_nodeC fin lRows κs₀ ν) hb hin (dm_node4 hF.sk)
  have hFR := finRest4_full (phiRS_nodeF fin lRows κs₀ ν) (tensorW_nodeC fin lRows κs₀ ν) hF hT
    (dm_node4 hF.sk) hb hin hπ hW
  obtain ⟨hrnd, hrndPf⟩ := rounds_of_run4 hF.sk
  refine ⟨tr, y, j, hF.sk, hsem, hes, acceptTail4_of_finLog (y := yv4 (KindP.ofNode ν) (#[] ++ y.1.toArray)) hb hci hlen
    (hes ▸ not_rejFX_node fin lRows κs₀ hsem L) ?_⟩
  rw [hes]
  exact ⟨hrnd, hrndPf, hFR.start, hFR.cols, hFR.link, hFR.pf0, hFR.enc, hFR.fin, hFR.cap⟩

/-! ## The statement views -/

section Views
variable {impl : OpImpl} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

/-- **A node's `stmt` checks carry its key** (X4's F4; 3.x's `vkOf_of_run`): `stmtOps4`'s node
branch asserts `piDigest 0 16 = input 0`, so `hdr.pub` (π's digest at 16) is the input's `vk`. -/
theorem vkOf_node4 {ν : NodeKind} (h : SkRun4 impl (.ofNode ν) inp tr y) : X.vkOf inp.π = inp.vk := by
  obtain ⟨trk, M, x, hx, -, -, -, hfl, -, -⟩ := phase_at4 impl _ inp _ h.ref (k := 1) (by decide)
  have hflag := h.flags _ hfl
  have hph : (phasesOf seq4)[1] = ("stmt", .absorb fStmt 128) := rfl
  have hnode : (KindP.ofNode ν).d.node = true := by cases ν <;> rfl
  rw [hph] at hx
  simp only [refPhase4] at hx
  obtain ⟨⟨a, trk'⟩, -, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp only [absTail4, ite_true, hnode] at hz
  generalize fieldOffOf seq4 fStmt + phaseOffOf seq4 1 fStmt = o at hz
  generalize (#[] ++ M.toArray) = R at hz
  simp only [stmtOps4, hnode, ite_true, List.cons_append, List.nil_append, pureRun, evalOp, rd_app,
    Nat.add_assoc, List.getD_cons_succ, List.getD_cons_zero, Option.map_some] at hz
  rw [← (Option.some.inj hz)] at hflag
  simp only [allK, Bool.not_true, Bool.false_or, Bool.true_and, Bool.and_true, Bool.and_eq_true, Val.eqv,
    decide_eq_true_eq] at hflag
  rw [X.vkOf, ← digestAt_eq, ← hflag.2.2.2, absOff_zero]

/-- **A node's statement on the log** (`NodeLog`) from its run and the statement fact `stmtOk4`. -/
theorem nodeLog4 {ν : NodeKind} {vk c : Digest} {π : Proof} {P : FinP}
    (h : SkRun4 impl (.ofNode ν) ⟨vk, c, π⟩ tr y)
    (hsem : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 P)) ⟨vk, c, π⟩ tr = some true)
    (hst : stmtOk4 seq4 (.ofNode ν) ⟨vk, c, π⟩ = true) : NodeLog ν vk c π (fsOf tr (itemsOf seq4)) := by
  have hk : kindOfC (fsOf tr (itemsOf seq4)) = .node ν := kindOfC_acc_node hsem
  have hvk : X.vkOf π = vk := vkOf_node4 (inp := ⟨vk, c, π⟩) h
  have hvkL : vkL (fsOf tr (itemsOf seq4)) = vk := vkL_eq4 (inp := ⟨vk, c, π⟩) h
  refine ⟨hk, hvk, hvkL, ?_⟩
  obtain ⟨h0, h1⟩ := stL_eq4 (inp := ⟨vk, c, π⟩) h
  simp only [stmtOk4, decide_eq_true_eq, KindP.ofNode, stmtDigest, stmtBytes4, stmtOff4] at hst
  rw [h0, h1, fieldOff_hdr_stmt4.2, ← hst, nodeStmtF_eq, bytesAt_extract_of_le π (by norm_num),
    bytesAt_extract_of_le π (by norm_num)]

/-- **A segment's statement on the log** (`SegLog`) from its run, on a view `V_A` accepts
(`n ≤ cap`: the program's 24-bit `n` is `segView`'s, `segView_lastN`). -/
theorem segLog4 {σ : SegKind} {P : FinP} {v : SegView} (h : SkRun4 impl (.ofSeg σ) inp tr y)
    (hsem : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true)
    (hv : segView inp.π = some v) (hσ : v.kind = σ) (hcap : v.n ≤ v.kind.cap) :
    SegLog v (fsOf tr (itemsOf seq4)) := by
  have hn := segView_lastN hv hcap
  simp only [segView, Option.map_eq_some_iff] at hv
  obtain ⟨κ, -, rfl⟩ := hv
  refine ⟨by rw [kindOfC_acc_seg hsem, ← hσ], seed_bytesAt4 h (o := 16) (n := 32) (by norm_num), ?_, ?_⟩
  · rw [stmt_msg4 h, bytesAt_extract_of_le inp.π (by norm_num)]
  · rw [nStmt_eq4 h, ← hn, stmtOff4]

end Views

/-! ## `RunFacts4` -/

/-- **`RunFacts4.seg` on the segment proofs `V_A` runs**: `π` of `piSizeOf seq4` bytes
(`piSize_aggSegs`) and `n ≤ cap` (`aggChecks`). Since INT-10 this is literally `RunFacts4.seg`
(`runFacts4S_seg`). -/
def RunFacts4S (Vseg : SegProgs) (vk : Digest) : Prop :=
  ∀ L π v, ¬ Bad L → segView π = some v → π.size = piSizeOf seq4 → v.n ≤ v.kind.cap →
    (Vseg v.kind vk (segC v) π).runLog L = some true →
    ∃ j, T4.AcceptTail RejFX W0X c0X L j ∧ SegLog v (entriesOf L (pathOf L j))

/-- **The segment proofs `V_A` never runs** (another size, or `n > cap`). The segment program
asserts neither value (finding F1). Before INT-10 this was the rest of `RunFacts4.seg`; since INT-10's
amendment `RunFacts4.seg` no longer asks for it, and no theorem of the certificate needs it (it stays a
hypothesis of the kept `ks_rev4G`/`certificate_rev4G`, unused). -/
def SegOut4 (Vseg : SegProgs) (vk : Digest) : Prop :=
  ∀ L π v, ¬ Bad L → segView π = some v → (π.size ≠ piSizeOf seq4 ∨ v.kind.cap < v.n) →
    (Vseg v.kind vk (segC v) π).runLog L = some true →
    ∃ j, T4.AcceptTail RejFX W0X c0X L j ∧ SegLog v (entriesOf L (pathOf L j))

/-- **The verifier's run, then the statement fact** (`runStmt`'s acceptance). -/
theorem runStmt_acc {impl : OpImpl} {Pg : VProg} {p : KindP} {inp : Input} {L : Log}
    (h : (runStmt impl Pg p inp).runLog L = some true) :
    (runIR impl Pg inp).runLog L = some true ∧ stmtOk4 seq4 p inp = true := by
  rw [runStmt, runLog_bind_ret] at h
  obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.1 h
  rw [Bool.and_eq_true] at he
  exact ⟨by rw [hb, he.1], he.2⟩

section C
variable (fin : Finals) (lRows : List Circ.Row) (κs₀ : F)

/-- **`RunFacts4.seg` at the concrete segment ops**, on `V_A`'s segment proofs. -/
theorem runFacts4S_C (vk : Digest) : RunFacts4S (VsegC (Impl.implC fin lRows κs₀)) vk := by
  intro L π v hb hv hπ hcap hrun
  obtain ⟨hrun', -⟩ := runStmt_acc hrun
  obtain ⟨tr, y, j, hS, hsem, hes, hT⟩ := acceptRun4_seg fin lRows κs₀ v.kind (inp := ⟨vk, segC v, π⟩) hb hπ hrun'
  exact ⟨j, hT, hes ▸ segLog4 hS hsem hv rfl hcap⟩

/-- **`RunFacts4.node` at the concrete node ops** (INT-9's `implN4F`, `cells4`; the zero outputs from
`finE`'s asserts, RSV-S2a's `rsvZero4`). -/
theorem runFacts4_node_C (vk : Digest) :
    ∀ κ L c π, ¬ Bad L → kindOf4 π = .node κ →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ j, T4.AcceptTail RejFX W0X c0X L j ∧ NodeLog κ vk c π (entriesOf L (pathOf L j)) ∧
        RsvZero (entriesOf L (pathOf L j)) := by
  intro κ L c π hb hk hrun
  obtain ⟨hrun', hst⟩ := runStmt_acc hrun
  obtain ⟨tr, y, j, hS, hsem, hes, hT⟩ :=
    acceptRun4_node fin lRows κs₀ κ (inp := ⟨vk, c, π⟩) hb (piSize_node4 hk) hrun'
  exact ⟨j, hT, hes ▸ nodeLog4 hS hsem hst, hes ▸ rsvZero4 hsem⟩

/-- **X4's `RunFacts4` at the concrete ops** (INT-10: unconditional; `RunFacts4.seg` is
`RunFacts4S`). -/
theorem runFacts4H_C (vk : Digest) :
    RunFacts4 (VsegC (Impl.implC fin lRows κs₀)) (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀)
      N4c.cells4) vk :=
  ⟨runFacts4S_C fin lRows κs₀ vk, runFacts4_node_C fin lRows κs₀ vk⟩

/-- R4i's form, kept for its users: `SegOut4` is no longer needed (`runFacts4H_C`). -/
theorem runFacts4_C (vk : Digest)
    (_hO : SegOut4 (VsegC (Impl.implC fin lRows κs₀)) vk) :
    RunFacts4 (VsegC (Impl.implC fin lRows κs₀)) (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀)
      N4c.cells4) vk :=
  runFacts4H_C fin lRows κs₀ vk

end C

/-- **The amended `RunFacts4.seg` is `RunFacts4S`** (INT-10), for any programs. -/
theorem runFacts4S_seg (Vseg : SegProgs) (Vnode : NodeProgs) (vk : Digest) (h : RunFacts4 Vseg Vnode vk) :
    RunFacts4S Vseg vk := h.seg

end FR.Snd.R4

end G6_FRSoundness4XRun

section G6_FRSoundness4XRunG

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; track R4i): P4f's `ks_rev4F` and
-- `certificate_rev4F` with X4's residual 2 (`RunFacts4`) discharged but for `SegOut4`. INT-10:
-- `ks_rev4H`/`certificate_rev4H`, with residual 2 discharged in full (no `SegOut4`).

/-!
# Revision 4.1's knowledge soundness without `RunFacts4`

**`ks_rev4G`**, **`certificate_rev4G`**: P4f's `ks_rev4F`/`certificate_rev4F` at the concrete ops
(`impl₀ = implC fin lRows κs₀`, `base = fun _ => implC fin lRows κs₀`; S-I's `implB` is `implC` of the
node's finals, `Impl.implCN_eq`), with `hRun` replaced by **`SegOut4`**: `RunFacts4.seg` on the
segment proofs `V_A` never runs (another size than `piSizeOf seq4`, or `n > cap`). The segment
program asserts neither value, so no run fact gives them (finding F1); `segOut4_size_VA` shows `V_A`'s
segments are outside `SegOut4`'s size case.

**`ks_rev4H`**, **`Resid4H`**, **`certificate_rev4H`** (INT-10): the same with no `SegOut4`, after the
ruled amendment (`SegSoundLog` and `RunFacts4.seg` carry `π.size = piSizeOf seq4` and `n ≤ cap`, which
`V_A` checks before it runs any segment program). `ks_rev4G`/`certificate_rev4G` are kept with their
statements (users in other tracks) and now follow from the `H` forms; their `SegOut4` is unused.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 X4 FR.X.X4

section KS
variable (fin : Finals) (lRows : List Circ.Row) (κs₀ : F)

/-- **Revision 4.1's knowledge soundness** (INT-10; P4f's `ks_rev4F` with `hRun` from
`runFacts4H_C`). -/
theorem ks_rev4H (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, X4.GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV :=
  ks_rev4R _ _ S vk hV hq hE hε (runFacts4H_C fin lRows κs₀ vk) I rd hI (fun κ w c₁ c₂ _ hS => hRes κ w c₁ c₂ hS.1)
    D hL

/-- **`ks_rev4H` with the reserve** (revision 4.4.2): the residual `hRes` is over `StmtN4R`
(`ks_rev4R` with `hRun` from `runFacts4H_C`). -/
theorem ks_rev4HR (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, X4.GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV :=
  ks_rev4R _ _ S vk hV hq hE hε (runFacts4H_C fin lRows κs₀ vk) I rd hI hRes D hL

/-- R4i's form (`SegOut4` unused since INT-10), kept for its users. -/
theorem ks_rev4G (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (_hO : SegOut4 (VsegC (Impl.implC fin lRows κs₀)) vk)
    (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, X4.GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV :=
  ks_rev4H fin lRows κs₀ S vk hV hq hE hε I rd hI hRes D hL

/-- **X4's `Resid4` without `run`**: `SegOut4`, the slot interface, the links. -/
structure Resid4G (S : Submission) (nd : X.XIR) (D : NodeDec4 nd) (vk : Digest) : Prop where
  out : SegOut4 (VsegC (Impl.implC fin lRows κs₀)) vk
  slots : ∃ (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4))
    (rd : N4c.Read4), (I.lrows = lRows4 ∧ I.irows = nodeIRows4) ∧
      ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
        N4c.NodeResid4 I rd κ vk c₁ c₂ w
  links : ∀ κ L c π, X4.GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)

/-- **X4's `Resid4` without `run`** (INT-10): the slot interface and the links. -/
structure Resid4H (S : Submission) (nd : X.XIR) (D : NodeDec4 nd) (vk : Digest) : Prop where
  slots : ∃ (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4))
    (rd : N4c.Read4), (I.lrows = lRows4 ∧ I.irows = nodeIRows4) ∧
      ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
        N4c.NodeResid4 I rd κ vk c₁ c₂ w
  links : ∀ κ L c π, X4.GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)

/-- **`Resid4H` with the reserve** (revision 4.4.2): the slot interface with `hRes` over `StmtN4R`,
and the links. -/
structure Resid4HR (S : Submission) (nd : X.XIR) (D : NodeDec4 nd) (vk : Digest) : Prop where
  slots : ∃ (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4))
    (rd : N4c.Read4), (I.lrows = lRows4 ∧ I.irows = nodeIRows4) ∧
      ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
        N4c.NodeResid4 I rd κ vk c₁ c₂ w
  links : ∀ κ L c π, X4.GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)

theorem resid4HR_of_H {S : Submission} {nd : X.XIR} {D : NodeDec4 nd} {vk : Digest}
    (h : Resid4H fin lRows κs₀ S nd D vk) : Resid4HR fin lRows κs₀ S nd D vk :=
  let ⟨I, rd, hI, hRes⟩ := h.slots
  ⟨⟨I, rd, hI, fun κ w c₁ c₂ _ hS => hRes κ w c₁ c₂ hS.1⟩, h.links⟩

theorem resid4R_of_HR {S : Submission} {nd : X.XIR} {D : NodeDec4 nd} {vk : Digest}
    (h : Resid4HR fin lRows κs₀ S nd D vk) :
    X4.Resid4R (Impl.implC fin lRows κs₀) (fun _ => Impl.implC fin lRows κs₀) S nd D vk :=
  ⟨runFacts4H_C fin lRows κs₀ vk, h.slots, h.links⟩

theorem resid4_of_H {S : Submission} {nd : X.XIR} {D : NodeDec4 nd} {vk : Digest}
    (h : Resid4H fin lRows κs₀ S nd D vk) :
    X4.Resid4 (Impl.implC fin lRows κs₀) (fun _ => Impl.implC fin lRows κs₀) S nd D P4f.DFhi vk :=
  ⟨runFacts4H_C fin lRows κs₀ vk, h.slots, h.links⟩

theorem resid4H_of_G {S : Submission} {nd : X.XIR} {D : NodeDec4 nd} {vk : Digest}
    (h : Resid4G fin lRows κs₀ S nd D vk) : Resid4H fin lRows κs₀ S nd D vk :=
  ⟨h.slots, h.links⟩

theorem resid4_of_G {S : Submission} {nd : X.XIR} {D : NodeDec4 nd} {vk : Digest}
    (h : Resid4G fin lRows κs₀ S nd D vk) :
    X4.Resid4 (Impl.implC fin lRows κs₀) (fun _ => Impl.implC fin lRows κs₀) S nd D P4f.DFhi vk :=
  resid4_of_H fin lRows κs₀ (resid4H_of_G fin lRows κs₀ h)

/-- **The contract's `Certificate`** (INT-10; P4f's `certificate_rev4F` with `Resid4`'s `run`
discharged in full). -/
theorem certificate_rev4H (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd)
    (hfuel : S.fuel = X.fuel) (hnd : DecOk4 nd) (D : NodeDec4 nd)
    (hR : ∀ vk, Resid4H fin lRows κs₀ S nd D vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S :=
  certificate_rev4R _ _ S hV hq hE hε hext hfuel hnd D
    (fun vk => resid4R_of_HR fin lRows κs₀ (resid4HR_of_H fin lRows κs₀ (hR vk))) hC hδ

/-- **The contract's `Certificate` with the reserve** (revision 4.4.2; `certificate_rev4H` with the
residual over `StmtN4R`, `certificate_rev4R`). -/
theorem certificate_rev4HR (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd)
    (hfuel : S.fuel = X.fuel) (hnd : DecOk4 nd) (D : NodeDec4 nd)
    (hR : ∀ vk, Resid4HR fin lRows κs₀ S nd D vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S :=
  certificate_rev4R _ _ S hV hq hE hε hext hfuel hnd D (fun vk => resid4R_of_HR fin lRows κs₀ (hR vk)) hC hδ

/-- R4i's form (`Resid4G.out` unused since INT-10), kept for its users. -/
theorem certificate_rev4G (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd)
    (hfuel : S.fuel = X.fuel) (hnd : DecOk4 nd) (D : NodeDec4 nd)
    (hR : ∀ vk, Resid4G fin lRows κs₀ S nd D vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S :=
  certificate_rev4H fin lRows κs₀ S hV hq hE hε hext hfuel hnd D
    (fun vk => resid4H_of_G fin lRows κs₀ (hR vk)) hC hδ

end KS

/-! ## Controls -/

/-- (−) **`V_A`'s segments are outside `SegOut4`'s size case**: on an aggregate `V_A` runs
(`π.size = 48 + k · piSizeOf seq4`), every segment has `piSizeOf seq4` bytes. -/
theorem segOut4_size_VA {k : ℕ} {π : Proof} (h : π.size = 48 + k * piSizeOf seq4) :
    ∀ s ∈ aggSegs (piSizeOf seq4) k π, ¬ s.size ≠ piSizeOf seq4 :=
  fun s hs hne => hne (piSize_aggSegs h s hs)

/-- (+/−) **`pfFamM`**: the kind's family `m` (`m*` for `L32`, its own for `L30`). -/
theorem pfFamM_ctl : pfFamM (segFinP .L32) .L32 = 32 ∧ pfFamM (segFinP .L30) .L32 = 30 ∧
    pfFamM (segFinP .L30) .L32 ≠ seq4.mStar := by
  refine ⟨pfFamM_eq (finTabs4_seg .L32 _), pfFamM_eq (finTabs4_seg .L30 _), ?_⟩
  rw [pfFamM_eq (finTabs4_seg .L30 _), seq4_mStar]; decide

/-- (+/−) **`tailList4`**: level 1's tail has `mLog L32 0 = 19` values at `m = 32`, 17 at `m = 30`. -/
theorem tailList4_len (es : Log) : (tailList4 es 32 1).length = 19 ∧
    (tailList4 es 30 1).length ≠ (tailList4 es 32 1).length := by
  simp [tailList4, hEll, lvlStar, lvl, ladder, ladder32, List.range'_succ]

/-- (+/−) **`rsSrc4`**: a node has E4's fourth claim point, a segment does not. -/
theorem rsSrc4_ctl (σ : SegKind) (ν : NodeKind) (fi : FinIn) :
    (rsSrc4 (.seg σ) fi).length = 3 ∧ (rsSrc4 (.node ν) fi).length = 4 := by
  simp [rsSrc4]

/-- (+) **`rsSpec4`** is the kind's `rsWeight` specification. -/
theorem rsSpec4_ctl (σ : SegKind) (ν : NodeKind) :
    rsSpec4 (.seg σ) = Impl.rsWeightS ∧ rsSpec4 (.node ν) = Impl.rsWeightS4 ν := ⟨rfl, rfl⟩

/-- (+/−) **`eqCellK4`** over 25 coordinates at a one-coordinate `ρ` (the 24 others padded): cell `1`
reads `ρ₀` (`1` at `ρ = [1]`, `0` at `ρ = [0]`). -/
theorem eqCellK4_ctl : eqCellK4 25 ([1] : List K).toArray 1 = 1 ∧ eqCellK4 25 ([0] : List K).toArray 1 = 0 := by
  constructor
  · rw [eqCellK4_eq (n := 1) [1] rfl (by norm_num) (by norm_num), eqCell, Fin.prod_univ_one]
    simp [FR.ptOf]
  · rw [eqCellK4_eq (n := 1) [0] rfl (by norm_num) (by norm_num), eqCell, Fin.prod_univ_one]
    simp [FR.ptOf]

end FR.Snd.R4

end G6_FRSoundness4XRunG

section G6_FRNodeSound4K

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; stage S-N2): P4f's `ks_rev4F` and
-- `certificate_rev4F` with residuals 3–4 (the slot interface, its reader, `hRes`) instantiated.

/-!
# `ks_rev4H`, `certificate_rev4H`: residuals 3–4 reduced to the circuit's gaps

**`ks_rev4H`** is P4f's `ks_rev4F` (revision 4.4.2: X4's `ks_rev4R`, the gaps over `StmtN4R`) with
* residual 3 discharged: the slot interface is `I4 impl₀ base hT₀ hT` (`FRNodeSound4`; its
  `soundN`/`soundS` proved from the compiler's soundness and INT-8's group-program bridge), at
  `lRows4`/`nodeIRows4` (`I4_rows`), and the reader is `rd4 pf` (`FRNodeRead4`);
* residual 4 reduced to **`hGap`**: on the node's truths, the items no row of the circuit binds
  (`Gap4`, `FRNodeSound4R`); every other `NodeResid4` item is proved (`resid4_of`).

Its new parameters: `hT₀`/`hT` (`ImplT` of the segment and node bases: the templates' ops, by
`implCWith_implT` at the submission's `implC`), and `pf` (the proof a `seq4` trace carries, S-H4's
reassembly; any `pf` will do for this theorem).

**`certificate_rev4H`** is `certificate_rev4F` with `Resid4` replaced by `Resid4H` (the run facts,
`hGap`, the links).

**`ks_rev4GH`/`certificate_rev4GH`** are the same on top of R4i's `ks_rev4G`/`certificate_rev4G`
(residual 2 closed at the 3.x base `Impl.implC fin lRows κs₀`; `ImplT` of that base is
`implCWith_implT`): their hypotheses are R4i's `SegOut4`, `hGap`, `D`, `hL`.
-/

namespace FR.Snd.P4f
open RecursionFast FR.Rev4 FR.N4s FR.X.X4 FR.Circ

/-- **`ks_rev4F` with residuals 3–4 instantiated**: the remaining hypotheses are `hRun` (2), `hGap`
(the circuit's gaps), `D` (5), `hL` (6), and the definitional ones. -/
theorem ks_rev4H (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (hRun : X4.RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk)
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (pf : Trace → Proof)
    (hGap : ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      Gap4 impl₀ base pf κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, X4.GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV :=
  X4.ks_rev4R impl₀ base S vk hV hq hE hε hRun (I4 impl₀ base hT₀ hT) (rd4 pf) (I4_rows impl₀ base hT₀ hT)
    (fun κ w c₁ c₂ ch hS => resid4_of hT₀ hT pf hS.1 (hGap κ w c₁ c₂ ch hS)) D hL

/-- **The residuals of `ks_rev4H` at one key**: the run facts (2), the circuit's gaps, the links (6). -/
structure Resid4H (impl₀ : OpImpl) (base : NodeKind → OpImpl) (pf : Trace → Proof) (S : Submission)
    (nd : X.XIR) (D : NodeDec4 nd) (vk : Digest) : Prop where
  run : X4.RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk
  gap : ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
    Gap4 impl₀ base pf κ vk c₁ c₂ w
  links : ∀ κ L c π, X4.GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)

/-- `Resid4H` gives X4's `Resid4R` (its `slots` field at `I4`, `rd4 pf`, `resid4_of`). -/
theorem resid4_of_H {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) {pf : Trace → Proof} {S : Submission} {nd : X.XIR} {D : NodeDec4 nd}
    {vk : Digest} (h : Resid4H impl₀ base pf S nd D vk) : X4.Resid4R impl₀ base S nd D vk :=
  ⟨h.run, ⟨I4 impl₀ base hT₀ hT, rd4 pf, I4_rows impl₀ base hT₀ hT,
    fun κ w c₁ c₂ ch hS => resid4_of hT₀ hT pf hS.1 (h.gap κ w c₁ c₂ ch hS)⟩, h.links⟩

/-- **`certificate_rev4F` with residuals 3–4 instantiated.** -/
theorem certificate_rev4H (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd) (hfuel : S.fuel = X.fuel)
    (hnd : DecOk4 nd) (D : NodeDec4 nd) (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν))
    (pf : Trace → Proof) (hR : ∀ vk, Resid4H impl₀ base pf S nd D vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S :=
  X4.certificate_rev4R impl₀ base S hV hq hE hε hext hfuel hnd D (fun vk => resid4_of_H hT₀ hT (hR vk)) hC hδ

/-! ## On top of R4i (`ks_rev4G`) -/

section G
variable (fin : Finals) (lRows : List Row) (κs₀ : F)

/-- **`ks_rev4G` with residuals 3–4 instantiated** (the concrete base `Impl.implC fin lRows κs₀`):
the remaining hypotheses are `hO` (R4i's `SegOut4`), `hGap`, `D`, `hL`. -/
theorem ks_rev4GH (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (hO : R4.SegOut4 (VsegC (Impl.implC fin lRows κs₀)) vk) (pf : Trace → Proof)
    (hGap : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      Gap4 (Impl.implC fin lRows κs₀) (fun _ => Impl.implC fin lRows κs₀) pf κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, X4.GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV :=
  R4.ks_rev4G fin lRows κs₀ S vk hV hq hE hε hO
    (I4 _ _ (Impl.implCWith_implT _ _) fun _ => Impl.implCWith_implT _ _) (rd4 pf)
    (I4_rows _ _ _ _) (fun κ w c₁ c₂ hS => resid4_of _ _ pf hS (hGap κ w c₁ c₂ hS)) D hL

/-- **R4i's `Resid4G` with the slots instantiated**: `SegOut4`, the circuit's gaps, the links. -/
structure Resid4GH (pf : Trace → Proof) (S : Submission) (nd : X.XIR) (D : NodeDec4 nd) (vk : Digest) :
    Prop where
  out : R4.SegOut4 (VsegC (Impl.implC fin lRows κs₀)) vk
  gap : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
    Gap4 (Impl.implC fin lRows κs₀) (fun _ => Impl.implC fin lRows κs₀) pf κ vk c₁ c₂ w
  links : ∀ κ L c π, X4.GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)

/-- **The contract's `Certificate`** from R4i's `certificate_rev4G` with the slots instantiated. -/
theorem certificate_rev4GH (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd)
    (hfuel : S.fuel = X.fuel) (hnd : DecOk4 nd) (D : NodeDec4 nd) (pf : Trace → Proof)
    (hR : ∀ vk, Resid4GH fin lRows κs₀ pf S nd D vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S :=
  R4.certificate_rev4G fin lRows κs₀ S hV hq hE hε hext hfuel hnd D (fun vk => ⟨(hR vk).out,
    ⟨I4 _ _ (Impl.implCWith_implT _ _) fun _ => Impl.implCWith_implT _ _, rd4 pf, I4_rows _ _ _ _,
      fun κ w c₁ c₂ hS => resid4_of _ _ pf hS ((hR vk).gap κ w c₁ c₂ hS)⟩, (hR vk).links⟩) hC hδ

end G

end FR.Snd.P4f

end G6_FRNodeSound4K

section G6_FRNodeRows4PackSound

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2, A.5, A.7; stage S-E13a, track L-circ):
-- S-N2's `Gap4.kindN`, `.kindS` (first sub-slot) and `.wf` (aligned segments) from the pack rows.

/-!
# What the pack rows give: the kind tie and the stream's constant bytes

The pack rows of `FRNodeRows4.packRows4` sit in the link region of the slots whose stream segment is
16-aligned (the previous node's slot and each aggregate's first sub-slot). From them and the node's
truths (`StmtN4` at `lRows4`, `nodeIRows4`):

* **the bytes of an H element** (`chainBytes4_elem`): stream byte `16e + r` is byte `r` of the F
  element in cell `sCell b0 e` (A.7's pack; `unpack`, `bitF`, `F.toBytes`);
* **the kind tie** (`kindN_of_rows`, `kindS0_of_rows`): stream element 5 is `hdr[0…16)`, which the
  kind row equates to the selected index's constant, so byte 0 of the read proof is the selected
  kind's byte — given that `pf` takes `hdr` from the seed query (`PfHdr`, A.5's `reassemble`);
* **`wf`** (`wf0_of_rows`): the stream's tag and every item's length word of the aligned segment.

**`Gap4R`** is `Gap4` without what these rows give: `kindN` entirely, `kindS` at the first
sub-slot, `wf`'s tag and segment 0. **`gap4_of_rows`**: `StmtN4` + `PfHdr pf` + `Gap4R` give
`Gap4`; **`ks_rev4GR`**, **`certificate_rev4GR`**: `ks_rev4GH`, `certificate_rev4GH` with `hGap`
replaced by `PfHdr pf` and `Gap4R`.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval ProductCircuit

/-! ## The bytes of an H element -/

theorem toBytes_get (a : F) (r : ℕ) (hr : r < 16) :
    (F.toBytes a)[r] = if r < 8 then (a.c₀.val >>> (8 * r).toUInt64).toUInt8
      else (a.c₁.val >>> (8 * (r - 8)).toUInt64).toUInt8 := by
  interval_cases r <;> rfl

/-- Bit `i` of byte `r` of an element is its pack bit `8r + i` (A.7). -/
theorem toBytes_bit (a : F) (r i : ℕ) (hr : r < 16) (hi : i < 8) :
    (F.toBytes a)[r].toBitVec.getLsbD i = bitF a ⟨8 * r + i, by omega⟩ := by
  rw [toBytes_get a r hr, bitF]
  simp only [Fin.val_mk]
  split_ifs with h1 h2 h2
  · simp [hi]; congr 1; omega
  · omega
  · omega
  · simp [hi]; congr 1; omega

theorem decide_unpack (a : F) (j : Fin 128) : decide (unpack a j = 1) = bitF a j := by
  unfold unpack; cases bitF a j <;> simp

/-- A block's message position `512 + 128 s + 8 r + i` is bit `8 r + i` of the block's element
`4 + s`. -/
theorem bitsB4_cell (w : Asg) (blk : ℕ) {s r i : ℕ} (hs : s < 4) (hr : r < 16) (hi : i < 8) :
    N4c.bitsB4 w blk (pos (512 + 128 * s + 8 * r + i)) = bitF (w (blk * 128 + 4 + s)) ⟨8 * r + i, by omega⟩ := by
  rw [N4c.bitsB4_pos w blk (by omega), N4c.zN4, N4c.zW4, ← decide_unpack]
  have h1 : (blk * 2 ^ 14 + (512 + 128 * s + 8 * r + i)) / 128 = blk * 128 + 4 + s := by omega
  have h2 : (blk * 2 ^ 14 + (512 + 128 * s + 8 * r + i)) % 128 = 8 * r + i := by omega
  simp only [h1, h2]

/-- **A message byte is a byte of the block's element** (A.7's pack). -/
theorem readByte_cell (w : Asg) (blk : ℕ) {s r : ℕ} (hs : s < 4) (hr : r < 16) :
    Block.readByte (N4c.bitsB4 w blk) (512 + 128 * s + 8 * r) = (F.toBytes (w (blk * 128 + 4 + s)))[r] := by
  refine UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi => ?_)
  rw [Block.readByte_getLsbD _ _ hi, bitsB4_cell w blk hs hr hi, toBytes_bit _ _ _ hr hi]

/-- **Stream byte `16 e + r` is byte `r` of the H cell `sCell` of element `e`** (outside the last
block, which may be an aggregate's candidate final block). -/
theorem chainBytes4_elem {κ : NodeKind} {σ k : ℕ} (w : Asg) {e r : ℕ} (hr : r < 16)
    (hp : 16 * e + r < N4c.streamB κ σ k) (hb : e / 4 + 1 ≠ N4c.streamL κ σ k) :
    (N4c.chainBytes4 κ σ k w).getD (16 * e + r) 0 = (F.toBytes (w (sCell (N4c.chBase κ σ) e)))[r] := by
  obtain ⟨h1, h2⟩ := Stream.elem_slot e r hr
  rw [N4c.chainBytes4, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hp, Option.map_some, Option.getD_some, h1, h2]
  simp only [N4c.chainW4, N4c.blkOf, if_neg hb]
  rw [show 128 * (4 + e % 4) + 8 * r = 512 + 128 * (e % 4) + 8 * r by ring,
    readByte_cell w _ (Nat.mod_lt _ (by norm_num)) hr]
  rfl

/-- The stream of a signed child (an aggregate with `k ≥ 1` segments) holds one trace: its bytes
and blocks bound those of a segment. -/
theorem stream_ge {κ : NodeKind} {σ k : ℕ} (hk : N4c.isAgg κ σ = true → 1 ≤ k) :
    N4c.segB ≤ N4c.streamB κ σ k ∧ N4c.cLen ≤ N4c.streamL κ σ k := by
  unfold N4c.streamB N4c.streamL
  by_cases h : N4c.isAgg κ σ = true
  · have hk1 := hk h
    rw [if_pos h, if_pos h]
    obtain ⟨h1, h2, -⟩ := N4c.aggB_blocks hk1
    obtain ⟨-, h4, h5⟩ := N4c.strideB_eq
    have : N4c.sBlk ≤ N4c.sBlk * k := Nat.le_mul_of_pos_right _ hk1
    have : N4c.segB ≤ N4c.aggB k := by rw [h1, h2, h5]; omega
    exact ⟨this, by rw [h2]; omega⟩
  · rw [if_neg h, if_neg h]; exact ⟨le_rfl, le_rfl⟩

/-- **An element of the stream's first segment** (`16 e + 80 ≤ segB`) is read off its main-chain
cell. -/
theorem seg0_elem {κ : NodeKind} {σ k : ℕ} (w : Asg) (hk : N4c.isAgg κ σ = true → 1 ≤ k) {e r : ℕ}
    (hr : r < 16) (he : 16 * e + 80 ≤ N4c.segB) :
    (N4c.chainBytes4 κ σ k w).getD (16 * e + r) 0 = (F.toBytes (w (sCell (N4c.chBase κ σ) e)))[r] := by
  obtain ⟨h1, h2⟩ := stream_ge hk
  have hs : N4c.segB = 64 * N4c.cLen := N4c.strideB_eq.2.2
  exact chainBytes4_elem w hr (by omega) (by omega)

/-! ## An aggregate's later segments and its spacers (R-A′) -/

theorem sCell_add (b0 d e : ℕ) : sCell b0 (4 * d + e) = sCell (b0 + d) e := by
  unfold sCell
  rw [show (4 * d + e) / 4 = d + e / 4 by omega, show (4 * d + e) % 4 = e % 4 by omega]
  ring

/-- **An element of an aggregate's stream before its last block** is read off its main-chain cell. -/
theorem agg_elem {κ : NodeKind} {σ k : ℕ} (w : Asg) (hA : N4c.isAgg κ σ = true) (hk : 1 ≤ k) {e r : ℕ}
    (hr : r < 16) (he : e / 4 + 1 < N4c.aggL k) :
    (N4c.chainBytes4 κ σ k w).getD (16 * e + r) 0 = (F.toBytes (w (sCell (N4c.chBase κ σ) e)))[r] := by
  have hB := (N4c.aggB_blocks hk).1
  refine chainBytes4_elem w hr ?_ ?_
  · simp only [N4c.streamB, hA, if_true]; omega
  · simp only [N4c.streamL, hA, if_true]; omega

/-- **Segment `i`'s element `e`** (`i < k`, `16 e + 80 ≤ segB`) of an aggregate's stream: stream
byte `i·strideB + 16 e + r`, read off the cell `sCell (chBase + i·sBlk) e` (R-A′: segment `i` is
segment 0 shifted by `i·sBlk` blocks). -/
theorem segi_elem {κ : NodeKind} {σ k i : ℕ} (w : Asg) (hA : N4c.isAgg κ σ = true) (hi : i < k) {e r : ℕ}
    (hr : r < 16) (he : 16 * e + 80 ≤ N4c.segB) :
    (N4c.chainBytes4 κ σ k w).getD (i * N4c.strideB + 16 * e + r) 0 =
      (F.toBytes (w (sCell (N4c.chBase κ σ + i * N4c.sBlk) e)))[r] := by
  obtain ⟨h1, h2, h3⟩ := N4c.strideB_eq
  have hL := (N4c.aggB_blocks (k := k) (by omega)).2.1
  have hik : i * N4c.sBlk + N4c.sBlk ≤ k * N4c.sBlk := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  have hc : N4c.sBlk * k = k * N4c.sBlk := Nat.mul_comm _ _
  rw [show i * N4c.strideB + 16 * e + r = 16 * (4 * (i * N4c.sBlk) + e) + r by rw [h1]; ring,
    agg_elem w hA (by omega) hr (by omega), sCell_add]

/-- **Spacer `i`'s element `j`** (`1 ≤ i < k`, `j < 8`): stream byte `i·strideB − 128 + 16 j + r`,
read off the cell `sCell (chBase + i·sBlk − 2) j`. -/
theorem spc_elem {κ : NodeKind} {σ k i : ℕ} (w : Asg) (hA : N4c.isAgg κ σ = true) (hi1 : 1 ≤ i) (hi : i < k)
    {j r : ℕ} (hj : j < 8) (hr : r < 16) :
    (N4c.chainBytes4 κ σ k w).getD (i * N4c.strideB - 128 + 16 * j + r) 0 =
      (F.toBytes (w (sCell (N4c.chBase κ σ + i * N4c.sBlk - 2) j)))[r] := by
  obtain ⟨h1, h2, h3⟩ := N4c.strideB_eq
  have hL := (N4c.aggB_blocks (k := k) (by omega)).2.1
  have hik : i * N4c.sBlk + N4c.sBlk ≤ N4c.sBlk * k := by
    rw [Nat.mul_comm N4c.sBlk k, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  have hs : N4c.sBlk ≤ i * N4c.sBlk := Nat.le_mul_of_pos_left _ hi1
  have hsb : 2 ≤ N4c.sBlk := by rw [h2]; decide
  have hm : i * N4c.strideB = 64 * (i * N4c.sBlk) := by rw [h1]; ring
  have hcl : 0 < N4c.cLen := by decide
  rw [hm]
  generalize i * N4c.sBlk = m at *
  generalize N4c.sBlk * k = K at *
  rw [show 64 * m - 128 + 16 * j + r = 16 * (4 * (m - 2) + j) + r by omega,
    agg_elem w hA (by omega) hr (by omega), sCell_add, Nat.add_sub_assoc (by omega)]

/-! ## `seq4`'s items: the seed, then 16-byte multiples -/

/-- The shapes whose items all take a multiple of 16 bytes (the seed's take 159). -/
def shAl : Sh → Bool
  | .seed => false
  | .absorb _ len => len % 16 == 0
  | .squeezes _ _ => true
  | .uni _ => true
  | .rounds _ _ _ _ => true
  | .queries i => colBytes i % 16 == 0 && decide (32 ≤ colBytes i)

theorem sh_al (lv : ℕ → Level) {sh : Sh} (h : shAl sh = true) :
    ∀ it ∈ sh.itemsL lv, it.slen % 16 = 0 ∧ 80 ≤ it.slen := by
  intro it hit
  cases sh with
  | seed => exact absurd h (by decide)
  | absorb f len =>
    simp only [shAl, beq_iff_eq] at h
    simp [Sh.itemsL] at hit; subst hit; simp [Item.slen, Item.qlen]; omega
  | squeezes n ch =>
    simp only [Sh.itemsL, List.mem_replicate] at hit; rw [hit.2]; simp [Item.slen, Item.qlen]
  | uni f =>
    simp only [Sh.itemsL, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> simp [Item.slen, Item.qlen, uniBytes]
  | rounds f n deg inK =>
    simp only [Sh.itemsL, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> cases inK <;> simp [Item.slen, Item.qlen, roundBytes]
  | queries i =>
    simp only [shAl, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    simp only [Sh.itemsL, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
    simp only [posItemsL, List.mem_cons, List.mem_map, List.mem_range] at hl
    rcases hl with rfl | ⟨h', -, rfl⟩ <;> simp [Item.slen, Item.qlen] <;> omega

theorem phasesOf_cons : ∃ tl, phasesOf seq4 = ("seed", .seed) :: tl := ⟨_, rfl⟩

/-- Every `seq4` phase after the seed has 16-byte items (its shape parameters only). -/
theorem phasesOf_al : ((phasesOf seq4).tail).all (fun p => shAl p.2) = true := by
  rw [seq4_eq]; decide +kernel

/-- **`seq4`'s items**: the seed, then items of a multiple of 16 bytes, each at least 80. -/
theorem itemsOf_seq4_al : ∃ rest, itemsOf seq4 = .seed :: rest ∧ ∀ it ∈ rest, it.slen % 16 = 0 ∧ 80 ≤ it.slen := by
  obtain ⟨tl, htl⟩ := phasesOf_cons
  have hal := phasesOf_al
  rw [htl, List.tail_cons] at hal
  refine ⟨tl.flatMap fun p => p.2.itemsL seq4.lv, ?_, fun it hit => ?_⟩
  · rw [itemsOf, htl, List.flatMap_cons]; rfl
  · obtain ⟨p, hp, hit⟩ := List.mem_flatMap.1 hit
    exact sh_al _ (List.all_eq_true.1 hal p hp) it hit

/-! ## The pins give the stream's constant bytes -/

/-- The offsets the items of `its` start at, from `o`, are `≡ 0` or `1 (mod 16)`. -/
def AlAt : ℕ → List Item → Prop
  | _, [] => True
  | o, it :: its => o % 16 ≤ 1 ∧ AlAt (o + it.slen) its

theorem alAt_of (o : ℕ) (its : List Item) (ho : o % 16 = 0) (h : ∀ it ∈ its, it.slen % 16 = 0) :
    AlAt o its := by
  induction its generalizing o with
  | nil => trivial
  | cons it its ih =>
    refine ⟨by omega, ih _ ?_ fun it' h' => h it' (List.mem_cons_of_mem _ h')⟩
    have := h it List.mem_cons_self
    omega

/-- Bytes `ρ … ρ + 7` of an item's element value are its length word (`ρ = o mod 16 ≤ 1`). -/
theorem winF_word (o : ℕ) (it : Item) (ho : o % 16 ≤ 1) {t : ℕ} (ht : t < 8) :
    (F.toBytes (winF o it))[o % 16 + t]'(by omega) = (enc64 it.qlen).getD t 0 := by
  rw [winF, winFB, F.toBytes_ofBytes, Vector.getElem_ofFn]
  simp only [winB]
  have hl : (enc64 it.qlen).length = 8 := by simp [enc64]
  rcases (by omega : o % 16 = 0 ∨ o % 16 = 1) with h | h
  · rw [h, if_neg (by omega), List.nil_append, Nat.zero_add,
      List.getD_append _ _ _ _ (by omega)]
  · rw [h, if_pos rfl, List.singleton_append, Nat.add_comm,
      List.getD_append _ _ _ _ (by simp only [List.length_cons]; omega), List.getD_cons_succ]

/-- **The pins give the length words.** If every pinned element of `wfData o its` has its value's
bytes in `B`, and the items start at offsets `≡ 0, 1 (mod 16)` inside `B`, the length words are in
place. -/
theorem wfAt_of_pins (B : List UInt8) : ∀ (its : List Item) (o : ℕ), AlAt o its →
    o + slenL its ≤ B.length →
    (∀ p ∈ wfData o its, ∀ r (hr : r < 16), B.getD (16 * p.1 + r) 0 = (F.toBytes p.2)[r]) → WfAt B o its
  | [], _, _, _, _ => trivial
  | it :: its, o, ⟨ho, hal⟩, hl, hp => by
    have hs : slenL (it :: its) = it.slen + slenL its := by simp [slenL]
    have h8 : 8 ≤ it.slen := by simp [Item.slen]
    refine ⟨?_, wfAt_of_pins B its _ hal (by omega) fun p hp' => hp p (List.mem_cons_of_mem _ hp')⟩
    have h0 := hp (o / 16, winF o it) List.mem_cons_self
    refine List.ext_getElem (by simp [enc64]; omega) fun t h₁ h₂ => ?_
    have ht : t < 8 := by simpa [enc64] using h₂
    have := h0 (o % 16 + t) (by omega)
    dsimp only at this
    rw [show 16 * (o / 16) + (o % 16 + t) = o + t by omega, winF_word o it ho ht] at this
    rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0, this,
      List.getD_eq_getElem _ 0 (by simp [enc64]; omega)]

theorem slenL_seq4 : 1 + slenL (itemsOf seq4) = N4c.segB := by
  rw [N4c.segB_eq, streamBytesOf, slenL]; congr 2

theorem wfData_lt80 : ∀ (o : ℕ) (its : List Item), (∀ it ∈ its, 80 ≤ it.slen) →
    ∀ q ∈ wfData o its, 16 * q.1 + 80 ≤ o + slenL its
  | _, [], _ => by simp [wfData]
  | o, it :: its, h80 => by
    intro q hq
    simp only [wfData, List.mem_cons] at hq
    have hs : slenL (it :: its) = it.slen + slenL its := by simp [slenL]
    have := h80 it List.mem_cons_self
    rcases hq with rfl | hq
    · dsimp only; omega
    · have := wfData_lt80 (o + it.slen) its (fun it' h' => h80 it' (List.mem_cons_of_mem _ h')) q hq
      omega

/-- **A pinned element of a segment lies in the segment's main-chain blocks.** -/
theorem wfSeg_lt80 : ∀ p ∈ wfSeg, 16 * p.1 + 80 ≤ N4c.segB := fun p hp => by
  obtain ⟨rest, hr, hal⟩ := itemsOf_seq4_al
  have h80 : ∀ it ∈ itemsOf seq4, 80 ≤ it.slen := by
    rw [hr]; intro it hit
    rcases List.mem_cons.1 hit with rfl | hit
    · decide
    · exact (hal it hit).2
  have := wfData_lt80 1 (itemsOf seq4) h80 p (List.mem_of_mem_tail hp)
  have := slenL_seq4
  omega

/-- `wfSeg` is the first elements of the items after the seed, from offset 160. -/
theorem wfSeg_eq {rest : List Item} (hr : itemsOf seq4 = .seed :: rest) : wfSeg = wfData 160 rest := by
  rw [wfSeg, hr, wfData, List.tail_cons, show 1 + Item.seed.slen = 160 from rfl]

/-- **Shifting the items by `16 d` bytes shifts their pinned elements by `d`** (the values depend on
the offset modulo 16 only). -/
theorem wfData_shift (d : ℕ) : ∀ (o : ℕ) (its : List Item),
    wfData (o + 16 * d) its = (wfData o its).map fun p => (p.1 + d, p.2)
  | _, [] => rfl
  | o, it :: its => by
    have ih := wfData_shift d (o + it.slen) its
    have h1 : (o + 16 * d) / 16 = o / 16 + d := by omega
    have h2 : winF (o + 16 * d) it = winF o it := by
      simp only [winF, winB, show (o + 16 * d) % 16 = o % 16 by omega]
    simp only [wfData, List.map_cons, h1, h2, show o + 16 * d + it.slen = o + it.slen + 16 * d by omega, ih]

/-! ## The head rows' readings (R-A′) -/

theorem toBytes_add_hi {a b : F} {r : ℕ} (hr : r < 16)
    (hb : ∀ i (hi : i < 8), bitF b ⟨8 * r + i, by omega⟩ = false) :
    (F.toBytes (a + b))[r] = (F.toBytes a)[r] := by
  refine UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi => ?_)
  rw [toBytes_bit _ _ _ hr hi, toBytes_bit _ _ _ hr hi, bitF_add, hb i hi, Bool.xor_false]

theorem packAt_ev_succ (w : Asg) (cell : ℕ → ℕ) (d n : ℕ) :
    (packAt cell d (n + 1)).ev w =
      (packAt cell d n).ev w + bitBasis ⟨(d + n) % 128, Nat.mod_lt _ (by norm_num)⟩ * w (cell n) := by
  simp [packAt, List.range_succ, Lin.ev]

/-- **Packed Boolean cells at bits `d … d + n − 1`** leave every other bit clear. -/
theorem bitF_packAt_out (w : Asg) (cell : ℕ → ℕ) {d n : ℕ} (hn : d + n ≤ 128)
    (hb : ∀ q < n, w (cell q) = 0 ∨ w (cell q) = 1) (j : Fin 128) (hj : j.val < d ∨ d + n ≤ j.val) :
    bitF ((packAt cell d n).ev w) j = false := by
  induction n with
  | zero => simpa [packAt] using bitF_zero j
  | succ n ih =>
    rw [packAt_ev_succ, bitF_add, ih (by omega) (fun q hq => hb q (by omega)) (by omega)]
    rcases hb n (by omega) with h | h
    · rw [h, mul_zero, bitF_zero]; rfl
    · rw [h, mul_one, bitF_bitBasis, Bool.false_xor, decide_eq_false_iff_not, Fin.ext_iff]
      simp only [Fin.val_mk]
      rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem boolRow_val {w : Asg} {one c : ℕ} (hone : w one = 1) (h : (boolRow one c).Holds w) :
    w c = 0 ∨ w c = 1 := by
  simp only [Row.Holds, boolRow, Lin.ev_cell, Lin.ev_sub, Lin.ev_nil, hone, mul_eq_zero] at h
  rcases h with h | h
  · exact .inl h
  · exact .inr (sub_eq_zero.mp h).symm

theorem decRow_val {w : Asg} {one x : ℕ} {c : F} {bits : Lin} (hone : w one = 1)
    (h : (decRow one x c bits).Holds w) : w x = c + bits.ev w := by
  simp only [Row.Holds, decRow, Lin.ev_cell, Lin.ev_sub, Lin.ev_smul, Lin.ev_nil, hone, one_mul,
    mul_one] at h
  linear_combination h

theorem seedW_word {t : ℕ} (ht : t < 8) : (F.toBytes seedW)[1 + t]'(by omega) = (enc64 119).getD t 0 :=
  winF_word 1 .seed (by norm_num) ht

theorem seedW_tag : (F.toBytes seedW)[0] = tagTrace := by
  rw [seedW, winF, winFB, F.toBytes_ofBytes]; rfl

theorem seedM_seedW (r : ℕ) (hr : r < 16) (h1 : 1 ≤ r) : (F.toBytes seedM)[r] = (F.toBytes seedW)[r] := by
  rw [seedM, seedW, winF, winFB, winFB, F.toBytes_ofBytes, F.toBytes_ofBytes, Vector.getElem_ofFn,
    Vector.getElem_ofFn]
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rfl

theorem spBytes_eq : spBytes = enc64 89 ++ spacerQ.data.toList := by
  rw [spacerQ_bytes, spBytes, List.append_assoc]

theorem spPin_byte {j r : ℕ} (hj : j < 6) (hr : r < 16) :
    (F.toBytes (spPin j))[r] = spBytes.getD (16 * j + r) 0 := by
  rw [spPin, winFB, F.toBytes_ofBytes, Vector.getElem_ofFn]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hr]

/-- **What a segment's head rows give** (R-A′), at `one = 1`: bytes 1–15 of its element 0 are the
seed's (`enc64 119 ‖ "FRSEED0"`); for `s = 0` its byte 0 is the tag `0x54`; for `s ≥ 1` the spacer's
elements 0–5 are its constants and byte 0 of its element 6 (its query's last byte) is zero. -/
structure HeadOk (w : Asg) (b0 s : ℕ) : Prop where
  e0 : ∀ r (hr : r < 16), 1 ≤ r → (F.toBytes (w (sCell b0 0)))[r] = (F.toBytes seedW)[r]
  tag : s = 0 → (F.toBytes (w (sCell b0 0)))[0] = tagTrace
  sp : s ≠ 0 → (∀ j < 6, w (sCell (b0 - 2) j) = spPin j) ∧ (F.toBytes (w (sCell (b0 - 2) 6)))[0] = 0

theorem headOk_of {w : Asg} {one b0 s : ℕ} {cell : ℕ → ℕ} (hone : w one = 1)
    (h : ∀ r ∈ headRows one b0 s cell, r.Holds w) : HeadOk w b0 s := by
  unfold headRows at h
  by_cases hs : s = 0
  · rw [if_pos hs] at h
    have h0 := pinRow_holds hone (h _ (List.mem_singleton_self _))
    exact ⟨fun r _ _ => by rw [h0], fun _ => by rw [h0, seedW_tag], fun h' => absurd hs h'⟩
  · rw [if_neg hs] at h
    have hb : ∀ q < 128, w (cell q) = 0 ∨ w (cell q) = 1 := fun q hq =>
      boolRow_val hone (h _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩))))
    have h6 := decRow_val hone (h _ (List.mem_append_right _ (List.mem_cons_self ..)))
    have h8 := decRow_val hone (h _ (List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))
    refine ⟨fun r hr h1 => ?_, fun h' => absurd h' hs, fun _ => ⟨fun j hj => ?_, ?_⟩⟩
    · rw [h8, toBytes_add_hi hr (fun i hi => bitF_packAt_out w _ (by norm_num)
        (fun q hq => hb _ (by omega)) _ (by simp only; omega)), seedM_seedW r hr h1]
    · exact pinRow_holds hone (h _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))))
    · rw [h6, toBytes_add_hi (by norm_num) (fun i hi => bitF_packAt_out w _ (by norm_num)
        (fun q hq => hb _ (by omega)) _ (by simp only; omega))]
      rfl

/-! ## The pins give the segments' and the spacers' constant bytes -/

/-- **A segment's length words from its pins and head facts**: if stream byte `64 d + 16 e + r` is
byte `r` of the cell `sCell b0 e` (`16 e + 80 ≤ segB`), the segment read at `1 + 64 d` has every
item's length word in place. -/
theorem wfSeg_of_pins {B : List UInt8} {w : Asg} {b0 d s : ℕ}
    (hB : ∀ e r (hr : r < 16), 16 * e + 80 ≤ N4c.segB →
      B.getD (64 * d + 16 * e + r) 0 = (F.toBytes (w (sCell b0 e)))[r])
    (hlen : 64 * d + N4c.segB ≤ B.length)
    (hpin : ∀ p ∈ wfSeg, w (sCell b0 p.1) = p.2) (hh : HeadOk w b0 s) :
    WfAt B (1 + 64 * d) (itemsOf seq4) := by
  obtain ⟨rest, hrs, hal⟩ := itemsOf_seq4_al
  have h159 : Item.seed.slen = 159 := rfl
  have hsl : 1 + (159 + slenL rest) = N4c.segB := by
    rw [← slenL_seq4, hrs]; simp [slenL, h159]
  rw [hrs]
  refine ⟨?_, ?_⟩
  · refine List.ext_getElem (by simp [enc64]; omega) fun t h₁ h₂ => ?_
    have ht : t < 8 := by simpa [enc64] using h₂
    have := hB 0 (1 + t) (by omega) (by decide)
    rw [Nat.mul_zero, Nat.add_zero, hh.e0 _ (by omega) (by omega), seedW_word ht] at this
    rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0,
      show 1 + 64 * d + t = 64 * d + (1 + t) by omega, this, List.getD_eq_getElem _ 0 (by simp [enc64]; omega)]
    rfl
  · rw [h159]
    refine wfAt_of_pins B rest _ (alAt_of _ rest (by omega) fun it h => (hal it h).1) (by omega)
      fun p hp r hr => ?_
    rw [show 1 + 64 * d + 159 = 160 + 16 * (4 * d) by omega, wfData_shift, ← wfSeg_eq hrs] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    dsimp only
    rw [show 16 * (q.1 + 4 * d) + r = 64 * d + 16 * q.1 + r by ring, hB _ _ hr (wfSeg_lt80 q hq),
      hpin q hq]

/-- **A spacer's constant bytes from its pins** (R-A′): if stream byte `o + 16 j + r` is byte `r` of
the cell `sCell bb j` (`j < 7`), the pins of elements 0–5 and element 6's zero byte 0 give
`enc64 89 ‖ spacerQ` at `o`. -/
theorem spAt_of_pins {B : List UInt8} {w : Asg} {bb o : ℕ}
    (hB : ∀ j r, j < 7 → ∀ hr : r < 16, B.getD (o + 16 * j + r) 0 = (F.toBytes (w (sCell bb j)))[r])
    (hlen : o + 97 ≤ B.length) (hp : ∀ j < 6, w (sCell bb j) = spPin j)
    (h6 : (F.toBytes (w (sCell bb 6)))[0] = 0) : SpAt B o := by
  unfold SpAt
  rw [← spBytes_eq]
  have hl : spBytes.length = 97 := by simp [spBytes, enc64, tagAbs]
  refine List.ext_getElem (by simp; omega) fun t h₁ h₂ => ?_
  rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
  rw [hl] at h₂
  by_cases ht : t < 96
  · have := hB (t / 16) (t % 16) (by omega) (Nat.mod_lt _ (by norm_num))
    rw [hp _ (by omega), spPin_byte (by omega) (Nat.mod_lt _ (by norm_num))] at this
    rw [show o + t = o + 16 * (t / 16) + t % 16 by omega, this]
    congr 1; omega
  · have := hB 6 0 (by norm_num) (by norm_num)
    rw [h6] at this
    rw [show t = 96 by omega, show o + 96 = o + 16 * 6 + 0 by rfl, this]
    rfl

/-! ## The kind byte -/

/-- **What `pf` must do with the header** (A.5's `reassemble`: `hdr := payload₀[64…111]`): byte 0
of the proof is byte 71 of the first query (the seed's 7-byte tag, then `vk`, `c`, `hdr`). -/
def PfHdr (pf : Trace → Proof) : Prop := ∀ e tr, byteAt (pf (e :: tr)) 0 = byteAt e.1 71

theorem byteAt_slotPf (pf : Trace → Proof) (κ : NodeKind) (v : ℕ) (w : Asg) :
    byteAt (⟨(slotPf pf κ v w).toArray⟩ : Proof) 0 = byteAt (pf (slotTr4 κ v w)) 0 := by
  rw [byteAt_mk, slotPf, fitL]
  have hn : 0 < piSizeOf seq4 := by rw [piSizeOf_seq4]; norm_num
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hn, List.getElem?_append]
  conv_rhs => rw [show pf (slotTr4 κ v w) = ⟨(pf (slotTr4 κ v w)).data.toList.toArray⟩ from rfl, byteAt_mk]
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD]
  · simp only [not_lt, Nat.le_zero, List.length_eq_zero_iff] at h
    simp [h]

/-- **Byte 0 of a slot's proof read off segment `i`** is the segment's stream byte 80 (its
element 5's byte 0). -/
theorem kind_byte (pf : Trace → Proof) (hpf : PfHdr pf) {κ : NodeKind} {σ k i : ℕ} {w : Asg} {c : UInt8}
    (h5 : (N4c.chainBytes4 κ σ k w).getD (i * N4c.strideB + 16 * 5 + 0) 0 = c) :
    byteAt (pf (segTr κ σ k i w)) 0 = c := by
  obtain ⟨rest, hr, -⟩ := itemsOf_seq4_al
  rw [segTr, hr, Read.readItems, hpf, byteAt_mk]
  show (((N4c.chainBytes4 κ σ k w).drop (1 + i * N4c.strideB + 8)).take Item.seed.qlen).getD 71 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by decide), List.getElem?_drop,
    ← List.getD_eq_getElem?_getD, ← h5]
  congr 1; omega

/-- **The kind row and a selected index give the index's constant.** -/
theorem kindRow_sel {κ : NodeKind} {σ : ℕ} {w : Asg} {G : Grp} {h5 : ℕ} {ι : Kind} (hone : w κ.oneCell = 1)
    (h : (kindRow κ.oneCell h5 (fun ι => κ.oneCell + selR σ ι) G).Holds w)
    (hS : SelOk (slotAsg κ σ w) (protoP (protoOf κ σ)) ι) : w h5 = kConst G ι := by
  have hsel : ∀ ι', w (κ.oneCell + selR σ ι') = if ι' = ι then 1 else 0 := fun ι' => by
    rw [← slotAsg_sel κ σ w ι']; simpa [protoP, Lin.ev_cell] using hS.2 ι'
  rw [kindRow_holds hone h, hsel, hsel, hsel]
  cases ι <;> simp

/-! ## `Gap4` from the pack rows -/

section Gap
variable {impl₀ : OpImpl} {base : NodeKind → OpImpl} (pf : Trace → Proof) {κ : NodeKind}
  {vk c₁ c₂ : Digest} {w : Asg}

/-- **`Gap4` without what the M rows give** (S-E13a; revision 4.4.1, R-A′): the slots' imports
`imp` and `V_A`'s checks `aggChk`. The kind bytes and the streams' constant bytes (`kindN`, `kindS`,
`wf`) are given by the pack rows at every slot (`gap4_of_rows`); `wots` and `aggPad` by S-E13b's
rows (`wots_aggPad_of_rows`). -/
structure Gap4R (impl₀ : OpImpl) (base : NodeKind → OpImpl) (pf : Trace → Proof) (κ : NodeKind)
    (vk c₁ c₂ : Digest) (w : Asg) : Prop where
  imp : ∀ v, N4c.Active4 (rd4 pf) κ w v →
    SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)
  aggChk : ∀ a < N4c.nAgg κ, ∃ vs, (aggSegs (piSizeOf seq4) (N4c.kA (rd4 pf) κ w a)
      ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π).mapM segView = some vs ∧
    aggChecks (N4c.stOf c₁ c₂ (N4c.aggChild κ a)) (rdLE64 ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 8)
      (bytesAt ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 16 32) vs = true

/-- **S-E13b's node rows give `Gap4.wots` and `Gap4.aggPad`** (`W4.gap4_wots_aggPad`), with the
fold: the node rows are slot 1's link rows when their cell check passes; otherwise slot 1 holds the
rejecting row, which no `StmtN4` witness meets. -/
theorem wots_aggPad_of_rows (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    (∀ σ < 2, SigOk vk (N4c.hDig4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) ((rd4 pf).sgn κ σ w).σ = true) ∧
      ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf) κ w a) w := by
  by_cases h : xOkK κ = true
  · refine W4.gap4_wots_aggPad pf (fun r hr => ?_) hS
    refine List.mem_append_right _ ?_
    rw [extRowsC, if_pos rfl, if_pos h, xRowsK_eq]; exact List.mem_append_left _ hr
  · exfalso
    obtain ⟨-, -, -, hE, hP⟩ := hS
    have hone := one_of_pubCells hP
    have h1 : 1 < κ.vslots := by cases κ <;> decide
    have := linkRows_hold (protoFit_of hone hE) h1 hE (rejR κ)
      (List.mem_append_right _ (by rw [extRowsC, if_pos rfl, if_neg h]; simp))
    simp [rejR, Row.Holds, hone] at this

/-- The pack rows of slot `v` hold (they are link rows). -/
theorem packRows_hold {v : ℕ} (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) (hv : v < κ.vslots) :
    ∀ r ∈ packRows4 κ v, r.Holds w := by
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hF := protoFit_of (one_of_pubCells hP) hE
  exact fun r hr => linkRows_hold hF hv hE r (List.mem_append_left _ (List.mem_append_right _ hr))

/-- The pins, the kind tie and the head facts of a slot whose segment base is `b0`. -/
theorem pins_of {v b0 : ℕ} {G : Grp} (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hv : v < κ.vslots) (hb : packB κ v = some (b0, G)) :
    (∀ p ∈ wfSeg, w (sCell b0 p.1) = p.2) ∧
      (kindRow κ.oneCell (sCell b0 5) (fun ι => κ.oneCell + selR v ι) G).Holds w ∧
      HeadOk w b0 (segIx κ v) := by
  have hone := one_of_pubCells hS.2.2.2.2
  have h := packRows_hold hS hv
  refine ⟨fun p hp => pinRow_holds hone (h _ ?_), h _ ?_,
    headOk_of (cell := spC κ (N4c.aggChild κ (aggSlot κ v)) (segIx κ v)) hone fun r hr => h r ?_⟩
  · simp only [packRows4, packWf4, hb, List.mem_append]
    exact Or.inr (List.mem_map.2 ⟨p, hp, rfl⟩)
  · simp [packRows4, packHead4, hb]
  · simp only [packRows4, packHead4, hb, List.mem_append, List.mem_cons]
    exact Or.inl (Or.inr hr)

theorem packB_prev (hp : κ.hasPrev = true) : packB κ 0 = some (N4c.chBase κ 0, nodeGrp) := by
  simp [packB, isPrevSlot, hp]

theorem packB_sub {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) :
    packB κ (N4c.sub κ a i) = some (N4c.chBase κ (N4c.aggChild κ a) + i * N4c.sBlk, segGrp) := by
  obtain ⟨-, hx, hp, -⟩ := sub_facts κ ha hi
  have hs : aggSlot κ (N4c.sub κ a i) = a := slotA_sub κ ha hi
  simp only [packB, hp, hx, hs, Bool.false_eq_true, if_false]

theorem segIx_sub {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) : segIx κ (N4c.sub κ a i) = i := by
  obtain ⟨-, hx, hp, -⟩ := sub_facts κ ha hi
  simp only [segIx, hp, hx, Bool.false_eq_true, if_false]

theorem segIx_prev (hp : κ.hasPrev = true) : segIx κ 0 = 0 := by simp [segIx, isPrevSlot, hp]

theorem maxK_pos (κ : NodeKind) : 0 < κ.maxK := by cases κ <;> decide

/-- **Signed child `σ`'s stream from the pack rows** (R-A′): its tag, every segment's length words
and every spacer's constant bytes. -/
theorem wf_of_rows (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) {σ : ℕ} (hσ : σ < 2) :
    (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w).head? = some tagTrace ∧
      ∀ i < nSeg κ σ w, WfAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (1 + i * N4c.strideB)
        (itemsOf seq4) ∧
      (0 < i → SpAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (i * N4c.strideB - 128)) := by
  have hone := one_of_pubCells hS.2.2.2.2
  have hF := protoFit_of hone hS.2.2.2.1
  have hst := N4c.strideB_eq
  have hlen : ∀ k, (N4c.chainBytes4 κ σ k w).length = N4c.streamB κ σ k := fun k =>
    Stream.streamBytes_length _ _
  by_cases hA : N4c.isAgg κ σ = true
  · obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
    have hlk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ (N4c.aggOf κ σ) i), r.Holds w :=
      fun i hi => linkRows_hold hF (sub_facts κ ha hi).1 hS.2.2.2.1
    have hk1 : 1 ≤ kAct κ (N4c.aggOf κ σ) w := (actK_kAct hone ha hS.2.2.1 hlk).1
    have hkm := kAct_le κ (N4c.aggOf κ σ) w
    have hk : N4c.kOf (rd4 pf) κ w σ = kAct κ (N4c.aggOf κ σ) w := by
      rw [N4c.kOf, if_pos hA, kA_rd4 pf κ ha]
    have hn : nSeg κ σ w = kAct κ (N4c.aggOf κ σ) w := by rw [nSeg, if_pos hA]
    rw [hk, hn]
    set k := kAct κ (N4c.aggOf κ σ) w
    have hB : (N4c.chainBytes4 κ σ k w).length = N4c.aggB k := by rw [hlen, N4c.streamB, if_pos hA]
    have hBk := N4c.aggB_blocks hk1
    -- sub-slot `i`'s pins
    have hpin : ∀ i < k, (∀ p ∈ wfSeg, w (sCell (N4c.chBase κ σ + i * N4c.sBlk) p.1) = p.2) ∧
        HeadOk w (N4c.chBase κ σ + i * N4c.sBlk) i := fun i hi => by
      have hi' : i < κ.maxK := by omega
      have h := pins_of hS (sub_facts κ ha (i := i) hi').1 (packB_sub (i := i) ha hi')
      simp only [hc, segIx_sub ha hi'] at h
      exact ⟨h.1, h.2.2⟩
    have hseg : ∀ i < k, WfAt (N4c.chainBytes4 κ σ k w) (1 + i * N4c.strideB) (itemsOf seq4) := fun i hi => by
      obtain ⟨hp, hh⟩ := hpin i hi
      have h64 : i * N4c.strideB = 64 * (i * N4c.sBlk) := by rw [hst.1]; ring
      rw [h64]
      refine wfSeg_of_pins (fun e r hr he => ?_) ?_ hp hh
      · rw [← h64]; exact segi_elem w hA hi hr he
      · have : (i + 1) * N4c.strideB ≤ k * N4c.strideB := Nat.mul_le_mul_right _ (by omega)
        rw [hB, ← h64, hBk.2.2, Nat.add_one_mul] at *
        have : N4c.segB + 128 = N4c.strideB := by simp [N4c.strideB, N4c.spacerB, N4c.segB]
        omega
    refine ⟨?_, fun i hi => ⟨hseg i hi, fun hi0 => ?_⟩⟩
    · -- the tag
      have h0 := (hpin 0 (by omega)).2.tag rfl
      have he := segi_elem w hA (k := k) (i := 0) (by omega) (e := 0) (r := 0) (by norm_num) (by decide)
      simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_zero] at he h0
      have h0lt : 0 < N4c.aggB k := by
        have := Nat.le_mul_of_pos_right N4c.sBlk hk1
        rw [hBk.1, hBk.2.1]; simp only [N4c.sBlk] at *; omega
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [hB]; exact h0lt), ← List.getD_eq_getElem _ 0,
        he, h0]
    · -- spacer `i`
      obtain ⟨hpj, h6⟩ := (hpin i hi).2.sp (by omega)
      refine spAt_of_pins (bb := N4c.chBase κ σ + i * N4c.sBlk - 2) (fun j r hj hr => spc_elem w hA hi0 hi
        (by omega) hr) ?_ hpj h6
      have : (i + 1) * N4c.strideB ≤ k * N4c.strideB := Nat.mul_le_mul_right _ (by omega)
      have : 128 ≤ i * N4c.strideB := le_trans (by rw [hst.1, hst.2.1]; decide)
        (Nat.le_mul_of_pos_left _ hi0)
      rw [hB, hBk.2.2, Nat.add_one_mul] at *
      omega
  · have hp : κ.hasPrev = true ∧ σ = 0 := by
      cases κ <;> simp_all [N4c.isAgg, NodeKind.hasPrev]
    obtain ⟨hp, rfl⟩ := hp
    have hk : N4c.kOf (rd4 pf) κ w 0 = 0 := by rw [N4c.kOf, if_neg hA]
    have hn : nSeg κ 0 w = 1 := by rw [nSeg, if_neg hA]
    rw [hk, hn]
    have hk0 : N4c.isAgg κ 0 = true → 1 ≤ 0 := fun h => absurd h hA
    have h := pins_of hS (vslots_pos κ) (packB_prev hp)
    rw [segIx_prev hp] at h
    obtain ⟨hpin, -, hh⟩ := h
    have hB : (N4c.chainBytes4 κ 0 0 w).length = N4c.segB := by rw [hlen, N4c.streamB, if_neg hA]
    refine ⟨?_, fun i hi => ?_⟩
    · have he := seg0_elem w hk0 (e := 0) (r := 0) (by norm_num) (by decide)
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [hB]; decide), ← List.getD_eq_getElem _ 0]
      simpa [hh.tag rfl] using he
    · obtain rfl : i = 0 := by omega
      refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
      have := wfSeg_of_pins (d := 0) (fun e r hr he => by simpa using seg0_elem w hk0 hr he)
        (by rw [hB]; omega) hpin hh
      simpa using this

/-- **`Gap4.kindS` from the pack rows** (every sub-slot; R-A′): an active sub-slot's proof has the
selected segment kind's byte. -/
theorem kindS_of_rows (hpf : PfHdr pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ a < N4c.nAgg κ, ∀ i < kAct κ a w, ∀ ι, SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι →
      byteAt ((rd4 pf).slotπ κ (N4c.sub κ a i) w) 0 = (segAt ι).byte := by
  have hone := one_of_pubCells hS.2.2.2.2
  intro a ha i hi ι hι
  have hkm := kAct_le κ a w
  have hi' : i < κ.maxK := by omega
  obtain ⟨-, hx, hpv, -⟩ := sub_facts κ ha hi'
  obtain ⟨-, hrow, -⟩ := pins_of hS (sub_facts κ ha (i := i) hi').1 (packB_sub (i := i) ha hi')
  have h5 := kindRow_sel hone hrow (by rw [protoOf_seg hpv]; exact hι)
  show byteAt (⟨(slotPf pf κ (N4c.sub κ a i) w).toArray⟩ : Proof) 0 = _
  rw [byteAt_slotPf]
  simp only [slotTr4, hpv, Bool.false_eq_true, if_false, slotA_sub κ ha (by omega : i < κ.maxK), hx]
  rw [kind_byte pf hpf (segi_elem w (N4c.isAgg_aggChild κ a) hi (by norm_num) (by decide)), h5]
  exact (kConst_byte ι).2

/-- **`gap4_of_rows`**: the node's truths, `PfHdr pf` and `Gap4R` give S-N2's `Gap4`. -/
theorem gap4_of_rows (hpf : PfHdr pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hG : Gap4R impl₀ base pf κ vk c₁ c₂ w) : Gap4 impl₀ base pf κ vk c₁ c₂ w := by
  have hone := one_of_pubCells hS.2.2.2.2
  have hF := protoFit_of hone hS.2.2.2.1
  have hL := hS.2.2.1
  have hlk : ∀ a < N4c.nAgg κ, ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w :=
    fun a ha i hi => linkRows_hold hF (sub_facts κ ha hi).1 hS.2.2.2.1
  obtain ⟨hwots, hpad⟩ := wots_aggPad_of_rows pf hS
  refine ⟨hG.imp, ?_, ?_, fun σ hσ => wf_of_rows pf hS hσ, hG.aggChk, hpad, hwots⟩
  · -- kindN
    intro hp ι hι
    obtain ⟨-, hrow, -⟩ := pins_of hS (vslots_pos κ) (packB_prev hp)
    have h5 := kindRow_sel hone hrow (by rw [protoOf_zero hp]; exact hι)
    have hk0 : N4c.isAgg κ 0 = true → 1 ≤ 0 := fun h => by simp [isAgg_zero hp] at h
    show byteAt (sgn4 pf κ 0 w).π 0 = _
    rw [sgn4, if_neg (by simp [isAgg_zero hp]), byteAt_slotPf]
    simp only [slotTr4, isPrevSlot, hp, Bool.true_and, beq_self_eq_true, if_true]
    rw [kind_byte pf hpf (i := 0) (by simpa using seg0_elem w hk0 (e := 5) (r := 0) (by norm_num) (by decide)),
      h5]
    exact (kConst_byte ι).1
  · -- kindS, every sub-slot
    exact kindS_of_rows pf hpf hS

/-- (Converse) `Gap4` gives `Gap4R`: nothing beyond `Gap4` is asked. -/
theorem gap4R_of_gap4 (hG : Gap4 impl₀ base pf κ vk c₁ c₂ w) : Gap4R impl₀ base pf κ vk c₁ c₂ w :=
  ⟨hG.imp, hG.aggChk⟩

end Gap

/-! ## Controls -/

/-- (+) The kind row holds at a one-hot selection with the element at the selected constant;
(−) with the element at another index's constant it fails (`kConst_ne`). -/
theorem kindRow_ctl (w : Asg) (one h5 : ℕ) (sel : Kind → ℕ) (hone : w one = 1)
    (hs : w (sel .L32) = 0 ∧ w (sel .P30) = 1 ∧ w (sel .N30) = 0) :
    (w h5 = kConst nodeGrp .P30 → (kindRow one h5 sel nodeGrp).Holds w) ∧
      (w h5 = kConst nodeGrp .L32 → ¬ (kindRow one h5 sel nodeGrp).Holds w) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have key : (kindRow one h5 sel nodeGrp).Holds w ↔ w h5 = kConst nodeGrp .P30 := by
    simp only [kindRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, hone, one_mul, Lin.ev_nil, sub_eq_zero]
    simp [Circ.kinds, Lin.ev, h1, h2, h3]
  refine ⟨key.2, fun h hr => kConst_ne.1 (h.symm.trans (key.1 hr))⟩

/-- (+/−) **`SpAt`** (R-A′): the spacer's encoding `enc64 89 ‖ spacerQ ‖ a` meets it (any answer
`a`); 129 zero bytes do not, nor does the spacer with its last query byte set. -/
theorem spAt_ctl : SpAt (enc64 89 ++ spacerQ.data.toList ++ List.replicate 32 7) 0 ∧
    ¬ SpAt (List.replicate 129 0) 0 ∧
    ¬ SpAt (enc64 89 ++ (spacerQ.data.toList.take 88 ++ [1]) ++ List.replicate 32 7) 0 := by
  unfold SpAt; decide

/-- (+) **The masked element 0** (R-A′): an element whose bytes 1–15 are the seed's and whose byte
0 is any `b` is `seedM` plus `b`'s bits at positions 0–7: the decomposition row holds with the bits
of `b = 1`. (−) An element differing from `seedM` in bit 8 (byte 1) fails the row for every Boolean
choice of the 8 bit cells. -/
theorem decRow_ctl :
    (decRow 0 1 seedM (packAt (fun q => 2 + q) 0 8)).Holds
      (fun c => if c = 0 then 1 else if c = 1 then seedM + bitBasis 0 else if c = 2 then 1 else 0) ∧
    ∀ w : Asg, w 0 = 1 → w 1 = seedM + bitBasis 8 → (∀ q < 8, w (2 + q) = 0 ∨ w (2 + q) = 1) →
      ¬ (decRow 0 1 seedM (packAt (fun q => 2 + q) 0 8)).Holds w := by
  refine ⟨?_, fun w h0 h1 hb h => ?_⟩
  · simp only [Row.Holds, decRow, Lin.ev_cell, Lin.ev_sub, Lin.ev_smul, Lin.ev_nil]
    simp [packAt, Lin.ev, List.range_succ]
  · have hv := decRow_val h0 h
    rw [h1] at hv
    have := congrArg (fun x => bitF x ⟨8, by norm_num⟩) hv
    simp only [bitF_add] at this
    rw [bitF_packAt_out w _ (by norm_num) (fun q hq => hb q hq) _ (by simp)] at this
    rw [bitF_bitBasis] at this
    simp at this

/-- (+/−) **Every slot is packed** (R-A′): `N8`'s slot 5 (aggregate 1's sub-slot 1) reads its segment
at the aggregate's first block plus `sBlk`, `N4`'s slot 2 (sub-slot 1) at its aggregate's plus
`sBlk`, not at sub-slot 0's. -/
theorem packB_ctl : (packB .N8 5).map Prod.fst = some (N4c.chBase .N8 1 + N4c.sBlk) ∧
    (packB .N4 2).map Prod.fst = some (N4c.chBase .N4 1 + N4c.sBlk) ∧
    (packB .N4 2).map Prod.fst ≠ (packB .N4 1).map Prod.fst := by
  refine ⟨rfl, rfl, by decide⟩

/-- (+) A proof decoder that takes byte 0 from the seed query's byte 71 meets `PfHdr`; (−) the
empty decoder does not (a seed query with a kind byte at 71). -/
theorem pfHdr_ctl : PfHdr (fun tr => ⟨#[byteAt (tr.headD (ByteArray.empty, default)).1 71]⟩) ∧
    ¬ PfHdr (fun _ => ByteArray.empty) := by
  refine ⟨fun e tr => ?_, fun h => ?_⟩
  · show byteAt ⟨[byteAt e.1 71].toArray⟩ 0 = _
    rw [byteAt_mk]; rfl
  have := h (⟨(List.replicate 72 (0x4e : UInt8)).toArray⟩, default) []
  revert this; decide

end N4s

namespace Snd.P4f
open RecursionFast FR.Rev4 FR.N4s FR.X.X4 FR.Circ

section G
variable (fin : Finals) (lRows : List Row) (κs₀ : F)

/-- **`ks_rev4GH` with the pack rows** (S-E13a): `hGap` is replaced by `PfHdr pf` (A.5's
`reassemble`, S-H4) and `Gap4R`, which no longer asks for the previous node's kind byte, the first
sub-slot's kind byte, the streams' tag or segment 0's length words. -/
theorem ks_rev4GR (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (hO : R4.SegOut4 (VsegC (Impl.implC fin lRows κs₀)) vk) (pf : Trace → Proof) (hpf : PfHdr pf)
    (hGap : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      Gap4R (Impl.implC fin lRows κs₀) (fun _ => Impl.implC fin lRows κs₀) pf κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, X4.GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV :=
  ks_rev4GH fin lRows κs₀ S vk hV hq hE hε hO pf
    (fun κ w c₁ c₂ hS => gap4_of_rows pf hpf hS (hGap κ w c₁ c₂ hS)) D hL

/-- `Resid4GH` with the pack rows: `PfHdr pf` and `Gap4R` in place of `Gap4`. -/
structure Resid4GR (pf : Trace → Proof) (S : Submission) (nd : X.XIR) (D : NodeDec4 nd) (vk : Digest) :
    Prop where
  out : R4.SegOut4 (VsegC (Impl.implC fin lRows κs₀)) vk
  gap : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
    Gap4R (Impl.implC fin lRows κs₀) (fun _ => Impl.implC fin lRows κs₀) pf κ vk c₁ c₂ w
  links : ∀ κ L c π, X4.GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)

/-- **The contract's `Certificate`** with the pack rows (`certificate_rev4GH` at `Gap4R`). -/
theorem certificate_rev4GR (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd)
    (hfuel : S.fuel = X.fuel) (hnd : DecOk4 nd) (D : NodeDec4 nd) (pf : Trace → Proof) (hpf : PfHdr pf)
    (hR : ∀ vk, Resid4GR fin lRows κs₀ pf S nd D vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S :=
  certificate_rev4GH fin lRows κs₀ S hV hq hE hε hext hfuel hnd D pf
    (fun vk => ⟨(hR vk).out, fun κ w c₁ c₂ hS => gap4_of_rows pf hpf hS ((hR vk).gap κ w c₁ c₂ hS),
      (hR vk).links⟩) hC hδ

end G

end Snd.P4f
end FR

end G6_FRNodeRows4PackSound

section G6_FRNodeRows4AggChkG

-- New for `flock-recursive` (PACK-4.4.1 §1.3 `input`/`hashStmt` rows, §4.3, §7 B4; stage B4, track L-circ).

/-!
# `Gap4R.aggChk` from the node rows

**`aggChk_of_rows`**: on the node's truths (`StmtN4` at `lRows4`, `nodeIRows4`), with the proof
decoder's positional facts `PfHdr pf` (byte 0) and `PfView pf` (the view's fields), every
aggregate meets `V_A`'s checks (`aggChecks`) against its statement `c_A`:

* the views exist (`kindS_of_rows`) and read the sub-slots' stream elements (`view_sub`):
  `start = dg2 (6, 7)`, `h = sh1 (13, 14, 15)`, `n = n8 (15)`;
* `c_A = leafStmt e n` with `π_A`'s `e`, `n` (`stmt_A`): the `hashA` block `cAB` (Z truth,
  `hashA_leafStmt`) hashes `tagLeaf ‖ e ‖ enc64 n`, and its `h_out` is `c_A` (`PubCells4`). No row;
* `1 ≤ k ≤ 4` (`actK_kAct`); the lengths, the sum, the end and the chaining from the check rows
  (`FRNodeRows4AggChkS`).

**`gap4_of_rowsI`**: `StmtN4`, `PfHdr pf`, `PfView pf` and `Gap4R.imp` give S-N2's `Gap4`: B4 leaves
`imp` as the node circuit's only gap.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Finset

/-! ## The proof decoder's view fields -/

/-- **What `pf` must do with the header and the statement** (A.5's `reassemble`, fields 0 and 1):
the proof's bytes `0 … 47` (`hdr`) are the seed query's bytes `71 … 118`, its bytes `48 … 175`
(`stmt`) the second query's message (bytes `40 … 167`). A segment view reads `hdr.pub` (`16 … 47`)
and `stmt[1 … 41)`. -/
def PfView (pf : Trace → Proof) : Prop :=
  ∀ e₀ e₁ tr, (∀ j < 48, byteAt (pf (e₀ :: e₁ :: tr)) j = byteAt e₀.1 (71 + j)) ∧
    ∀ j < 128, byteAt (pf (e₀ :: e₁ :: tr)) (48 + j) = byteAt e₁.1 (40 + j)

theorem byteAt_slotPfP (pf : Trace → Proof) (κ : NodeKind) (v : ℕ) (w : Asg) {p : ℕ} (hp : p < piSizeOf seq4) :
    byteAt (⟨(slotPf pf κ v w).toArray⟩ : Proof) p = byteAt (pf (slotTr4 κ v w)) p := by
  rw [byteAt_mk, slotPf, fitL]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hp, List.getElem?_append]
  conv_rhs => rw [show pf (slotTr4 κ v w) = ⟨(pf (slotTr4 κ v w)).data.toList.toArray⟩ from rfl, byteAt_mk]
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (not_lt.1 h), List.getElem?_replicate]
    split_ifs <;> rfl

theorem itemsOf_seq4_two : ∃ rest, itemsOf seq4 = .seed :: .absorb 128 :: rest := ⟨_, rfl⟩

theorem entry_byte (B : List UInt8) (o : ℕ) (it : Item) {j : ℕ} (hj : j < it.qlen) :
    byteAt (Read.entryAt B o it).1 j = B.getD (o + 8 + j) 0 := by
  show byteAt ⟨((B.drop (o + 8)).take it.qlen).toArray⟩ j = _
  rw [byteAt_mk, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]

theorem fb_eq (a : F) {r : ℕ} (hr : r < 16) : fb a r = (F.toBytes a)[r] := by
  unfold fb; simp only [Nat.mod_eq_of_lt hr]

/-- **Byte `p` of sub-slot `i`'s segment** is byte `p mod 16` of its element `p / 16`. -/
theorem seg_byte {κ : NodeKind} {a k i : ℕ} (w : Asg) (hi : i < k) {p : ℕ} (hp : p < 400) :
    (N4c.chainBytes4 κ (N4c.aggChild κ a) k w).getD (i * N4c.strideB + p) 0 =
      fb (w (sE κ (N4c.aggChild κ a) i (p / 16))) (p % 16) := by
  have h := segi_elem w (N4c.isAgg_aggChild κ a) hi (e := p / 16) (r := p % 16) (Nat.mod_lt _ (by norm_num))
    (by simp only [N4c.segB]; omega)
  rw [show i * N4c.strideB + 16 * (p / 16) + p % 16 = i * N4c.strideB + p by omega] at h
  rw [h, fb_eq _ (Nat.mod_lt _ (by norm_num))]
  rfl

theorem fb_congr_mod (a : F) {k k' : ℕ} (h : k % 16 = k' % 16) : fb a k = fb a k' := by
  rw [← fb_mod a k, ← fb_mod a k', h]

section View
variable {pf : Trace → Proof} {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}

/-- Sub-slot `i` of aggregate `a` reads its segment of the aggregate's stream. -/
theorem slotTr_sub {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) :
    slotTr4 κ (N4c.sub κ a i) w = segTr κ (N4c.aggChild κ a) (kAct κ a w) i w := by
  obtain ⟨-, hx, hpv, -⟩ := sub_facts κ ha hi
  simp only [slotTr4, hpv, Bool.false_eq_true, if_false, slotA_sub κ ha hi, hx]

/-- **An active sub-slot's view** reads its stream: kind from the selector, start from elements
`6, 7`, end from `13–15`, length from `15`. -/
theorem view_sub (hpf : PfHdr pf) (hpv : PfView pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    {a : ℕ} (ha : a < N4c.nAgg κ) {i : ℕ} (hi : i < kAct κ a w) {ι : Kind}
    (hι : SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι) :
    segView ((rd4 pf).slotπ κ (N4c.sub κ a i) w) = some ⟨segAt ι,
      dg2 (w (sE κ (N4c.aggChild κ a) i 6)) (w (sE κ (N4c.aggChild κ a) i 7)),
      sh1 (w (sE κ (N4c.aggChild κ a) i 13)) (w (sE κ (N4c.aggChild κ a) i 14)) (w (sE κ (N4c.aggChild κ a) i 15)),
      n8 (w (sE κ (N4c.aggChild κ a) i 15))⟩ := by
  have hkm := kAct_le κ a w
  have hb0 := kindS_of_rows pf hpf hS a ha i hi ι hι
  set σ := N4c.aggChild κ a
  set B := N4c.chainBytes4 κ σ (kAct κ a w) w
  obtain ⟨rest, hr⟩ := itemsOf_seq4_two
  have htr : slotTr4 κ (N4c.sub κ a i) w = Read.entryAt B (1 + i * N4c.strideB) .seed ::
      Read.entryAt B (1 + i * N4c.strideB + 159) (.absorb 128) :: Read.readItems B (1 + i * N4c.strideB + 159 + 208) rest := by
    rw [slotTr_sub ha (by omega), segTr, hr]; rfl
  obtain ⟨hv1, hv2⟩ := hpv (Read.entryAt B (1 + i * N4c.strideB) .seed)
    (Read.entryAt B (1 + i * N4c.strideB + 159) (.absorb 128)) (Read.readItems B (1 + i * N4c.strideB + 159 + 208) rest)
  have hps : 89 ≤ piSizeOf seq4 := by rw [piSizeOf_seq4]; norm_num
  -- the proof's bytes `16 … 47` and `49 … 88`
  have hP1 : ∀ j < 32, byteAt ((rd4 pf).slotπ κ (N4c.sub κ a i) w) (16 + j) =
      fb (w (sE κ σ i ((96 + j) / 16))) ((96 + j) % 16) := fun j hj => by
    show byteAt (⟨(slotPf pf κ _ w).toArray⟩ : Proof) _ = _
    rw [byteAt_slotPfP pf κ _ w (by omega), htr, hv1 (16 + j) (by omega),
      entry_byte _ _ _ (by simp [Item.qlen]; omega),
      show 1 + i * N4c.strideB + 8 + (71 + (16 + j)) = i * N4c.strideB + (96 + j) by ring, seg_byte w hi (by omega)]
  have hP2 : ∀ j < 40, byteAt ((rd4 pf).slotπ κ (N4c.sub κ a i) w) (49 + j) =
      fb (w (sE κ σ i ((209 + j) / 16))) ((209 + j) % 16) := fun j hj => by
    show byteAt (⟨(slotPf pf κ _ w).toArray⟩ : Proof) _ = _
    rw [byteAt_slotPfP pf κ _ w (by omega), htr, show 49 + j = 48 + (1 + j) by ring, hv2 (1 + j) (by omega),
      entry_byte _ _ _ (by simp [Item.qlen]; omega),
      show 1 + i * N4c.strideB + 159 + 8 + (40 + (1 + j)) = i * N4c.strideB + (209 + j) by ring,
      seg_byte w hi (by omega)]
  simp only [segView, hb0, SegKind.ofByte?_byte, Option.map_some, Option.some.injEq, SegView.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · refine Vector.ext fun j hj => ?_
    rw [bytesAt, Vector.getElem_ofFn, hP1 j hj, dg2, Vector.getElem_ofFn, catByte]
    simp only [Fin.val_mk]
    refine (fb_congr_mod _ (show (96 + j) % 16 % 16 = j % 16 by omega)).trans ?_
    congr 1
    rcases (by omega : j / 16 = 0 ∨ j / 16 = 1) with h | h
    · rw [h, show (96 + j) / 16 = 6 by omega]; rfl
    · rw [h, show (96 + j) / 16 = 7 by omega]; rfl
  · refine Vector.ext fun j hj => ?_
    rw [bytesAt, Vector.getElem_ofFn, hP2 j (by omega), sh1, Vector.getElem_ofFn, catByte]
    simp only [Fin.val_mk]
    refine (fb_congr_mod _ (show (209 + j) % 16 % 16 = (1 + j) % 16 by omega)).trans ?_
    congr 1
    rcases (by omega : (1 + j) / 16 = 0 ∨ (1 + j) / 16 = 1 ∨ (1 + j) / 16 = 2) with h | h | h
    · rw [h, show (209 + j) / 16 = 13 by omega]; rfl
    · rw [h, show (209 + j) / 16 = 14 by omega]; rfl
    · rw [h, show (209 + j) / 16 = 15 by omega]; rfl
  · rw [rdLE64, n8, lsum_range]
    refine sum_congr rfl fun t ht => ?_
    have ht := mem_range.1 ht
    rw [show 81 + t = 49 + (32 + t) by ring, hP2 _ (by omega), show (209 + (32 + t)) / 16 = 15 by omega]
    congr 2
    exact fb_congr_mod _ (by omega)

end View

/-! ## The aggregate's statement: `c_A = leafStmt e n` -/

theorem hA_get (κ : NodeKind) (a : ℕ) (w : Asg) {p : ℕ} (hp : p < 41) :
    (hA κ a w).getD p 0 = fb (w (hc (N4c.cAB κ a) (4 + p / 16))) (p % 16) := by
  rw [hA, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
    Option.map_some, Option.getD_some, Nat.mod_eq_of_lt (show p < 64 by omega),
    show Blake2sCircuit.msgBase + 8 * p = 8 * (64 + p) by rw [show Blake2sCircuit.msgBase = 512 from rfl]; ring,
    readByte_hc w _ (by omega),
    show (64 + p) / 16 = 4 + p / 16 by omega]
  exact fb_congr_mod _ (by omega)

theorem hAe_eq (κ : NodeKind) (a : ℕ) (w : Asg) :
    hAe κ a w = sh1 (w (hc (N4c.cAB κ a) 4)) (w (hc (N4c.cAB κ a) 5)) (w (hc (N4c.cAB κ a) 6)) := by
  refine Vector.ext fun j hj => ?_
  rw [hAe, Vector.getElem_ofFn, hA_get κ a w (by omega), sh1, Vector.getElem_ofFn, catByte]
  simp only [Fin.val_mk]
  refine (fb_mod _ _).trans ?_
  congr 1
  rcases (by omega : (1 + j) / 16 = 0 ∨ (1 + j) / 16 = 1 ∨ (1 + j) / 16 = 2) with h | h | h <;> rw [h] <;> rfl

theorem hAn_eq (κ : NodeKind) (a : ℕ) (w : Asg) : hAn κ a w = n8 (w (hc (N4c.cAB κ a) 6)) := by
  rw [hAn, n8, lsum_range]
  refine sum_congr rfl fun t ht => ?_
  have ht := mem_range.1 ht
  rw [hA_get κ a w (by omega), show (33 + t) / 16 = 2 by omega]
  congr 2
  exact fb_congr_mod _ (by omega)

theorem ofListLE_sum : ∀ l : List UInt8,
    CompPoly.Bytes.ofListLE l = ∑ t ∈ range l.length, (l.getD t 0).toNat * 256 ^ t
  | [] => rfl
  | d :: l => by
    rw [CompPoly.Bytes.ofListLE_cons, ofListLE_sum l, List.length_cons, sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [Nat.add_comm]; congr 1
    refine sum_congr rfl fun t _ => by ring

/-- `hA`'s last eight bytes are `enc64 hAn`. -/
theorem hA_drop (κ : NodeKind) (a : ℕ) (w : Asg) : (hA κ a w).drop 33 = enc64 (hAn κ a w) := by
  have hl : ((hA κ a w).drop 33).length = 8 := by simp [hA, Stream.streamBytes_length]
  have hn : hAn κ a w = CompPoly.Bytes.ofListLE ((hA κ a w).drop 33) := by
    rw [ofListLE_sum, hl, hAn, lsum_range]
    refine sum_congr rfl fun t _ => ?_
    simp [List.getD_eq_getElem?_getD]
  rw [hn, Snd.enc64_toListLE, ← hl, CompPoly.Bytes.toListLE_ofListLE]

/-- **`hashA`'s message is `tagLeaf ‖ hAe ‖ enc64 hAn`** (its first byte is the kind's tag). -/
theorem hA_eq (κ : NodeKind) (a : ℕ) (w : Asg) (h0 : (hA κ a w).getD 0 0 = tagLeaf) :
    hA κ a w = tagLeaf :: (hAe κ a w).toList ++ enc64 (hAn κ a w) := by
  have hl : (hA κ a w).length = 41 := by simp [hA, Stream.streamBytes_length]
  conv_lhs => rw [← List.take_append_drop 33 (hA κ a w)]
  rw [hA_drop]
  congr 1
  refine List.ext_getElem (by simp [hl]) fun p h₁ h₂ => ?_
  rw [List.getElem_take, ← List.getD_eq_getElem _ 0]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [h0, List.getElem_cons_zero]
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [List.getElem_cons_succ, Vector.getElem_toList]
    unfold hAe
    rw [Vector.getElem_ofFn]
    congr 1; simp only [Fin.val_mk]; omega


/-- `cAB` is a `hashA` block of the node. -/
theorem cAB_tgt (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) :
    N4c.cAB κ a < κ.blocks ∧ N4c.nodeKind4 κ (N4c.cAB κ a) = some Kinds.hashA.target := by
  have hm := N4c.tailIvs_mem κ ha ⟨.hashA, N4c.cAB κ a, N4c.cAB κ a + 1, fun _ => some Kinds.hashA.target⟩
    (by simp [N4c.tailIvs])
  have hk : N4c.TIv.mem ⟨.hashA, N4c.cAB κ a, N4c.cAB κ a + 1, fun _ => some Kinds.hashA.target⟩
      (N4c.cAB κ a) = true := by simp [N4c.TIv.mem]
  exact ⟨N4c.mem_lt hm hk, N4c.tgt_of_mem hm hk⟩

/-- **The statement cells of an aggregate child are `c_A`**: `cAB`'s `h_out` (`PubCells4`). -/
theorem stmt_cells {κ : NodeKind} {w : Asg} {vk c₁ c₂ : Digest} (hP : N4c.PubCells4 κ w vk c₁ c₂) {a : ℕ}
    (ha : a < N4c.nAgg κ) :
    Read.digestOf w (hc (N4c.cAB κ a) 2) (hc (N4c.cAB κ a) 3) = N4c.stOf c₁ c₂ (N4c.aggChild κ a) := by
  have hσ := N4c.aggChild_lt κ ha
  have hs : ∀ h, N4c.stC κ (N4c.aggChild κ a) h = hc (N4c.cAB κ a) (2 + h) := fun h => by
    simp only [N4c.stC, N4c.isAgg_aggChild, if_true, N4c.aggOf_aggChild κ ha, hc]; ring
  unfold N4c.PubCells4 at hP
  simp only [N4c.cells4, List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.cons_append,
    Node.pubVals, Node.halves, List.cons.injEq] at hP
  rw [← hs 0, ← hs 1]
  rcases (by omega : N4c.aggChild κ a = 0 ∨ N4c.aggChild κ a = 1) with h | h <;> rw [h] <;> simp only [N4c.stOf]
  · exact Snd.digestOf_halves hP.2.2.2.1 hP.2.2.2.2.1
  · exact Snd.digestOf_halves hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.1

/-- **`c_A = leafStmt e n`** with `e`, `n` read off `cAB`'s message (no row: the `hashA` block). -/
theorem stmt_A {κ : NodeKind} {w : Asg} {vk c₁ c₂ : Digest} (hZ : N4c.truthZ4 κ w) (hP : N4c.PubCells4 κ w vk c₁ c₂)
    {a : ℕ} (ha : a < N4c.nAgg κ) : N4c.stOf c₁ c₂ (N4c.aggChild κ a) = leafStmtF (hAe κ a w) (hAn κ a w) := by
  obtain ⟨hb, ht⟩ := cAB_tgt κ ha
  have hh := N4c.holds_of_Z hZ hb ht
  have hmsg : (Block.msgBytes (N4c.bitsB4 w (N4c.cAB κ a))).take 41 = hA κ a w := by
    refine List.ext_getElem (by simp [Block.msgBytes, hA, Stream.streamBytes_length]) fun p h₁ h₂ => ?_
    have hp : p < 41 := by simpa [hA, Stream.streamBytes_length] using h₂
    rw [List.getElem_take, ← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, Block.msgBytes_getD _ (by omega)]
    simp only [hA, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some, Nat.mod_eq_of_lt (show p < 64 by omega)]
  have h0 : (hA κ a w).getD 0 0 = tagLeaf := by
    rw [← hmsg, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by norm_num),
      ← List.getD_eq_getElem?_getD, Block.msgBytes_getD _ (by norm_num), Nat.mul_zero, Nat.add_zero]
    exact (Kinds.hashA_sound (R := F) hh).2
  rw [← stmt_cells hP ha, ← readDigest_digestOf, Kinds.hashA_leafStmt (R := F) hh (by rw [hmsg]; exact hA_eq κ a w h0),
    leafStmtF_eq]


/-! ## `aggChk` -/

theorem mapM_map_some {γ β : Type} (P : ℕ → γ) (f : γ → Option β) (g : ℕ → β) :
    ∀ l : List ℕ, (∀ i ∈ l, f (P i) = some (g i)) → (l.map P).mapM f = some (l.map g)
  | [], _ => rfl
  | i :: l, h => by
    rw [List.map_cons, List.mapM_cons, h i List.mem_cons_self,
      mapM_map_some P f g l fun j hj => h j (List.mem_cons_of_mem _ hj)]
    rfl

/-- **The chaining** of views whose consecutive starts and ends meet. -/
theorem chainOk_range' (V : ℕ → SegView) : ∀ k m, (∀ i, m + 1 ≤ i → i < m + k → (V i).start = (V (i - 1)).h) →
    chainOk ((List.range' m k).map V) = true
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | k + 2, m, h => by
    rw [show List.range' m (k + 2) = m :: List.range' (m + 1) (k + 1) from rfl, List.map_cons,
      show List.range' (m + 1) (k + 1) = (m + 1) :: List.range' (m + 1 + 1) k from rfl, List.map_cons, chainOk,
      ← List.map_cons, show (m + 1) :: List.range' (m + 1 + 1) k = List.range' (m + 1) (k + 1) from rfl,
      chainOk_range' V (k + 1) (m + 1) fun i h1 h2 => h i (by omega) (by omega),
      h (m + 1) le_rfl (by omega), Nat.add_sub_cancel]
    simp

theorem cap_segAt (ι : Kind) : (segAt ι).cap = 2 ^ capE ι := by cases ι <;> rfl

theorem selc_eq (κ : NodeKind) (v : ℕ) (ι : Kind) : selc κ v ι = κ.oneCell + selR v ι := by
  cases ι <;> rfl

/-- **`V_A`'s checks on views indexed by the sub-slots.** -/
theorem aggChecks_of {c e : Digest} {n k : ℕ} {V : ℕ → SegView} (hc : c = leafStmtF e n)
    (hk : 1 ≤ k ∧ k ≤ 4) (hr : ∀ i < k, 1 ≤ (V i).n ∧ (V i).n ≤ (V i).kind.cap)
    (hs : ∑ i ∈ range k, (V i).n = n) (he : (V (k - 1)).h = e)
    (hch : ∀ i, 1 ≤ i → i < k → (V i).start = (V (i - 1)).h) :
    aggChecks c n e ((List.range k).map V) = true := by
  rw [aggChecks]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_map, List.length_range]
  refine ⟨⟨⟨⟨⟨hc, hk⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact decide_eq_true (hr i (List.mem_range.1 hi))
  · rw [List.map_map, lsum_range]; exact hs
  · rw [List.getLast?_map, show (List.range k).getLast? = some (k - 1) by
      rw [List.getLast?_eq_getElem?, List.length_range, List.getElem?_range (by omega)], Option.map_some,
      Option.map_some, he]
  · rw [List.range_eq_range']
    exact chainOk_range' V k 0 fun i h1 h2 => hch i (by omega) (by omega)

section Agg
variable {impl₀ : OpImpl} {base : NodeKind → OpImpl} {pf : Trace → Proof} {κ : NodeKind}
  {vk c₁ c₂ : Digest} {w : Asg}

/-- **The check rows hold** (folded into slot 1's link rows; otherwise the rejecting row). -/
theorem chk_hold (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ a < N4c.nAgg κ, ∀ r ∈ aggRowsC κ a (actW κ a), r.Holds w := by
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hone := one_of_pubCells hP
  have hF := protoFit_of hone hE
  have h1 : 1 < κ.vslots := by cases κ <;> decide
  by_cases h : xOkK κ = true
  · intro a ha r hr
    refine linkRows_hold hF h1 hE r (List.mem_append_right _ ?_)
    rw [extRowsC, if_pos rfl, if_pos h, xRowsK_eq]
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, hr⟩))
  · exfalso
    have := linkRows_hold hF h1 hE (rejR κ)
      (List.mem_append_right _ (by rw [extRowsC, if_pos rfl, if_neg h]; simp))
    simp [rejR, Row.Holds, hone] at this

theorem aggPf_hdr (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) {p : ℕ} (hp : p < 48) :
    byteAt (aggPf pf κ a w) p = (aggHdr (kAct κ a w) (hAn κ a w) (hAe κ a w)).getD p 0 := by
  rw [aggPf, byteAt_mk, List.getD_append _ _ _ _ (by rw [aggHdr_length]; exact hp)]

theorem aggHdr_n (k n : ℕ) (e : Digest) {t : ℕ} (ht : t < 8) : (aggHdr k n e).getD (8 + t) 0 = (enc64 n).getD t 0 := by
  unfold aggHdr
  rw [List.append_assoc, List.append_assoc, List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp [enc64_length]; omega)]
  congr 1; simp; omega

theorem aggHdr_e (k n : ℕ) (e : Digest) {j : ℕ} (hj : j < 32) : (aggHdr k n e).getD (16 + j) 0 = e[j] := by
  unfold aggHdr
  rw [List.append_assoc, List.append_assoc, List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp [enc64_length]; omega)]
  simp [enc64_length, List.getD_eq_getElem?_getD, show 16 + j - 2 - 6 - 8 = j by omega, hj]

theorem rdLE64_aggPf (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) (hl : hAn κ a w < 2 ^ 64) :
    rdLE64 (aggPf pf κ a w) 8 = hAn κ a w := by
  rw [rdLE64, lsum_range]
  conv_rhs => rw [← CompPoly.Bytes.ofListLE_toListLE_of_lt (w := 8) (show hAn κ a w < 256 ^ 8 by simpa using hl),
    ← Snd.enc64_toListLE, ofListLE_sum, enc64_length]
  refine sum_congr rfl fun t ht => ?_
  rw [aggPf_hdr pf κ a w (by have := mem_range.1 ht; omega), aggHdr_n _ _ _ (mem_range.1 ht)]

theorem bytesAt_aggPf (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) :
    bytesAt (aggPf pf κ a w) 16 32 = hAe κ a w :=
  Vector.ext fun j hj => by rw [bytesAt, Vector.getElem_ofFn, aggPf_hdr pf κ a w (by omega), aggHdr_e _ _ _ hj]

/-- **`Gap4R.aggChk` from the node rows** (B4): every aggregate meets `V_A`'s checks against its
statement `c_A`. -/
theorem aggChk_of_rows (hpf : PfHdr pf) (hpv : PfView pf)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ a < N4c.nAgg κ, ∃ vs, (aggSegs (piSizeOf seq4) (N4c.kA (rd4 pf) κ w a)
      ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π).mapM segView = some vs ∧
    aggChecks (N4c.stOf c₁ c₂ (N4c.aggChild κ a)) (rdLE64 ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 8)
      (bytesAt ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 16 32) vs = true := by
  intro a ha
  have hS' := hS
  obtain ⟨hZ, -, hL, hE, hP⟩ := hS'
  have hone := one_of_pubCells hP
  have hF := protoFit_of hone hE
  have hlk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w :=
    fun i hi => linkRows_hold hF (sub_facts κ ha hi).1 hE
  have hK := actK_kAct hone ha hL hlk
  have hPr := act_profile hone ha hL hlk hK
  obtain ⟨hk1, hkm, -⟩ := hK
  have hR := chk_hold hS a ha
  have hP' : ∀ i < κ.maxK, (actW κ a i).ev w = if i < kAct κ a w then 1 else 0 := fun i hi => by
    rw [actW_eq]; exact hPr i hi
  have h4 : κ.maxK ≤ 4 := by cases κ <;> decide
  set k := kAct κ a w with hkdef
  have hsel : ∀ i < k, ∃ ι, SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι := fun i hi => by
    obtain ⟨ι, hι⟩ := selA_sel hone ha hL hlk (actK_kAct hone ha hL hlk) i hi
    rw [protoOf_seg (sub_facts κ ha (by omega : i < κ.maxK)).2.2.1] at hι
    exact ⟨ι, hι⟩
  classical
  let ιf : ℕ → Kind := fun i => if h : i < k then Classical.choose (hsel i h) else .L32
  have hιf : ∀ i (h : i < k), SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) (ιf i) := fun i h => by
    simp only [ιf, dif_pos h]; exact Classical.choose_spec (hsel i h)
  let V : ℕ → SegView := fun i => ⟨segAt (ιf i), dg2 (w (sE κ (N4c.aggChild κ a) i 6)) (w (sE κ (N4c.aggChild κ a) i 7)),
    sh1 (w (sE κ (N4c.aggChild κ a) i 13)) (w (sE κ (N4c.aggChild κ a) i 14)) (w (sE κ (N4c.aggChild κ a) i 15)),
    n8 (w (sE κ (N4c.aggChild κ a) i 15))⟩
  have hπ : ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π = aggPf pf κ a w := by simp only [rd4, sgn4_agg pf κ ha]
  refine ⟨(List.range k).map V, ?_, ?_⟩
  · -- the views
    rw [kA_rd4 pf κ ha, hπ, aggPf, aggSegs_flat _ _ (aggHdr_length _ _ _)
      (fun s hs => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
        exact slotPf_length pf κ _ w) (by simp), List.map_map]
    exact mapM_map_some _ segView V _ fun i hi => view_sub hpf hpv hS ha (List.mem_range.1 hi) (hιf i (List.mem_range.1 hi))
  · -- the checks
    have hl : hAn κ a w < 2 ^ 64 := by rw [hAn_eq, n8_bits]; exact nOfBits_lt _ 64
    have hact : ∀ i < k, (actW κ a i).ev w = 1 := fun i hi => by rw [hP' i (by omega), if_pos hi]
    rw [hπ, rdLE64_aggPf pf κ a w hl, bytesAt_aggPf]
    refine aggChecks_of (stmt_A hZ hP ha) ⟨hk1, by omega⟩ (fun i hi => ?_) ?_ ?_
      (fun i h1 h2 => chain_sub hone hR (by omega) (by omega) (hact i (by omega)))
    · -- the lengths' range
      have hselc : ∀ ι', w (selc κ (N4c.sub κ a i) ι') = if ι' = ιf i then 1 else 0 := fun ι' => by
        have h := (hιf i hi).2 ι'
        have hp := protoOf_seg (sub_facts κ ha (by omega : i < κ.maxK)).2.2.1
        have e := slotAsg_sel κ (N4c.sub κ a i) w ι'
        rw [hp] at e
        simp only [protoP, Lin.ev_cell, e] at h
        rw [selc_eq]; exact h
      have := rng_sub hone hR (by omega : i < κ.maxK) (hact i hi) hselc
      rw [show (V i).kind.cap = 2 ^ capE (ιf i) from cap_segAt _]
      exact this
    · -- the sum
      rw [hAn_eq]
      exact sum_sub hone hR hk1 hkm hP'
    · -- the end
      rw [hAe_eq]
      have hind : (ind κ (actW κ a) (k - 1 + 1)).ev w = 1 := by
        rw [Nat.sub_add_cancel hk1, ind_ev hk1 hkm hPr hk1 hkm, if_pos rfl]
      exact end_sub hone hR (by omega) hind

/-- **`Gap4R` reduces to `imp`** (B4): with the node rows, `PfHdr pf` and `PfView pf`, the slots'
imports alone give S-N2's `Gap4`. -/
theorem gap4_of_rowsI (hpf : PfHdr pf) (hpv : PfView pf)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (himp : ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)) :
    Gap4 impl₀ base pf κ vk c₁ c₂ w :=
  gap4_of_rows pf hpf hS ⟨himp, aggChk_of_rows hpf hpv hS⟩

end Agg

end N4s
end FR

end G6_FRNodeRows4AggChkG

section G6_FRNodeRows4AskStmtS

-- New for `flock-recursive` (PACK-4.4 §1.3 `input`/`stmtOk4`, PK-m7; track IMP): what the statement
-- rows give — `stmtOk4` at every active slot, and the cells of every slot's `input` registers.

/-!
# The statement rows' soundness (PK-m7)

With `StmtN4` (Z truth on the statement blocks, `PubCells4`), the statement rows
(`W4.stmtRows`, folded into `xRowsA`) and the proof decoder's positional facts (`PfHdr`, `PfView`):

* **`stmtOk4_of_rows`**: every active slot meets the statement fact `stmtOk4` at every index its
  selectors may pick (`SlotImp`'s second conjunct, so `SlotImpA`'s third). A segment slot needs no
  row: its `c` *is* `leafStmt` of the bytes `stmtOk4` hashes (`stmtOk_seg`, from the slot's kind byte);
  the previous node needs `hashB1`/`hashB2` tied to its `stmt` field and to `c₁` (`stmtOk_prev`).
* **The `input` registers' cells** (the targets of the `input` alias, PACK §1.3): a segment slot's
  `c` is its `hashA` block's `h_out` (`stmtC_sub`), the previous node's `c` is `c₁`'s public cells
  (`stmtC_prev`), every slot's `vk` its signed child's public `vk` cells (`stmtVk`).
* The block-generic forms of B4's `hA_*` (`hBm_*`, `leaf_blk`): a `hashA` block's output is
  `leafStmt` of the element-aligned fields of its message.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Finset

/-! ## A `hashA` block's message (block-generic B4 `hA_*`) -/

/-- A block's first 41 message bytes. -/
noncomputable def hBm (blk : ℕ) (w : Asg) : List UInt8 :=
  Stream.streamBytes (fun _ => N4c.bitsB4 w blk) 41

/-- Its bytes `1 … 32` (`h`) and its bytes `33 … 40` read little-endian (`n`). -/
noncomputable def hBe (blk : ℕ) (w : Asg) : Digest := Vector.ofFn fun i : Fin 32 => (hBm blk w).getD (1 + i) 0
noncomputable def hBn (blk : ℕ) (w : Asg) : ℕ :=
  ((List.range 8).map fun i => ((hBm blk w).getD (33 + i) 0).toNat * 256 ^ i).sum

theorem hBm_get (blk : ℕ) (w : Asg) {p : ℕ} (hp : p < 41) :
    (hBm blk w).getD p 0 = fb (w (hc blk (4 + p / 16))) (p % 16) := by
  rw [hBm, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
    Option.map_some, Option.getD_some, Nat.mod_eq_of_lt (show p < 64 by omega),
    show Blake2sCircuit.msgBase + 8 * p = 8 * (64 + p) by rw [show Blake2sCircuit.msgBase = 512 from rfl]; ring,
    readByte_hc w _ (by omega),
    show (64 + p) / 16 = 4 + p / 16 by omega]
  exact fb_congr_mod _ (by omega)

theorem hBe_eq (blk : ℕ) (w : Asg) :
    hBe blk w = sh1 (w (hc blk 4)) (w (hc blk 5)) (w (hc blk 6)) := by
  refine Vector.ext fun j hj => ?_
  rw [hBe, Vector.getElem_ofFn, hBm_get blk w (by omega), sh1, Vector.getElem_ofFn, catByte]
  simp only [Fin.val_mk]
  refine (fb_mod _ _).trans ?_
  congr 1
  rcases (by omega : (1 + j) / 16 = 0 ∨ (1 + j) / 16 = 1 ∨ (1 + j) / 16 = 2) with h | h | h <;> rw [h] <;> rfl

theorem hBn_eq (blk : ℕ) (w : Asg) : hBn blk w = n8 (w (hc blk 6)) := by
  rw [hBn, n8, lsum_range]
  refine sum_congr rfl fun t ht => ?_
  have ht := mem_range.1 ht
  rw [hBm_get blk w (by omega), show (33 + t) / 16 = 2 by omega]
  congr 2
  exact fb_congr_mod _ (by omega)

theorem hBm_drop (blk : ℕ) (w : Asg) : (hBm blk w).drop 33 = enc64 (hBn blk w) := by
  have hl : ((hBm blk w).drop 33).length = 8 := by simp [hBm, Stream.streamBytes_length]
  have hn : hBn blk w = CompPoly.Bytes.ofListLE ((hBm blk w).drop 33) := by
    rw [ofListLE_sum, hl, hBn, lsum_range]
    refine sum_congr rfl fun t _ => ?_
    simp [List.getD_eq_getElem?_getD]
  rw [hn, Snd.enc64_toListLE, ← hl, CompPoly.Bytes.toListLE_ofListLE]

theorem hBm_eq (blk : ℕ) (w : Asg) (h0 : (hBm blk w).getD 0 0 = tagLeaf) :
    hBm blk w = tagLeaf :: (hBe blk w).toList ++ enc64 (hBn blk w) := by
  have hl : (hBm blk w).length = 41 := by simp [hBm, Stream.streamBytes_length]
  conv_lhs => rw [← List.take_append_drop 33 (hBm blk w)]
  rw [hBm_drop]
  congr 1
  refine List.ext_getElem (by simp [hl]) fun p h₁ h₂ => ?_
  rw [List.getElem_take, ← List.getD_eq_getElem _ 0]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [h0, List.getElem_cons_zero]
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [List.getElem_cons_succ, Vector.getElem_toList]
    unfold hBe
    rw [Vector.getElem_ofFn]
    congr 1; simp only [Fin.val_mk]; omega

/-- **A `hashA` block outputs `leafStmt` of its message's `h` and `n`** (its `h_out` cells). -/
theorem leaf_blk {κ : NodeKind} {w : Asg} (hZ : N4c.truthZ4 κ w) {blk : ℕ} (hb : blk < κ.blocks)
    (ht : N4c.nodeKind4 κ blk = some Kinds.hashA.target) :
    Read.digestOf w (hc blk 2) (hc blk 3) = leafStmtF (hBe blk w) (hBn blk w) := by
  have hh := N4c.holds_of_Z hZ hb ht
  have hmsg : (Block.msgBytes (N4c.bitsB4 w blk)).take 41 = hBm blk w := by
    refine List.ext_getElem (by simp [Block.msgBytes, hBm, Stream.streamBytes_length]) fun p h₁ h₂ => ?_
    have hp : p < 41 := by simpa [hBm, Stream.streamBytes_length] using h₂
    rw [List.getElem_take, ← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, Block.msgBytes_getD _ (by omega)]
    simp only [hBm, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some, Nat.mod_eq_of_lt (show p < 64 by omega)]
  have h0 : (hBm blk w).getD 0 0 = tagLeaf := by
    rw [← hmsg, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by norm_num),
      ← List.getD_eq_getElem?_getD, Block.msgBytes_getD _ (by norm_num), Nat.mul_zero, Nat.add_zero]
    exact (Kinds.hashA_sound (R := F) hh).2
  rw [← readDigest_digestOf, Kinds.hashA_leafStmt (R := F) hh (by rw [hmsg]; exact hBm_eq blk w h0),
    leafStmtF_eq]

/-! ## The statement blocks -/

/-- **Slot `v`'s statement blocks** are a `hashA`, a `hashB1 tagNode` and a `hashB2` block. -/
theorem stmt_tgt (κ : NodeKind) {v : ℕ} (hv : v < κ.vslots) :
    (N4c.stmtB κ + 3 * v < κ.blocks ∧ N4c.nodeKind4 κ (N4c.stmtB κ + 3 * v) = some Kinds.hashA.target) ∧
    (N4c.stmtB κ + 3 * v + 1 < κ.blocks ∧
      N4c.nodeKind4 κ (N4c.stmtB κ + 3 * v + 1) = some (Kinds.hashB1 RecursionFast.tagNode).target) ∧
    (N4c.stmtB κ + 3 * v + 2 < κ.blocks ∧ N4c.nodeKind4 κ (N4c.stmtB κ + 3 * v + 2) = some Kinds.hashB2.target) := by
  have hm : ∀ iv ∈ N4c.stmtIvs κ, iv ∈ N4c.nodeLayout4 κ := fun iv h => by
    simp only [N4c.nodeLayout4, List.mem_append]; tauto
  have hi : ∀ iv ∈ ([⟨.hashA, N4c.stmtB κ + 3 * v, N4c.stmtB κ + 3 * v + 1, fun _ => some Kinds.hashA.target⟩,
      ⟨.hashB1, N4c.stmtB κ + 3 * v + 1, N4c.stmtB κ + 3 * v + 2, fun _ => some (Kinds.hashB1 RecursionFast.tagNode).target⟩,
      ⟨.hashB2, N4c.stmtB κ + 3 * v + 2, N4c.stmtB κ + 3 * v + 3, fun _ => some Kinds.hashB2.target⟩] : List N4c.TIv),
      iv ∈ N4c.nodeLayout4 κ := fun iv h => hm iv (List.mem_flatMap.2 ⟨v, List.mem_range.2 hv, h⟩)
  have key : ∀ iv ∈ ([⟨.hashA, N4c.stmtB κ + 3 * v, N4c.stmtB κ + 3 * v + 1, fun _ => some Kinds.hashA.target⟩,
      ⟨.hashB1, N4c.stmtB κ + 3 * v + 1, N4c.stmtB κ + 3 * v + 2,
        fun _ => some (Kinds.hashB1 RecursionFast.tagNode).target⟩,
      ⟨.hashB2, N4c.stmtB κ + 3 * v + 2, N4c.stmtB κ + 3 * v + 3, fun _ => some Kinds.hashB2.target⟩] :
      List N4c.TIv), iv.lo < iv.hi → iv.lo < κ.blocks ∧ N4c.nodeKind4 κ iv.lo = iv.tgt 0 := by
    intro iv h hlt
    have hk : iv.mem iv.lo = true := by
      simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq]; omega
    refine ⟨N4c.mem_lt (hi iv h) hk, ?_⟩
    rw [N4c.tgt_of_mem (hi iv h) hk, Nat.sub_self]
  exact ⟨key _ List.mem_cons_self (by simp), key _ (List.mem_cons_of_mem _ List.mem_cons_self) (by simp),
    key _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by simp)⟩

section Stmt
variable {pf : Trace → Proof} {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}

/-- **The statement rows hold** on the node statement (slot 1's node rows, as `chk_hold`). -/
theorem stmtRows_hold (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ r ∈ stmtRows κ (actW κ), r.Holds w := by
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hone := one_of_pubCells hP
  have hF := protoFit_of hone hE
  have h1 : 1 < κ.vslots := by cases κ <;> decide
  by_cases h : xOkK κ = true
  · intro r hr
    refine linkRows_hold hF h1 hE r (List.mem_append_right _ ?_)
    rw [extRowsC, if_pos rfl, if_pos h, xRowsK_eq]
    exact List.mem_append_right _ (List.mem_append_right _ hr)
  · exfalso
    have := linkRows_hold hF h1 hE (rejR κ)
      (List.mem_append_right _ (by rw [extRowsC, if_pos rfl, if_neg h]; simp))
    simp [rejR, Row.Holds, hone] at this

/-- **The public `vk` cells** of signed child `σ` are `vk` (`PubCells4`). -/
theorem stmtVk (hP : N4c.PubCells4 κ w vk c₁ c₂) {σ : ℕ} (hσ : σ < 2) :
    Read.digestOf w (N4c.seedC κ σ 0) (N4c.seedC κ σ 1) = vk := by
  unfold N4c.PubCells4 at hP
  simp only [N4c.cells4, List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.cons_append,
    Node.pubVals, Node.halves, List.cons.injEq] at hP
  rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl
  · exact Snd.digestOf_halves hP.2.1 hP.2.2.1
  · exact Snd.digestOf_halves hP.2.2.2.2.2.1 hP.2.2.2.2.2.2.1

/-- **The previous node's public statement cells** are `c₁` (`PubCells4`). -/
theorem stmtC_prev (hP : N4c.PubCells4 κ w vk c₁ c₂) (hp : κ.hasPrev = true) :
    Read.digestOf w (N4c.seedC κ 0 2) (N4c.seedC κ 0 3) = c₁ := by
  have hs : ∀ h, N4c.stC κ 0 h = N4c.seedC κ 0 (2 + h) := fun h => by
    simp [N4c.stC, N4c.isAgg, hp]
  unfold N4c.PubCells4 at hP
  simp only [N4c.cells4, List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.cons_append,
    Node.pubVals, Node.halves, List.cons.injEq, hs] at hP
  exact Snd.digestOf_halves hP.2.2.2.1 hP.2.2.2.2.1

/-- An active sub-slot's statement rows: its `hashA` message elements are its stream's `13 … 16`. -/
theorem stmt_cells_sub (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) {a : ℕ} (ha : a < N4c.nAgg κ)
    {i : ℕ} (hi : i < kAct κ a w) {e : ℕ} (he : e < 4) :
    w (hc (N4c.stmtB κ + 3 * N4c.sub κ a i) (4 + e)) = w (sE κ (N4c.aggChild κ a) i (13 + e)) := by
  obtain ⟨-, -, hL, hE, hP⟩ := id hS
  have hone := one_of_pubCells hP
  have hF := protoFit_of hone hE
  have hlk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w :=
    fun i hi => linkRows_hold hF (sub_facts κ ha hi).1 hE
  have hi' : i < κ.maxK := lt_of_lt_of_le hi (kAct_le κ a w)
  have hact : (actW κ a i).ev w = 1 := by
    rw [actW_eq, act_profile hone ha hL hlk (actK_kAct hone ha hL hlk) i hi', if_pos hi]
  refine eqRowG_holds hact (stmtRows_hold hS _ (List.mem_append_left _ (List.mem_append_left _ ?_)))
  exact List.mem_flatMap.2 ⟨a, List.mem_range.2 ha,
    List.mem_flatMap.2 ⟨i, List.mem_range.2 hi', List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩⟩⟩

/-- **An active sub-slot's `c` is its `hashA` block's `h_out`** (the cells of its `input c`). -/
theorem stmtC_sub (hpf : PfHdr pf) (hpv : PfView pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    {a : ℕ} (ha : a < N4c.nAgg κ) {i : ℕ} (hi : i < kAct κ a w) {ι : Kind}
    (hι : SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι) :
    (N4c.slotIn (rd4 pf) κ vk c₁ w (N4c.sub κ a i)).c =
      Read.digestOf w (hc (N4c.stmtB κ + 3 * N4c.sub κ a i) 2) (hc (N4c.stmtB κ + 3 * N4c.sub κ a i) 3) := by
  have hi' : i < κ.maxK := lt_of_lt_of_le hi (kAct_le κ a w)
  obtain ⟨hv, -, hpv', -⟩ := sub_facts κ ha hi'
  have hnp : ¬ (κ.hasPrev = true ∧ N4c.sub κ a i = 0) := fun ⟨h1, h2⟩ => by
    simp [isPrevSlot, h1, h2] at hpv'
  have hc := fun e (he : e < 4) => stmt_cells_sub hS ha hi he
  obtain ⟨hb, ht⟩ := (stmt_tgt κ hv).1
  rw [N4c.slotIn, if_neg hnp, view_sub hpf hpv hS ha hi hι]
  simp only [Option.map_some, Option.getD_some, segC]
  rw [leaf_blk hS.1 hb ht, hBe_eq, hBn_eq, hc 0 (by norm_num), hc 1 (by norm_num),
    hc 2 (by norm_num)]

/-! ## The statement fact `stmtOk4` -/

theorem byteAt_toList (q : ByteArray) (k : ℕ) : byteAt q k = q.data.toList.getD k 0 := by
  conv_lhs => rw [show q = ⟨q.data.toList.toArray⟩ from rfl]
  exact byteAt_mk _ _

/-- Byte `j < n` of `π.extract a (a + n)` is byte `a + j` of `π`. -/
theorem byteAt_extract (π : ByteArray) (a n : ℕ) {j : ℕ} (hj : j < n) :
    byteAt (π.extract a (a + n)) j = byteAt π (a + j) := by
  rw [byteAt_toList, byteAt_toList, ByteArray.data_extract, Array.toList_extract, List.extract,
    Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, if_pos hj, List.getElem?_drop]

/-- A message byte of an H block is a byte of its message element (A.7's pack). -/
theorem msg_byte (w : Asg) (blk : ℕ) {p : ℕ} (hp : p < 64) :
    (Block.msgBytes (N4c.bitsB4 w blk)).getD p 0 = fb (w (hc blk (4 + p / 16))) (p % 16) := by
  rw [Block.msgBytes_getD _ hp, show Blake2sCircuit.msgBase + 8 * p = 8 * (64 + p) by rw [show Blake2sCircuit.msgBase = 512 from rfl]; ring,
    readByte_hc w _ (by omega), show (64 + p) / 16 = 4 + p / 16 by omega]
  exact fb_congr_mod _ (by omega)

theorem vec_getD {n : ℕ} (v : Vector UInt8 n) {i : ℕ} (hi : i < n) : v.toList.getD i 0 = v[i] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), Vector.getElem_toList]

/-- The node statement's message `tag ‖ s[1, 33) ‖ s[33, 65)` read byte-wise (the vectors are
generalised away: `whnf` on a concrete `bytesAt` evaluates it). -/
theorem nodeMsg_getD (t : UInt8) (s : ByteArray) {p : ℕ} (h1 : 1 ≤ p) (h2 : p < 65) :
    (t :: (bytesAt s 1 32).toList ++ (bytesAt s 33 32).toList).getD p 0 = byteAt s p := by
  have gX : ∀ i < 32, (bytesAt s 1 32).toList.getD i 0 = byteAt s (1 + i) := fun i hi => by
    rw [vec_getD _ hi, bytesAt, Vector.getElem_ofFn]
  have gY : ∀ i < 32, (bytesAt s 33 32).toList.getD i 0 = byteAt s (33 + i) := fun i hi => by
    rw [vec_getD _ hi, bytesAt, Vector.getElem_ofFn]
  have hX : (bytesAt s 1 32).toList.length = 32 := Vector.length_toList
  generalize (bytesAt s 1 32).toList = X at gX hX
  generalize (bytesAt s 33 32).toList = Y at gY
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [List.cons_append, List.getD_cons_succ]
  rcases Nat.lt_or_ge q 32 with hq | hq
  · rw [List.getD_append _ _ _ _ (by omega), gX q hq, Nat.add_comm 1 q]
  · rw [List.getD_append_right _ _ _ _ (by omega), hX, gY _ (by omega)]
    congr 1; omega

theorem nodeMsg_length (t : UInt8) (s : ByteArray) :
    (t :: (bytesAt s 1 32).toList ++ (bytesAt s 33 32).toList).length = 65 := by
  simp only [List.length_append, List.length_cons, Vector.length_toList]

/-- **The previous node's `stmt` field** (proof bytes `48 … 175`) is its stream's elements `13 … 20`. -/
theorem stmtByte_prev (hpv : PfView pf) (hp : κ.hasPrev = true) {j : ℕ} (hj : j < 128) :
    byteAt ((rd4 pf).slotπ κ 0 w) (48 + j) = fb (w (sE κ 0 0 (13 + j / 16))) (j % 16) := by
  set B := N4c.chainBytes4 κ 0 0 w
  obtain ⟨rest, hr⟩ := itemsOf_seq4_two
  have htr : slotTr4 κ 0 w = Read.entryAt B (1 + 0 * N4c.strideB) .seed ::
      Read.entryAt B (1 + 0 * N4c.strideB + 159) (.absorb 128) ::
        Read.readItems B (1 + 0 * N4c.strideB + 159 + 208) rest := by
    simp only [slotTr4, isPrevSlot, hp, Bool.true_and, beq_self_eq_true, if_true]
    rw [segTr, hr]; rfl
  obtain ⟨-, hv2⟩ := hpv (Read.entryAt B (1 + 0 * N4c.strideB) .seed)
    (Read.entryAt B (1 + 0 * N4c.strideB + 159) (.absorb 128)) (Read.readItems B (1 + 0 * N4c.strideB + 159 + 208) rest)
  have hps : 176 ≤ piSizeOf seq4 := by rw [piSizeOf_seq4]; norm_num
  have hk0 : N4c.isAgg κ 0 = true → 1 ≤ 0 := fun h => by simp [isAgg_zero hp] at h
  show byteAt (⟨(slotPf pf κ 0 w).toArray⟩ : Proof) _ = _
  rw [byteAt_slotPfP pf κ 0 w (by omega), htr, hv2 j hj, entry_byte _ _ _ (by simp [Item.qlen]; omega)]
  have h := seg0_elem (κ := κ) (σ := 0) (k := 0) w hk0 (e := 13 + j / 16) (r := j % 16) (Nat.mod_lt _ (by norm_num))
    (by simp only [N4c.segB]; omega)
  rw [show 1 + 0 * N4c.strideB + 159 + 8 + (40 + j) = 16 * (13 + j / 16) + j % 16 by omega, h,
    fb_eq _ (Nat.mod_lt _ (by norm_num))]
  simp [sE]

/-- **The previous node's statement fact**: `nodeStmt` of its `stmt` field is `c₁` (`hashB1`/`hashB2`
tied to the field and to `c₁`'s public cells by the statement rows). -/
theorem stmtOk_prev (hpv : PfView pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hp : κ.hasPrev = true) (ι : Kind) :
    stmtOk4 seq4 (kindP 0 ι) (N4c.slotIn (rd4 pf) κ vk c₁ w 0) = true := by
  obtain ⟨hZ, -, -, -, hP⟩ := id hS
  have hone := one_of_pubCells hP
  obtain ⟨-, ⟨hb1, ht1⟩, ⟨hb2, ht2⟩⟩ := stmt_tgt κ (vslots_pos κ)
  simp only [Nat.mul_zero, Nat.add_zero] at hb1 ht1 hb2 ht2
  set B1 := N4c.stmtB κ + 1
  set B2 := N4c.stmtB κ + 2
  have hR : ∀ r ∈ stmtRowsP κ, r.Holds w := fun r hr =>
    stmtRows_hold hS r (List.mem_append_left _ (List.mem_append_right _ hr))
  rw [stmtRowsP, if_pos hp] at hR
  have e1 : ∀ e < 4, w (hc B1 (4 + e)) = w (sE κ 0 0 (13 + e)) := fun e he => eqRow_holds hone
    (hR _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩)))))
  have e2 : ∀ e < 4, w (hc B2 (4 + e)) = w (sE κ 0 0 (17 + e)) := fun e he => eqRow_holds hone
    (hR _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩)))))
  have e3 : ∀ h < 2, w (hc B2 h) = w (hc B1 (2 + h)) := fun h hh => eqRow_holds hone
    (hR _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩))))
  have e4 : ∀ h < 2, w (hc B2 (2 + h)) = w (N4c.seedC κ 0 (2 + h)) := fun h hh => eqRow_holds hone
    (hR _ (List.mem_append_right _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩)))
  have hh1 := N4c.holds_of_Z hZ hb1 ht1
  have hh2 := N4c.holds_of_Z hZ hb2 ht2
  have hl : ∀ j < 256, N4c.bitsB4 w B2 (ProductCircuit.pos j) = N4c.bitsB4 w B1 (ProductCircuit.pos (256 + j)) :=
    fun j hj => by
      rw [bitsB4_bit w _ (by omega), bitsB4_bit w _ (by omega)]
      have h := e3 (j / 128) (by omega)
      simp only [hc] at h
      rw [show (256 + j) / 128 = 2 + j / 128 by omega, ← h]
      simp only [W4.bitN, show (256 + j) % 128 = j % 128 by omega]
  set π := (rd4 pf).slotπ κ 0 w
  set s := π.extract 48 (48 + 128)
  have hsz : ∀ j < 128, byteAt s j = fb (w (sE κ 0 0 (13 + j / 16))) (j % 16) := fun j hj => by
    rw [byteAt_extract _ _ _ hj, stmtByte_prev hpv hp hj]
  have hm : Block.msgBytes (N4c.bitsB4 w B1) ++ (Block.msgBytes (N4c.bitsB4 w B2)).take 1 =
      RecursionFast.tagNode :: (bytesAt s 1 32).toList ++ (bytesAt s 33 32).toList := by
    have hl1 : (Block.msgBytes (N4c.bitsB4 w B1)).length = 64 := by simp [Block.msgBytes]
    have hl2 : (Block.msgBytes (N4c.bitsB4 w B2)).length = 64 := by simp [Block.msgBytes]
    refine List.ext_getElem (by rw [nodeMsg_length, List.length_append, hl1, List.length_take, hl2]; rfl)
      fun p h₁ h₂ => ?_
    have hp65 : p < 65 := by rw [nodeMsg_length] at h₂; exact h₂
    rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [List.getD_append _ _ _ _ (by rw [hl1]; norm_num), List.cons_append, List.getD_cons_zero,
        ← (Kinds.hashB_sound (R := F) hh1 hh2 hl).2, Block.msgBytes_getD _ (by norm_num), Nat.mul_zero,
        Nat.add_zero]
    rw [nodeMsg_getD _ _ hp0 hp65, hsz _ (by omega)]
    rcases Nat.lt_or_ge p 64 with hp64 | hp64
    · rw [List.getD_append _ _ _ _ (by rw [hl1]; exact hp64), msg_byte w _ hp64, e1 _ (by omega)]
    · obtain rfl : p = 64 := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl1]), hl1, Nat.sub_self, List.getD_eq_getElem?_getD,
        List.getElem?_take, if_pos (by norm_num), ← List.getD_eq_getElem?_getD, msg_byte w _ (by norm_num),
        e2 0 (by norm_num)]
  have hout : Read.digestOf w (N4c.seedC κ 0 2) (N4c.seedC κ 0 3) = nodeStmt (bytesAt s 1 32) (bytesAt s 33 32) := by
    have e40 := e4 0 (by norm_num)
    have e41 := e4 1 (by norm_num)
    norm_num at e40 e41
    rw [show Read.digestOf w (N4c.seedC κ 0 2) (N4c.seedC κ 0 3) = Read.digestOf w (hc B2 2) (hc B2 3) by
      unfold Read.digestOf; rw [e40, e41], ← readDigest_digestOf,
      Kinds.hashB_nodeStmt (R := F) hh1 hh2 hl hm]
  rw [N4c.slotIn, if_pos ⟨hp, rfl⟩, kindP, if_pos rfl]
  simp only [stmtOk4, decide_eq_true_eq, KindP.ofNode, stmtDigest, stmtBytes4, Snd.R4.stmtOff4]
  rw [nodeStmtF_eq, ← hout, stmtC_prev hP hp]

theorem data_getD (s : ByteArray) (k : ℕ) : s.data.getD k 0 = byteAt s k := by
  rw [byteAt_toList, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **A segment's statement fact holds by the reader's definition**: once its byte 0 is a segment
kind's (its view exists), its `c` is `leafStmt` of exactly the bytes `stmtOk4` hashes. -/
theorem stmtOk_seg (π : Proof) {σ : SegKind} (hb : byteAt π 0 = σ.byte) (σ' : SegKind) (vk : Digest) :
    stmtOk4 seq4 (.ofSeg σ') ⟨vk, ((segView π).map segC).getD 0, π⟩ = true := by
  simp only [stmtOk4, decide_eq_true_eq, KindP.ofSeg, stmtDigest, stmtBytes4, Snd.R4.stmtOff4, segView, hb,
    SegKind.ofByte?_byte, Option.map_some, Option.getD_some, segC]
  refine congrArg₂ leafStmtF ?_ ?_
  · refine Vector.ext fun j hj => ?_
    rw [bytesAt, bytesAt, Vector.getElem_ofFn, Vector.getElem_ofFn, byteAt_extract _ _ _ (by omega)]
    congr 1; omega
  · rw [rdLE64]
    refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    have hi := List.mem_range.1 hi
    rw [data_getD, byteAt_extract _ _ _ (by omega)]
    congr 3; omega

/-- **`stmtOk4` at every active slot and selectable index** (`SlotImp`'s second conjunct): the
previous node's from the statement rows (`stmtOk_prev`), a segment's from its kind byte
(`kindS_of_rows`, `stmtOk_seg`). -/
theorem stmtOk4_of_rows (hpf : PfHdr pf) (hpv : PfView pf)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      stmtOk4 seq4 (kindP (protoOf κ v) ι) (N4c.slotIn (rd4 pf) κ vk c₁ w v) = true := by
  rintro v (⟨hp, rfl⟩ | ⟨a, ha, i, hi, rfl⟩) ι hι
  · rw [protoOf_zero hp]; exact stmtOk_prev hpv hS hp ι
  · rw [kA_rd4 pf κ ha] at hi
    have hi' : i < κ.maxK := lt_of_lt_of_le hi (kAct_le κ a w)
    obtain ⟨-, -, hpv', -⟩ := sub_facts κ ha hi'
    have hnp : ¬ (κ.hasPrev = true ∧ N4c.sub κ a i = 0) := fun ⟨h1, h2⟩ => by
      simp [isPrevSlot, h1, h2] at hpv'
    rw [protoOf_seg hpv'] at hι ⊢
    have hb := kindS_of_rows pf hpf hS a ha i hi ι hι
    rw [N4c.slotIn, if_neg hnp, kindP, if_neg one_ne_zero]
    exact stmtOk_seg _ hb _ vk

end Stmt

end N4s
end FR

end G6_FRNodeRows4AskStmtS
