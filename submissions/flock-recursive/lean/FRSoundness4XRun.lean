-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9, A.10, B-12; track R4i): X4's residual 2
-- (`RunFacts4`) from the program layer, at the concrete ops.
import FRSoundness4R4W0R
import FRSoundness4R4FrCtrlB
import FRSoundness4R4ColsCtrl
import FRSoundness4R4Stmt
import FRSoundness4XLaws

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
  · exact not_rejFinE4_node NI4F.srcE4 NI4F.srcL4 (NI4F.implN4F_hM _ ν) (NI4F.implN4F_hL _ ν) h L h4
  · exact not_rejRS4_node hZ hLS hST hSM hSW hLW h L h5

/-! ## `AcceptTail` from an accepted run, with the run's entries -/

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
  have hW := wV4_of_fields hF hk (finTabs4_seg σ _) (ptIx_seg4 σ _ _) (cells := N4c.cells4)
    (fun ν => (N4c.hcells4P4b ν).2) rfl rfl (show seq4.mStar - 7 = 25 by rw [seq4_mStar]) (rsWeight_segC fin lRows κs₀ σ)
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
  have hW := wV4_of_fields hF hk (finTabs4_node ν _ _) (ptIx_node4 ν _ _ _) (cells := N4c.cells4)
    (fun ν => (N4c.hcells4P4b ν).2) rfl rfl (show seq4.mStar - 7 = 25 by rw [seq4_mStar]) (rsWeight_nodeC fin lRows κs₀ ν)
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

/-- **`RunFacts4.node` at the concrete node ops** (INT-9's `implN4F`, `cells4`). -/
theorem runFacts4_node_C (vk : Digest) :
    ∀ κ L c π, ¬ Bad L → kindOf4 π = .node κ →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ j, T4.AcceptTail RejFX W0X c0X L j ∧ NodeLog κ vk c π (entriesOf L (pathOf L j)) := by
  intro κ L c π hb hk hrun
  obtain ⟨hrun', hst⟩ := runStmt_acc hrun
  obtain ⟨tr, y, j, hS, hsem, hes, hT⟩ :=
    acceptRun4_node fin lRows κs₀ κ (inp := ⟨vk, c, π⟩) hb (piSize_node4 hk) hrun'
  exact ⟨j, hT, hes ▸ nodeLog4 hS hsem hst⟩

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
