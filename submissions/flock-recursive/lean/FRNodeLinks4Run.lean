-- G6: this module also holds the former modules `FRNodeLinks4` (one section each, in import order).
import FRNodeRows4AskStmtS
import FRXPf4

section G6_FRNodeLinks4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.3 `node_sound`, B-13; track S-L4): residual
-- `hL` of `ks_rev4H`/`Resid4H` (the node links) from the circuit residual `hRes` and the run facts.
-- 3.x analogue: `FRNodeSoundA.rel_readWit` with S-N1's `RunLink`.

/-!
# The node links `hL` from the circuit residual

`ks_rev4H` asks, for every accepted in-domain node run on a good log, a transcript `es` with the
decoder's links `D.Links κ L es π c` and **`Rel (S.acc vk) c (D.readW κ L es)`**: the witness the
decoder reads is a node witness (`hL`). This module proves it from the circuit residual `hRes`
(`StmtN4 → NodeResid4`) and the run, for any decoder `D` that meets the reader interface below.

* **`RunLink4`** (S-N1's `RunLink` at revision 4.1): the run's trace `tr`, inside the log, whose
  entries are the chain `j`'s, with `SkRun4` and the statement fact.
* **`nodeRunL4`** (`nodeRun_X` with the chain kept): an accepted node run on a good log has a chain
  `j` with `RunLink4` and `AcceptTail`, and `StmtN4` holds on **`f⁽⁰⁾ = T4.fF (.node κ) L es`** of
  that chain `es`, at the statement digests `stL es 0`, `stL es 1` (with `c = nodeStmt …`).
* **`ReadIface4 D rd`**: what the decoder `D` must meet against the circuit's reader `rd`.
  - `links`: on the run's chain (`RunLink4`, `AcceptTail`, a good log, the domain), `D.Links` holds.
  - `readW`: on a chain whose `f⁽⁰⁾` carries the public cells (`PubCells4 κ w vk c₁ c₂`), the
    decoder's witness is `.node c₁ c₂ (rd.sgn κ 0 w) (rd.sgn κ 1 w)` with `w = T4.fF (.node κ) L es`.
* **`hL_of_res`**: `ReadIface4 D rd` and `hRes` at `rd` give `hL` (through `node_sound4'`).
* **`resid4H_of_res`**: `Resid4H` from the slot interface, `hRes` and `ReadIface4`.

Everything is parametric in the reader `rd` (S-N2's `rd4 pf`, or a reader with another signature
read) and in the decoder `D` (S-H4's `nd`): the proof format enters only through `rd`'s `pf` and
`D`'s `readW`.
-/

namespace FR.Snd.L4
open RecursionFast Rev4 X4 R4 FR.X.X4

/-! ## The run's chain -/

section Run
variable (fin : Finals) (lRows : List Circ.Row) (κs₀ : F)

/-- The node ops of the submission (INT-9's `implN4F` over 3.x's `implC`). -/
noncomputable abbrev implNC (ν : NodeKind) : OpImpl := NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν

/-- **The run's link** (S-N1's `RunLink` at revision 4.1): an accepting trace `tr` of the node
program, inside `L`, whose Fiat–Shamir entries are the chain `j`'s, and the statement fact. -/
def RunLink4 (κ : NodeKind) (vk c : Digest) (π : Proof) (L : Log) (j : ℕ) : Prop :=
  ∃ tr y, SkRun4 (implNC fin lRows κs₀ κ) (.ofNode κ) ⟨vk, c, π⟩ tr y ∧
    semIR (implNC fin lRows κs₀ κ) (gen4 seq4 (.ofNode κ) (finOps4 (nodeFinP κ (N4c.cells4 κ))))
      ⟨vk, c, π⟩ tr = some true ∧
    (∀ e ∈ tr, e ∈ L) ∧ G.IsChain L j ∧ entriesOf L (pathOf L j) = fsOf tr (itemsOf seq4) ∧
    stmtOk4 seq4 (.ofNode κ) ⟨vk, c, π⟩ = true

/-- **An accepted node run's chain is an `AcceptTail`, with its link** (`acceptRun4_node`, keeping
`runLog_chain4`'s trace inclusion and chain). -/
theorem acceptRunL4_node (ν : NodeKind) {vk c : Digest} {π : Proof} {L : Log} (hb : ¬ Bad L)
    (hk : kindOf4 π = .node ν)
    (hrun : (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 ν vk c π).runLog L =
      some true) :
    ∃ j, RunLink4 fin lRows κs₀ ν vk c π L j ∧ T4.AcceptTail RejFX W0X c0X L j := by
  obtain ⟨hrun', hst⟩ := runStmt_acc hrun
  have hπ : π.size = piSizeOf seq4 := piSize_node4 hk
  have hrun'' : (runIR (implNC fin lRows κs₀ ν) (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν (N4c.cells4 ν))))
      ⟨vk, c, π⟩).runLog L = some true := hrun'
  obtain ⟨tr, hsem, hin, j, hci, hes, hlen⟩ :=
    runLog_chain4 (implNC fin lRows κs₀ ν) (.ofNode ν) (finOps4 (nodeFinP ν (N4c.cells4 ν))) hb hπ hrun''
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν (N4c.cells4 ν)) hsem
  have hkC := kindOfC_acc_node hsem
  have hT : FinTabs4 (nodeFinP ν (N4c.cells4 ν)) (KindP.ofNode ν).tix (kindOfC (fsOf tr (itemsOf seq4))) := by
    rw [hkC]; exact finTabs4_node ν _ _
  have hW := wV4_of_fields hF hkC (finTabs4_node ν _ _) (ptIx_node4 ν _ _ _) (cells := X4.cellsX)
    hcellsX rfl rfl (by cases ν <;> rfl) (show seq4.mStar - 7 = 25 by rw [seq4_mStar])
    (rsWeight_nodeC fin lRows κs₀ ν) (tensorW_nodeC fin lRows κs₀ ν) hb hin (dm_node4 hF.sk)
  have hFR := finRest4_full (phiRS_nodeF fin lRows κs₀ ν) (tensorW_nodeC fin lRows κs₀ ν) hF hT
    (dm_node4 hF.sk) hb hin hπ hW
  obtain ⟨hrnd, hrndPf⟩ := rounds_of_run4 hF.sk
  refine ⟨j, ⟨tr, y, hF.sk, hsem, hin, hci, hes, hst⟩,
    acceptTail4_of_finLog (y := yv4 (KindP.ofNode ν) (#[] ++ y.1.toArray)) hb hci hlen
      (hes ▸ not_rejFX_node fin lRows κs₀ hsem L) ?_⟩
  rw [hes]
  exact ⟨hrnd, hrndPf, hFR.start, hFR.cols, hFR.link, hFR.pf0, hFR.enc, hFR.fin, hFR.cap⟩

/-- `f⁽⁰⁾` of a chain is that of its three-entry prefix (`src4.fz_same`). -/
theorem fF_take3 {κ : NodeKind} {L es : Log} (hlen : 3 ≤ es.length) (hk : kindOfC (es.take 3) = .node κ) :
    src4.fz L (es.take 3) = T4.fF (.node κ) L es := by
  have h := src4.fz_same (src4.ofAgree L (agree_take3 hlen).symm) (le_refl 3)
  have hk' : kindOfC es = .node κ :=
    (kindOfC_congr ((agree_take3 hlen).mono (by norm_num))).symm.trans hk
  rw [← h]
  show T4.fF (kindOfC es) L es = _
  rw [hk']

/-- **`nodeRun_X` with the chain kept**: an accepted node run on a good log has a chain `j` with
`RunLink4` and `AcceptTail`, and its statement `StmtN4` holds on that chain's `f⁽⁰⁾` at the
statement digests `stL es 0`, `stL es 1`, with `c = nodeStmt (stL es 0) (stL es 1)` and `vkOf π = vk`. -/
theorem nodeRunL4 (vk : Digest) {κ : NodeKind} {L : Log} {c : Digest} {π : Proof}
    (hG : GoodX P4f.DFhi L) (hk : kindOf4 π = .node κ)
    (hrun : (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L =
      some true) :
    ∃ j, RunLink4 fin lRows κs₀ κ vk c π L j ∧ T4.AcceptTail RejFX W0X c0X L j ∧
      X.vkOf π = vk ∧
      c = nodeStmt (stL (entriesOf L (pathOf L j)) 0) (stL (entriesOf L (pathOf L j)) 1) ∧
      N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk (stL (entriesOf L (pathOf L j)) 0)
        (stL (entriesOf L (pathOf L j)) 1) (T4.fF (.node κ) L (entriesOf L (pathOf L j))) := by
  obtain ⟨hb, -, -⟩ := T4.muT_lt_one hG.2
  obtain ⟨j, hR, hT⟩ := acceptRunL4_node fin lRows κs₀ κ hb hk hrun
  obtain ⟨tr, y, hS, hsem, -, -, hes, hst⟩ := id hR
  have hNL : NodeLog κ vk c π (entriesOf L (pathOf L j)) := hes ▸ nodeLog4 hS hsem hst
  obtain ⟨hkC, hvk, hvkL, hc⟩ := hNL
  obtain ⟨hlen, hSt⟩ := stmt4_of_tail P4f.frontHi_X hG hT
  set es := entriesOf L (pathOf L j)
  have hA := agree_take3 hlen
  have hk3 : kindOfC (es.take 3) = .node κ := (kindOfC_congr (hA.mono (by norm_num))).trans hkC
  rw [P4a.stmt4_node_iff hk3] at hSt
  have hp : pvL (es.take 3) = (vk, stL es 0, stL es 1) := by
    simp only [pvL, vkL, stL, hA 0 (by norm_num), msgAt_congr hA (by norm_num : 1 < 3)]
    rw [← hvkL]; rfl
  rw [hp, fF_take3 hlen hk3] at hSt
  exact ⟨j, hR, hT, hvk, hc, hSt⟩

/-- **`nodeRunL4` with the reserve** (revision 4.4.2; RSV-S3 §5.5): on the same chain, the node's
statement holds with the reserve, `StmtN4R`, at the log's own child claim `rsvL` (`PubCellsR4` from
RS0's `Pub` and `truthChildV` from E1's entry doom, both refuted on the accepted prefix,
`X4.rsv_of_tail`; the two zero outputs from the run, `R4.rsvZero4`). As `X4.nodeRunR_X`, keeping
the chain. -/
theorem nodeRunRL4 (vk : Digest) {κ : NodeKind} {L : Log} {c : Digest} {π : Proof}
    (hG : GoodX P4f.DFhi L) (hk : kindOf4 π = .node κ)
    (hrun : (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L =
      some true) :
    ∃ j, RunLink4 fin lRows κs₀ κ vk c π L j ∧ T4.AcceptTail RejFX W0X c0X L j ∧
      X.vkOf π = vk ∧
      c = nodeStmt (stL (entriesOf L (pathOf L j)) 0) (stL (entriesOf L (pathOf L j)) 1) ∧
      N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk (stL (entriesOf L (pathOf L j)) 0)
        (stL (entriesOf L (pathOf L j)) 1) (T4.fF (.node κ) L (entriesOf L (pathOf L j)))
        (Snd.P4b.rsvL (.node κ) (entriesOf L (pathOf L j))) := by
  obtain ⟨j, hR, hT, hvk, hc, hS⟩ := nodeRunL4 fin lRows κs₀ vk hG hk hrun
  refine ⟨j, hR, hT, hvk, hc, hS, ?_⟩
  obtain ⟨tr, y, -, hsem, -, -, hes, -⟩ := hR
  have hkC : kindOfC (entriesOf L (pathOf L j)) = .node κ := hes ▸ kindOfC_acc_node hsem
  obtain ⟨htc, hpub⟩ := X4.rsv_of_tail hG hT hkC
  obtain ⟨h58, h59⟩ := R4.rsvZero4 hsem
  rw [← hes] at h58 h59
  have hlen : 327 ≤ (entriesOf L (pathOf L j)).length := by
    have := hT.len; rw [T4.capPh_pos.2.2.2] at this; omega
  generalize entriesOf L (pathOf L j) = es at hlen htc hpub hkC h58 h59 ⊢
  have hA' := X4.agree_takeN (es := es) hlen
  have hlen3 : 3 ≤ es.length := by omega
  have hA := agree_take3 hlen3
  have hk3 : kindOfC (es.take 3) = .node κ := (kindOfC_congr (hA.mono (by norm_num))).trans hkC
  have hk327 : kindOfC (es.take 327) = .node κ := (kindOfC_congr (hA'.mono (by norm_num))).trans hkC
  have h33 : Agree (es.take 3) (es.take 327) 3 := fun p hp => (hA p hp).trans (hA' p (by omega)).symm
  have hfz : src4.fz L (es.take 3) = src4.fz L (es.take 327) := src4.fz_same (src4.ofAgree L h33) le_rfl
  refine ⟨?_, N4c.truthChildV_rsvL _ κ htc h58 h59⟩
  unfold N4c.PubCellsR4
  rw [← fF_take3 hlen3 hk3, hfz, hpub κ hk327, Snd.P4b.rsvL_congr hA' (by norm_num)]

end Run

/-! ## The decoder's interface and `hL` -/

/-- **The decoder's read law** against the circuit's reader `rd` (S-H4's side of `hL`): on a chain
whose `f⁽⁰⁾ = T4.fF (.node κ) L es` meets the node's statement at `(vk, c₁, c₂)`, the decoder's
witness is the node witness of `c₁`, `c₂` and `rd`'s two signed children read off `f⁽⁰⁾`. -/
def ReadW4 (readW : NodeKind → Log → Log → Wit) (rd : N4c.Read4) (vk : Digest) : Prop :=
  ∀ κ L es c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ (T4.fF (.node κ) L es) →
    readW κ L es = .node c₁ c₂ (rd.sgn κ 0 (T4.fF (.node κ) L es)) (rd.sgn κ 1 (T4.fF (.node κ) L es))

section Links
variable (fin : Finals) (lRows : List Circ.Row) (κs₀ : F)

/-- **What the decoder `D` must meet against the reader `rd`** for `hL`:
* `links`: on the accepted run's chain (`RunLink4`, `AcceptTail`, a good log, the domain), the
  decoder's links hold;
* `readW`: the read law `ReadW4`. -/
structure ReadIface4 {nd : X.XIR} (D : NodeDec4 nd) (rd : N4c.Read4) (vk : Digest) : Prop where
  links : ∀ κ L c π j, GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    RunLink4 fin lRows κs₀ κ vk c π L j → T4.AcceptTail RejFX W0X c0X L j →
    D.Links κ L (entriesOf L (pathOf L j)) π c
  readW : ReadW4 D.readW rd vk

/-- **`hL` from the circuit residual** (3.x's `rel_readWit` at revision 4.1): an accepted node run
on a good log in the domain has the chain `es` of its run, on which the decoder's links hold
(`ReadIface4.links`), and the decoder's witness on it is the reader's (`ReadIface4.readW`), which
`node_sound4'` proves a witness of the relation from `StmtN4` (`nodeRunL4`) and the residual
`hRes`. Parametric in the reader `rd` and the decoder `D`. -/
theorem hL_of_res (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (D : NodeDec4 nd)
    (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : ReadIface4 fin lRows κs₀ D rd vk) :
    ∀ κ L c π, GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es) := by
  intro κ L c π hG hk hdom hrun
  obtain ⟨j, hR, hT, -, hc, hS⟩ := nodeRunL4 fin lRows κs₀ vk hG hk hrun
  refine ⟨_, hD.links κ L c π j hG hk hdom hR hT, ?_⟩
  have hS' : N4c.StmtN4 κ (I.lrows κ) (I.irows κ) vk (stL (entriesOf L (pathOf L j)) 0)
      (stL (entriesOf L (pathOf L j)) 1) (T4.fF (.node κ) L (entriesOf L (pathOf L j))) := by
    rw [hI.1, hI.2]; exact hS
  rw [hD.readW κ L _ _ _ hS, acc_eqC4 _ _ _ S hV hq, hc]
  exact (N4c.node_sound4' hS' (hRes κ _ _ _ hS)).1

/-- **`hL_of_res` over `StmtN4R`** (revision 4.4.2): the residual `hRes` may use the reserve's cells
and the true child claim, which the accepted run gives on its chain (`nodeRunRL4`). -/
theorem hL_of_resR (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (D : NodeDec4 nd)
    (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : ReadIface4 fin lRows κs₀ D rd vk) :
    ∀ κ L c π, GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es) := by
  intro κ L c π hG hk hdom hrun
  obtain ⟨j, hR, hT, -, hc, hS⟩ := nodeRunRL4 fin lRows κs₀ vk hG hk hrun
  refine ⟨_, hD.links κ L c π j hG hk hdom hR hT, ?_⟩
  have hS' : N4c.StmtN4 κ (I.lrows κ) (I.irows κ) vk (stL (entriesOf L (pathOf L j)) 0)
      (stL (entriesOf L (pathOf L j)) 1) (T4.fF (.node κ) L (entriesOf L (pathOf L j))) := by
    rw [hI.1, hI.2]; exact hS.1
  rw [hD.readW κ L _ _ _ hS.1, acc_eqC4 _ _ _ S hV hq, hc]
  exact (N4c.node_sound4' hS' (hRes κ _ _ _ _ hS)).1

/-- **`Resid4H` from the slot interface, the residual and the decoder's interface.** -/
theorem resid4H_of_res (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (D : NodeDec4 nd)
    (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : ReadIface4 fin lRows κs₀ D rd vk) : Resid4H fin lRows κs₀ S nd D vk :=
  ⟨⟨I, rd, hI, hRes⟩, hL_of_res fin lRows κs₀ S vk hV hq D I rd hI hRes hD⟩

end Links

/-! ## Controls -/

section Controls
variable (fin : Finals) (lRows : List Circ.Row) (κs₀ : F)

/-- (−) **`RunLink4` needs an entry of the log**: on the empty log there is no chain. -/
theorem not_runLink4_nil (κ : NodeKind) (vk c : Digest) (π : Proof) (j : ℕ) :
    ¬ RunLink4 fin lRows κs₀ κ vk c π [] j := by
  rintro ⟨-, -, -, -, -, hc, -⟩
  exact absurd hc.1 (Nat.not_lt_zero _)

/-- The public cells fix the statement digests. -/
theorem pubCells4_unique {κ : NodeKind} {w : Circ.Asg} {vk c₁ c₂ c₁' c₂' : Digest}
    (h : N4c.PubCells4 κ w vk c₁ c₂) (h' : N4c.PubCells4 κ w vk c₁' c₂') : c₁ = c₁' ∧ c₂ = c₂' := by
  unfold N4c.PubCells4 at h h'
  rw [h] at h'
  simp only [Node.pubVals, Node.halves, List.cons_append, List.nil_append, List.cons.injEq] at h'
  exact ⟨Circ.digest_ext h'.2.2.2.1 h'.2.2.2.2.1, Circ.digest_ext h'.2.2.2.2.2.2.2.1 h'.2.2.2.2.2.2.2.2.1⟩

/-- A decoder meeting the read law by choice: the digests the public cells carry, the reader's
signed children. -/
noncomputable def readWP (rd : N4c.Read4) (vk : Digest) (κ : NodeKind) (L es : Log) : Wit :=
  open Classical in
  if h : ∃ c : Digest × Digest, N4c.PubCells4 κ (T4.fF (.node κ) L es) vk c.1 c.2 then
    .node h.choose.1 h.choose.2 (rd.sgn κ 0 (T4.fF (.node κ) L es)) (rd.sgn κ 1 (T4.fF (.node κ) L es))
  else .leaf zeroD 0

/-- (+) **The read law is satisfiable** for every reader and key (`readWP`). -/
theorem readW4_readWP (rd : N4c.Read4) (vk : Digest) : ReadW4 (readWP rd vk) rd vk := by
  intro κ L es c₁ c₂ hS
  have hP := hS.2.2.2.2
  have hex : ∃ c : Digest × Digest, N4c.PubCells4 κ (T4.fF (.node κ) L es) vk c.1 c.2 := ⟨(c₁, c₂), hP⟩
  unfold readWP
  split
  · rename_i h
    obtain ⟨e1, e2⟩ := pubCells4_unique h.choose_spec hP
    rw [e1, e2]
  · exact absurd hex ‹_›

/-- (−) **The read law has content**: a decoder that outputs a leaf meets it only if no chain
meets a node's statement. -/
theorem readW4_leaf (rd : N4c.Read4) (vk : Digest)
    (h : ∃ κ L es c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ (T4.fF (.node κ) L es)) :
    ¬ ReadW4 (fun _ _ _ => .leaf zeroD 0) rd vk := by
  obtain ⟨κ, L, es, c₁, c₂, hS⟩ := h
  intro hW
  exact Wit.noConfusion (hW κ L es c₁ c₂ hS)

end Controls

end FR.Snd.L4

end G6_FRNodeLinks4

section G6_FRNodeLinks4Run

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5; track S-L4): the node decoder's
-- links on the accepted run's chain. 3.x analogue: `FRSoundnessExtLinks` (S-N1, `E_node`'s links).

/-!
# The node decoder's links on the run's chain, and its read law

S-H4's decoder (`FRXOut4`) has the links **`LinksD4`** (`decF04_sem`'s hypotheses on the log and
the proof) and the witness **`readW4 sg`** (the statements from their cells, the signed children
of `rd4 pf4` with the signature read from H by `sg`). Both sides of `ReadIface4` at `rd4 pf4`:

* **`linksD4_of_run`**: on the run's chain (`RunLink4`, `AcceptTail`, a good log) `LinksD4` holds
  (3.x's `E_node_of_run` links at revision 4.1):

  | link | lemma |
  |---|---|
  | `¬ StateHit L` | `¬ Bad L` (`muT_lt_one`) |
  | `fmAns (fsQ4 seq4 (vkOf π) c π) st₀ L p = some (ansAt es p)` | **`fmAns_of_run4`** (no repeated query; `vkOf_node4`) |
  | `capDig es i e = capPi4 i π e` | `capDig_eq4` (R4), `cap_lv_node` |
  | `finalAt es x = finPi4 π x` | `finalAt_eq4` (R4), `fin_lv_node` |
  | `¬ farL`, `consSet = jointAgree` | `tail_of_accept`'s `LigeritoOut.close`, `.agree` |

* **`readW4_law`**: `readW4 sg` meets the read law `ReadW4` at `rd4 pf4` if the H signature is L's
  on the node's statement (**`SigH4 sg`**, S-G/S-E's `sig_of_H`): `readW4_eq` with `wF = T4.fF`
  (`wF_eq_fF`).
* **`hL_of_sig`**: `hL` for a decoder with the links `LinksD4` and the witness `readW4 sg`, from
  `hRes` at `rd4 pf4` and `SigH4 sg`.
-/

namespace FR.Snd.L4
open RecursionFast Rev4 X4 R4 FR.X.X4

/-! ## Level parameters and `f⁽⁰⁾` -/

/-- **`FRXOut4`'s `wF` is the tail's `f⁽⁰⁾`** at a node kind (level 0 has 64 rows). -/
theorem wF_eq_fF (κ : NodeKind) (L es : Log) : X.wF κ L es = T4.fF (.node κ) L es := by
  have h : (CKind.lv (.node κ) 0).rows = 64 := by cases κ <;> decide
  funext e; simp only [X.wF, T4.fF, T4.fTab, h]

/-- A node kind's cap depths are `seq4`'s. -/
theorem cap_lv_node (κ : NodeKind) {i : ℕ} (hi : i < 5) : (CKind.lv (.node κ) i).cap = (seq4.lv i).cap := by
  interval_cases i <;> cases κ <;> decide

/-- A node kind's final message has at most `128` elements. -/
theorem fin_lv_node (κ : NodeKind) : 2 ^ T4.mLog (.node κ) 4 ≤ 128 := by
  cases κ <;> decide

/-! ## On the run's chain -/

section Run
variable {impl : OpImpl} {p : KindP} {vk c : Digest} {π : Proof} {tr : Trace}
  {y : List Val × List Bool × Trace}

/-- In a log without repeated queries, the first match of an entry's query is its answer. -/
theorem findSnd_of_mem4 {L : Log} (hL : (L.map Prod.fst).Nodup) {e : ByteArray × Digest}
    (he : e ∈ L) : (L.find? fun x => decide (x.1 = e.1)).map Prod.snd = some e.2 := by
  rw [find_of_mem hL he]; rfl

/-- `FRXChain4`'s message table is R4's at `seq4` (the same positions, decided). -/
theorem fsMsgs4_X : X.fsMsgs4 seq4 = R4.fsMsgs4 seq4 := by
  rw [X.fsMsgs4, R4.fsMsgs4, seq4_eq]; decide +kernel

/-- **The forward chain of first matches is the run's chain** (3.x's `fmAns_of_run` at `seq4`). -/
theorem fmAns_of_run4 (h : SkRun4 impl p ⟨vk, c, π⟩ tr y) {L : Log} (hb : ¬ Bad L)
    (hin : ∀ e ∈ tr, e ∈ L) (st₀ : Digest) :
    ∀ q < 486, X.fmAns (X.fsQ4 seq4 vk c π) st₀ L q = some (ansAt (fsOf tr (itemsOf seq4)) q) := by
  have hnd : (L.map Prod.fst).Nodup := by
    by_contra hr; exact hb (Or.inr (Or.inr (Or.inr hr)))
  have hlen := h.len
  have hmem : ∀ q < 486, (fsOf tr (itemsOf seq4)).getD q default ∈ L := fun q hq => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hin _ (mem_fsOf (List.getElem_mem _))
  intro q
  induction q with
  | zero =>
    intro _
    have hq : ((fsOf tr (itemsOf seq4)).getD 0 default).1 =
        X.fsQ4 seq4 vk c π 0 ((fsOf tr (itemsOf seq4)).getD (0 - 1) default).2 := h.hq 0 (by norm_num)
    have e0 : X.fsQ4 seq4 vk c π 0 st₀ =
        X.fsQ4 seq4 vk c π 0 ((fsOf tr (itemsOf seq4)).getD (0 - 1) default).2 := by
      simp only [X.fsQ4_zero]
    rw [X.fmAns, e0, ← hq]
    exact findSnd_of_mem4 hnd (hmem 0 (by norm_num))
  | succ q ih =>
    intro hq'
    rw [X.fmAns, ih (by omega), Option.bind_some]
    have hq : ((fsOf tr (itemsOf seq4)).getD (q + 1) default).1 =
        X.fsQ4 seq4 vk c π (q + 1) ((fsOf tr (itemsOf seq4)).getD (q + 1 - 1) default).2 := by
      have h1 := h.hq (q + 1) hq'
      rw [← fsMsgs4_X] at h1; exact h1
    rw [Nat.add_sub_cancel] at hq
    rw [show ansAt (fsOf tr (itemsOf seq4)) q = ((fsOf tr (itemsOf seq4)).getD q default).2 from rfl, ← hq]
    exact findSnd_of_mem4 hnd (hmem (q + 1) hq')

end Run

section C
variable (fin : Finals) (lRows : List Circ.Row) (κs₀ : F)

/-- **`LinksD4` holds on the accepted run's chain** (3.x's `E_node_of_run` links, at revision 4.1). -/
theorem linksD4_of_run {κ : NodeKind} {vk c : Digest} {π : Proof} {L : Log} {j : ℕ}
    (hG : GoodX P4f.DFhi L) (hR : RunLink4 fin lRows κs₀ κ vk c π L j)
    (hT : T4.AcceptTail RejFX W0X c0X L j) : X.LinksD4 κ L (entriesOf L (pathOf L j)) π c := by
  obtain ⟨hb, -, -⟩ := T4.muT_lt_one hG.2
  obtain ⟨tr, y, hS, hsem, hin, -, hes, -⟩ := hR
  have hvk : X.vkOf π = vk := vkOf_node4 (inp := ⟨vk, c, π⟩) hS
  have hkC : kindOfC (fsOf tr (itemsOf seq4)) = .node κ := kindOfC_acc_node hsem
  obtain ⟨-, hLig⟩ := T4.tail_of_accept (frontObl_X P4f.frontHi_X).loc (frontChainStab_X P4f.frontHi_X) hG.2 hT
  rw [hes] at hLig ⊢
  refine ⟨fun hs => hb (Or.inr (Or.inr (Or.inl hs))), ⟨zeroD, fun q hq => ?_⟩, fun i hi e he => ?_,
    fun x hx => ?_,
    fun i hi => by have h := hLig.close i hi; rwa [hkC] at h,
    fun i hi => by have h := hLig.agree i hi; rwa [hkC] at h⟩
  · rw [hvk]; exact fmAns_of_run4 hS hb hin zeroD q (by unfold X.nRep4 at hq; omega)
  · rw [cap_lv_node κ hi] at he
    exact capDig_eq4 hS hi he
  · exact finalAt_eq4 hS (lt_of_lt_of_le hx (fin_lv_node κ))

/-- **`ReadIface4` for a decoder whose links follow from `LinksD4`** and which meets the read law. -/
theorem readIface4_of {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c) (rd : N4c.Read4) (vk : Digest)
    (hW : ReadW4 D.readW rd vk) : ReadIface4 fin lRows κs₀ D rd vk :=
  ⟨fun κ L c π _j hG _ _ hR hT => hLk κ L _ π c (linksD4_of_run fin lRows κs₀ hG hR hT), hW⟩

/-! ## The read law of `readW4` -/

/-- **The H side's signature is L's** on the node's statement (S-G/S-E's `sig_of_H`): on every
`f⁽⁰⁾` meeting `StmtN4`, the decoder's signature reader `sg` reads what `rd4`'s `readSig4` reads. -/
def SigH4 (sg : NodeKind → ℕ → Circ.Asg → Sig) (vk : Digest) : Prop :=
  ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w → ∀ σ < 2, sg κ σ w = N4s.readSig4 κ σ w

/-- **`readW4 sg` meets the read law at `rd4 pf4`** given `SigH4 sg` (`readW4_eq`). -/
theorem readW4_law {sg : NodeKind → ℕ → Circ.Asg → Sig} {vk : Digest} (h : SigH4 sg vk) :
    ReadW4 (X.readW4 sg) (N4s.rd4 X.pf4) vk := by
  intro κ L es c₁ c₂ hS
  rw [← wF_eq_fF] at hS ⊢
  exact X.readW4_eq hS.2.2.2.2 (h κ _ c₁ c₂ hS)

/-- **`hL` for S-H4's decoder** (links `LinksD4`, witness `readW4 sg`): from the residual `hRes` at
`rd4 pf4` and `SigH4 sg`. -/
theorem hL_of_sig (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c)
    {sg : NodeKind → ℕ → Circ.Asg → Sig} (hW : D.readW = X.readW4 sg) (hsig : SigH4 sg vk)
    (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4))
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I (N4s.rd4 X.pf4) κ vk c₁ c₂ w) :
    ∀ κ L c π, GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es) :=
  hL_of_res fin lRows κs₀ S vk hV hq D I _ hI hRes
    (readIface4_of fin lRows κs₀ D hLk _ vk (hW ▸ readW4_law hsig))

/-- **`hL_of_sig` over `StmtN4R`** (revision 4.4.2; `hL_of_resR`). -/
theorem hL_of_sigR (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c)
    {sg : NodeKind → ℕ → Circ.Asg → Sig} (hW : D.readW = X.readW4 sg) (hsig : SigH4 sg vk)
    (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4))
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      N4c.NodeResid4 I (N4s.rd4 X.pf4) κ vk c₁ c₂ w) :
    ∀ κ L c π, GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es) :=
  hL_of_resR fin lRows κs₀ S vk hV hq D I _ hI hRes
    (readIface4_of fin lRows κs₀ D hLk _ vk (hW ▸ readW4_law hsig))

end C

/-! ## Controls -/

/-- (−) **`LinksD4` fails on a log with a state hit** (its first conjunct). -/
theorem linksD4_stateHit {κ : NodeKind} {L es : Log} {π : Proof} {c : Digest} (h : StateHit L) :
    ¬ X.LinksD4 κ L es π c := fun hl => hl.1 h

/-- (+) **`SigH4` holds for L's own reader** `readSig4` (the decoder cannot use it: L's row 0 is
not decoded, `out_cells_rows`). -/
theorem sigH4_readSig4 (vk : Digest) : SigH4 N4s.readSig4 vk := fun _ _ _ _ _ _ _ => rfl

/-- (−) **`SigH4` has content**: a reader that differs from `readSig4` on some statement-meeting
witness fails it. -/
theorem sigH4_ne {sg : NodeKind → ℕ → Circ.Asg → Sig} {vk : Digest} {κ : NodeKind} {w : Circ.Asg}
    {c₁ c₂ : Digest} (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) {σ : ℕ} (hσ : σ < 2)
    (hne : sg κ σ w ≠ N4s.readSig4 κ σ w) : ¬ SigH4 sg vk := fun h => hne (h κ w c₁ c₂ hS σ hσ)

/-- (value) The cap depths and the final message's size per node kind. -/
theorem lv_node_ctl : (CKind.lv (.node .N2) 0).cap = 9 ∧ 2 ^ T4.mLog (.node .N2) 4 = 64 ∧
    2 ^ T4.mLog (.node .N4) 4 = 128 := by decide

end FR.Snd.L4

end G6_FRNodeLinks4Run
