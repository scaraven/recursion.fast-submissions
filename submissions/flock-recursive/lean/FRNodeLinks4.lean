-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.3 `node_sound`, B-13; track S-L4): residual
-- `hL` of `ks_rev4H`/`Resid4H` (the node links) from the circuit residual `hRes` and the run facts.
-- 3.x analogue: `FRNodeSoundA.rel_readWit` with S-N1's `RunLink`.
import FRSoundness4XRunG

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
