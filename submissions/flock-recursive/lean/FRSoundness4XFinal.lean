-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-11 … B-15, §5; stage X4, items 4–5): the
-- knowledge soundness of `V4with VsegC VnodeC` with every remaining gap a named hypothesis, and the
-- map onto the contract's `Certificate` (core `6d05d00`).
-- RET-2: import re-pointed at Core: `FRKState` → `FRSoundnessCoreRows`.
import FRSoundness4XLaws
import FRX4Ext
import FRSoundnessCoreRows

/-!
# `ks_rev4`: revision 4.1's knowledge soundness, composed

**`ks_rev4`** is the contract's `KS` for `VC4 impl₀ (implN4F base) cells4` (the segment programs
under `implSeg impl₀`, the node programs under INT-9's `implN4F`), the extractor
`S.E = E4X nd S.acc` (S-H3) and the error `S.ε = εR`. It is S-H3's `ks4_E4X` at T4's potential
`muT` of the composed front (`frontObl_X`, `muT_laws_of_front`), with
* the segment law from `segSound_X`;
* `NodeSoundLog` from S-E12a's `nodeLaws4C'`, its per-run truths from `nodeRun_X`.

**Its hypotheses are exactly the named residuals** (`X4-RESULT.md`, with owners):
* `hHi : FrontHi DFhi`: phases 13 … 25 of the front (P4b's unrun item 2);
* `hRun : RunFacts4 …`: the program layer's run facts (R4's `acceptTail4_of_run` assembled with
  R4h's `pf0`/`enc`/`fin`, the `not_rej*` theorems, and the statement views);
* `hI`, `hRes`: S-E's slot interface `I` at the node rows and its residual `NodeResid4`;
* `D : NodeDec4 nd`, `hL`: S-H4's node decoder and its links on the domain;
* the definitional hypotheses `hV`, `hq`, `hE`, `hε` that fix the submission.

**`certificate_rev4`** builds the contract's `Certificate` from `ks_rev4` (for every key), the
completeness (a named residual), `computes4` (`DecOk4 nd`, S-H4's) and the caps (`epsR_le_errorCap`,
`ext4_caps`).
-/

namespace FR.Snd.X4
open RecursionFast FR.Rev4 FR.X.X4
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- **The node laws at the concrete node programs**, from the front's residual, the run facts and
S-E's slot interface (`nodeLaws4C'`). -/
theorem nodeSound_X (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ implN N4c.cells4) (hq : S.qV = qV4) {DFhi : ℕ → Log → Log → Prop}
    (hHi : FrontHi DFhi) (hRun : RunFacts4 (VsegC impl₀) (VnodeC implN N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC implN N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w) :
    NodeSoundLog (VnodeC implN N4c.cells4) vk (GoodX DFhi) (Rel (S.acc vk)) := by
  obtain ⟨hl, hi⟩ := hI
  refine (N4c.nodeLaws4C' impl₀ implN N4c.cells4 S vk hV hq I rd ?_ ?_).1
  · rw [hl, hi]; exact nodeRun_X hHi hRun
  · rw [hl, hi]; exact hRes

/-- **`KS` for revision 4.1's verifier** at the extractor `E4X nd S.acc` and `S.ε = εR`; every
hypothesis after `hε` is a named residual (`X4-RESULT.md`). -/
theorem ks_rev4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    {DFhi : ℕ → Log → Log → Prop} (hHi : FrontHi DFhi)
    (hRun : RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV := by
  have hF := T4.muT_laws_of_front (frontObl_X hHi)
  rw [hε]
  exact ks4_E4X impl₀ (NI4F.implN4F base) N4c.cells4 S vk hV hq D hE _ hF.1 hF.2
    (segSound_X hHi hRun) (nodeSound_X impl₀ _ S vk hV hq hHi hRun I rd hI hRes) hL

/-! ## The contract's `Certificate` -/

/-- **The residuals of `ks_rev4` at one key** (everything but the submission's definition). -/
structure Resid4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (nd : X.XIR)
    (D : NodeDec4 nd) (DFhi : ℕ → Log → Log → Prop) (vk : Digest) : Prop where
  run : RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk
  slots : ∃ (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4))
    (rd : N4c.Read4), (I.lrows = lRows4 ∧ I.irows = nodeIRows4) ∧
      ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
        N4c.NodeResid4 I rd κ vk c₁ c₂ w
  links : ∀ κ L c π, GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)

/-- **The contract's `Certificate` for the revision 4.1 submission**: `secure` from `ks_rev4`,
`computes` from S-H3's `computes4`, the caps from `epsR_le_errorCap` and `ext4_caps`; the
completeness and `δ`'s cap are named hypotheses. -/
theorem certificate_rev4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd) (hfuel : S.fuel = X.fuel)
    (hnd : DecOk4 nd) (D : NodeDec4 nd) {DFhi : ℕ → Log → Log → Prop} (hHi : FrontHi DFhi)
    (hR : ∀ vk, Resid4 impl₀ base S nd D DFhi vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S where
  secure vk := by
    obtain ⟨hrun, ⟨I, rd, hI, hRes⟩, hL⟩ := hR vk
    exact ks_rev4 impl₀ base S vk hV hq hE hε hHi hrun I rd hI hRes D hL
  complete := hC
  computes := by rw [hext, hE, hfuel]; exact computes4 hnd S.acc
  cap := by
    obtain ⟨hf, hs⟩ := ext4_caps hnd
    refine ⟨hε ▸ epsR_le_errorCap, hδ, by rw [hq, qV4]; norm_num, fun t => ?_, by rw [hext]; exact hs⟩
    rw [hfuel]; exact hf t

end FR.Snd.X4
