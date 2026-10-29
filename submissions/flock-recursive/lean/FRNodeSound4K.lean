-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; stage S-N2): P4f's `ks_rev4F` and
-- `certificate_rev4F` with residuals 3–4 (the slot interface, its reader, `hRes`) instantiated.
import FRNodeSound4R
import FRSoundness4P4fObl
import FRSoundness4XRunG

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
