-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; track R4i): P4f's `ks_rev4F` and
-- `certificate_rev4F` with X4's residual 2 (`RunFacts4`) discharged but for `SegOut4`. INT-10:
-- `ks_rev4H`/`certificate_rev4H`, with residual 2 discharged in full (no `SegOut4`).
import FRSoundness4XRun
import FRSoundness4P4fObl

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
  P4f.ks_rev4F _ _ S vk hV hq hE hε (runFacts4H_C fin lRows κs₀ vk) I rd hI hRes D hL

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
  P4f.certificate_rev4F _ _ S hV hq hE hε hext hfuel hnd D (fun vk => resid4_of_H fin lRows κs₀ (hR vk)) hC hδ

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
