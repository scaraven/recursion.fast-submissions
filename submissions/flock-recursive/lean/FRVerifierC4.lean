-- New for `flock-recursive` (BLUEPRINT revision 4.1, §3, B-11 … B-13, A.9; stage S-F4).
import FRVIRFinals4
import FRSegTarget4
import FRVerifier4

/-!
# Revision 4.1's verifier programs: `Vseg` for L30/L31/L32, `Vnode` for N2/N4/N8

* **The programs** (`progSeg κ`, `progNode κ cells`): `FRVIR4.genSeg`/`genNode` with the finals
  over `seq4` (`finOps4`, `FRVIRFinals4`) at the kind's parameters (`segFinP`, `nodeFinP`): the
  kind tables are constants (`kvOf`), the node's real Lr/E2/E4 counts are its `logL`, `logM`,
  `m − 7`, `finPf`'s points are the kind's `m` family, and a segment's last block is variable
  (`vn`). A node's public cells are a parameter (its layout is S-E12′'s).
* **The verifiers**: `VsegC impl₀` runs a segment program under `implSeg impl₀` (the segment's
  `targetS` and `shiftMask`, `FRSegTarget4`); `VnodeC implN cells` runs a node program under the
  node kind's ops `implN κ` (its `evalM`, `evalL`, `targetS`, `linkWAll`, `shiftMask` are the node
  plan's: S-E12′). `VC4 = V4with VsegC VnodeC`.
* **`acc_eqC4`** (`acc_eq4` at the concrete programs), **`implSegC_meets`** (`implC_meets`'s
  analogue: with 3.x's ops as the base), **`VC4_agg_extract`** (an accepted `A` proof yields its
  leaf witness from the segments' knowledge soundness on good traces, `SegKSOn`, through
  `leaf_sound`).
-/

namespace FR
namespace Rev4
open RecursionFast

/-! ## Parameters and programs -/

/-- The kind tables of a revision-4 kind (constants): `m`, node or not, `finPf`'s second family,
its claim points (`Z`, `Lc`, `Sh` of the `mB` family, and a node's E4 point). -/
def kvOf (m : ℕ) (node : Bool) : KV :=
  ⟨fun _ => m, fun _ => node, fun _ => false, fun _ => if node then [1, 3, 5, 6] else [1, 3, 5]⟩

/-- **A segment's finals' parameters** (`vn`: the variable last block). -/
def segFinP (κ : SegKind) : FinP :=
  ⟨seq4, kvOf κ.m false, seq4.lr, seq4.e2, seq4.e4, κ.m, [], κ.m - 7, true⟩

/-- **A node's** (`cells`: its public cells, S-E12′'s layout). -/
def nodeFinP (κ : NodeKind) (cells : List ℕ) : FinP :=
  ⟨seq4, kvOf κ.m true, κ.dims.logL, κ.dims.logM, κ.m - 7, κ.m, cells, κ.m - 7, false⟩

/-- **The segment program.** -/
def progSeg (κ : SegKind) : VProg := genSeg κ (finOps4 (segFinP κ))

/-- **The node program.** -/
def progNode (κ : NodeKind) (cells : List ℕ) : VProg := genNode κ (finOps4 (nodeFinP κ cells))

/-! ## The verifiers -/

/-- **`Vseg`**: the segment program under the segment's ops. -/
def VsegC (impl₀ : OpImpl) : SegProgs := fun κ vk c π => runIR (implSeg impl₀) (progSeg κ) ⟨vk, c, π⟩

/-- **`Vnode`**: the node program under the node kind's ops. -/
def VnodeC (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ) : NodeProgs :=
  fun κ vk c π => runIR (implN κ) (progNode κ (cells κ)) ⟨vk, c, π⟩

/-- **The verifier** with the concrete programs. -/
def VC4 (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ) :
    Digest → Digest → Proof → OProg Bool :=
  V4with (VsegC impl₀) (VnodeC implN cells)

/-- **`acc_eq4` at the concrete programs.** -/
theorem acc_eqC4 (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ)
    (S : Submission) (hV : S.V = VC4 impl₀ implN cells) (hq : S.qV = qV4) :
    S.acc = accV4 (VsegC impl₀) (VnodeC implN cells) :=
  acc_eq4 _ _ S hV hq

/-- **`implC_meets`'s analogue**: with 3.x's ops as the base, the segment's ops meet their
specification. -/
theorem implSegC_meets (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) :
    (implSeg (Impl.implC fin lRows κs₀)).Meets (specSeg (Impl.specC fin lRows κs₀)) :=
  implSeg_meets (Impl.implC_meets fin lRows κs₀)

/-- **An accepted aggregate leaf yields its leaf witness** on a good trace, from the segment
programs' knowledge soundness on good traces (`SegKSOn`, the SNARK's half: S-G) and the circuit's
`leaf_sound` (`segSoundOn_of_KS`). -/
theorem VC4_agg_extract {impl₀ : OpImpl} {implN : NodeKind → OpImpl} {cells : NodeKind → List ℕ}
    {vk c : Digest} {π : Proof} {tr : Trace} {Good : Trace → Prop}
    (hKS : SegKSOn (VsegC impl₀) vk Good)
    (hG : ∀ trs : List Trace, tr = trs.flatten → ∀ t ∈ trs, Good t)
    (h0 : kindOf4 π = .agg) (h : (VC4 impl₀ implN cells vk c π).runSeq tr = some true) :
    ∃ s n, aggWit (piSizeOf seq4) π = some (s, n) ∧ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n := by
  rw [VC4, V4_agg _ _ _ _ _ h0] at h
  exact VA_extract_on (segSoundOn_of_KS hKS) hG h

/-! ## Controls -/

/-- (+) **The parameters**: a segment's last block is variable and its finals read the kind's `m`;
a node's real counts are its own (`N2`: Lr 16, E2 22, E4 24). -/
theorem finP_ctrl : (segFinP .L30).vn = true ∧ (segFinP .L30).kv.m .L32 = 30 ∧
    (nodeFinP .N2 []).vn = false ∧ ((nodeFinP .N2 []).lrR, (nodeFinP .N2 []).e2R, (nodeFinP .N2 []).e4R) =
      (16, 22, 24) := ⟨rfl, rfl, rfl, rfl⟩

/-- (−) **A segment kind byte at the top is rejected without a query**, and so is a node of the
wrong size (`VC4` dispatches as `V4with`). -/
theorem VC4_rejects (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ)
    (vk c : Digest) :
    VC4 impl₀ implN cells vk c ⟨#[SegKind.L32.byte]⟩ = .ret false ∧
      VC4 impl₀ implN cells vk c ⟨#[NodeKind.N4.byte]⟩ = .ret false :=
  ⟨ctrl4_seg_top _ _ vk c, ctrl4_bad_node_size _ _ vk c⟩

end Rev4
end FR
