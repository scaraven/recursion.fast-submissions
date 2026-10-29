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

/-- **The groups' counts** (revision 4.3): `finPf`'s point families besides `m* = 32` (one per smaller
`m` of the group, which are also the final message's zero tails), and the node group's E4 lengths. -/
def segFams : List ℕ := [30, 31]
def nodeFams : List ℕ := [31]
def nodeE4s : List ℕ := [25, 24]

/-- The kind tables of a revision-4 kind (constants) in a group with families `fams` and E4 lengths
`e4s`: `m`, node or not, `finPf`'s family (`m*`'s, else its index in `fams`), its claim points (Z, Lc,
Sh of its family; a node's E4 point of length `e4`). -/
def kvOf (m : ℕ) (node : Bool) (fams e4s : List ℕ) (e4 : ℕ) : KV :=
  let nf := fams.length; let i := fams.idxOf m; let a := decide (m = seq4.mStar)
  let base := if a then [0, 1 + nf, 2 + 2 * nf] else [1 + i, 2 + nf + i, 3 + 2 * nf + i]
  ⟨fun _ => m, fun _ => node, fun _ => a,
   fun _ => if node then base ++ [3 + 3 * nf + e4s.idxOf e4] else base, fun _ => if a then 0 else i⟩

/-- **A segment's finals' parameters** (`vn`: the variable last block; the segment group's counts;
no reserve). -/
def segFinP (κ : SegKind) : FinP :=
  ⟨seq4, kvOf κ.m false segFams [seq4.e4] seq4.e4, seq4.lr, seq4.e2, seq4.e4, segFams, [seq4.e4], [],
    seq4.mStar - 7, true, true, 0, segFams, false, false, [], 0⟩

/-- **The reserve's public cells of slot 0, M-relative** (revision 4.4.2, D1p §3; prototype 0's
compile, read off `nodedump4`'s `mregs-p0.txt`, `logs/RSV/nodedump/`): the single import cells of the
slot program's registers E2's 23 challenges, E4's 25, its own `evalM`'s three outputs, its kind
element (`hdr[0…16)`, the seed's `piElem 0 0`). Regenerated with the prototypes (as
`FRNodeRows4Hint`; B2′'s templates move them). -/
def rsvRel : List ℕ :=
  [1318, 1329, 1340, 1351, 1362, 1373, 1384, 1395, 1406, 1417, 1428, 1439, 1450, 1461, 1472, 1483,
   1494, 1505, 1516, 1527, 1538, 1549, 1560,
   1579, 1589, 1599, 1609, 1619, 1629, 1639, 1649, 1659, 1669, 1679, 1689, 1699, 1709, 1719, 1729,
   1739, 1749, 1759, 1769, 1779, 1789, 1799, 1809, 1819,
   116490, 116491, 116492, 6]

/-- **A node's reserve cells** (absolute: M's `one` cell `3·2^logM` plus the relative cell; slot 0
is the previous node's): none without a previous node (`N8`). -/
def rsvCells (κ : NodeKind) : List ℕ := if κ.hasPrev then rsvRel.map (3 * 2 ^ κ.dims.logM + ·) else []

/-- **A node's** (`cells`: its public cells, S-E12′'s layout; the node group's counts; revision 4.4.2:
the reserve's ops for every node kind, on for a kind with a previous node, its 52 cells). -/
def nodeFinP (κ : NodeKind) (cells : List ℕ) : FinP :=
  ⟨seq4, kvOf κ.m true nodeFams nodeE4s (κ.m - 7), κ.dims.logL, κ.dims.logM, κ.m - 7, nodeFams, nodeE4s,
    cells, seq4.mStar - 7, false, true, cells.length, nodeFams, true, κ.hasPrev, rsvCells κ, 52⟩

/-- **The segment program.** -/
def progSeg (κ : SegKind) : VProg := genSeg κ (finOps4 (segFinP κ))

/-- **The node program.** -/
def progNode (κ : NodeKind) (cells : List ℕ) : VProg := genNode κ (finOps4 (nodeFinP κ cells))

/-! ## The statement fact after the run (revision 4.3) -/

/-- **A run, then a check on its result** (`OProg.bind` into `ret`): the same queries. -/
theorem queries_bind_ret {α β : Type} (H : ByteArray → Digest) (f : α → β) :
    ∀ p : OProg α, (p.bind fun a => .ret (f a)).queries H = p.queries H
  | .ret _ => rfl
  | .query q k => by simp only [OProg.bind, OProg.queries, queries_bind_ret H f (k (H q))]

theorem runSeq_bind_ret {α β : Type} (f : α → β) :
    ∀ (p : OProg α) (tr : Trace), (p.bind fun a => .ret (f a)).runSeq tr = (p.runSeq tr).map f
  | .ret _, [] => rfl
  | .ret _, _ :: _ => rfl
  | .query _ _, [] => rfl
  | .query q k, (q', a) :: tr => by
    simp only [OProg.bind, OProg.runSeq]; split_ifs
    · exact runSeq_bind_ret f (k a) tr
    · rfl

theorem runLog_bind_ret {α β : Type} (f : α → β) (L : Log) :
    ∀ p : OProg α, (p.bind fun a => .ret (f a)).runLog L = (p.runLog L).map f
  | .ret _ => rfl
  | .query q k => by
    simp only [OProg.bind, OProg.runLog]
    cases (L.find? fun e => e.1 = q) with
    | none => rfl
    | some e => exact runLog_bind_ret f L (k e.2)

/-- **The program's run, and the statement fact** (`stmtOk4`): the verifier of one kind. -/
def runStmt (impl : OpImpl) (P : VProg) (p : KindP) (inp : Input) : OProg Bool :=
  (runIR impl P inp).bind fun ok => .ret (ok && stmtOk4 seq4 p inp)

/-! ## The verifiers -/

/-- **`Vseg`**: the segment program under the segment's ops, and the statement fact. -/
def VsegC (impl₀ : OpImpl) : SegProgs := fun κ vk c π =>
  runStmt (implSeg impl₀) (progSeg κ) (.ofSeg κ) ⟨vk, c, π⟩

/-- **`Vnode`**: the node program under the node kind's ops, and the statement fact. The node's
children are checked in its circuit; on an aggregate child that includes `childOk4 κ` (`N2`: at most
2 segments; S-E's row). -/
def VnodeC (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ) : NodeProgs :=
  fun κ vk c π => runStmt (implN κ) (progNode κ (cells κ)) (.ofNode κ) ⟨vk, c, π⟩

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

/-- (+) **The groups' tables** (revision 4.3): a kind of `m* = 32` reads the `m*` family, `N2` and
`L30`/`L31` their own; the claim points are the family's (and the node's E4 of its length). -/
theorem kv_ctrl : (nodeFinP .N4 []).kv.ptIx .N30 = [0, 2, 4, 6] ∧
    (nodeFinP .N2 []).kv.ptIx .N30 = [1, 3, 5, 7] ∧
    (nodeFinP .N2 []).kv.selA .N30 = false ∧ (segFinP .L32).kv.ptIx .L32 = [0, 3, 6] ∧
    (segFinP .L30).kv.ptIx .L32 = [1, 4, 7] ∧ (segFinP .L31).kv.ptIx .L32 = [2, 5, 8] ∧
    (segFinP .L31).kv.fsel .L32 = 1 ∧ (segFinP .L30).kv.fsel .L32 = 0 := by decide

/-- (+) **The run with the fact accepts iff the run accepts and the fact holds.** -/
theorem runStmt_iff (impl : OpImpl) (P : VProg) (p : KindP) (inp : Input) (tr : Trace) :
    (runStmt impl P p inp).runSeq tr = some true ↔
      (runIR impl P inp).runSeq tr = some true ∧ stmtOk4 seq4 p inp = true := by
  rw [runStmt, runSeq_bind_ret]
  cases (runIR impl P inp).runSeq tr with
  | none => simp
  | some b => cases b <;> simp

/-- (−) **A wrong statement fact rejects**, whatever the run; and of two digests at most one is the
statement's (the fact is not vacuous). -/
theorem runStmt_wrong (impl : OpImpl) (P : VProg) (p : KindP) (inp : Input) (tr : Trace)
    (h : stmtOk4 seq4 p inp = false) : (runStmt impl P p inp).runSeq tr ≠ some true := by
  rw [Ne, runStmt_iff, h]; simp

theorem stmtOk4_unique (p : KindP) (vk c₁ c₂ : Digest) (π : ByteArray)
    (h₁ : stmtOk4 seq4 p ⟨vk, c₁, π⟩ = true) (hne : c₂ ≠ c₁) : stmtOk4 seq4 p ⟨vk, c₂, π⟩ = false := by
  simp only [stmtOk4, decide_eq_true_eq, decide_eq_false_iff_not] at h₁ ⊢
  rw [h₁]; exact fun h => hne h.symm

/-- (+) **The queries are the program's**: the fact asks nothing. -/
theorem runStmt_queries (impl : OpImpl) (P : VProg) (p : KindP) (inp : Input) (H : ByteArray → Digest) :
    (runStmt impl P p inp).queries H = (runIR impl P inp).queries H :=
  queries_bind_ret H _ _

/-- (−) **A segment kind byte at the top is rejected without a query**, and so is a node of the
wrong size (`VC4` dispatches as `V4with`). -/
theorem VC4_rejects (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ)
    (vk c : Digest) :
    VC4 impl₀ implN cells vk c ⟨#[SegKind.L32.byte]⟩ = .ret false ∧
      VC4 impl₀ implN cells vk c ⟨#[NodeKind.N4.byte]⟩ = .ret false :=
  ⟨ctrl4_seg_top _ _ vk c, ctrl4_bad_node_size _ _ vk c⟩

end Rev4
end FR
