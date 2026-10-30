-- G6: this module also holds the former modules `FRVerifier4` (one section each, in import order).
import FRAgg
import FRNodeLayout4
import FRVIRSpecCore
import FRVIRFinals4
import FRSegTarget4

section G6_FRVerifier4

-- New for `flock-recursive` (BLUEPRINT revision 4.0, B-11, B-13, B-17; §3; stage S-0′).

/-!
# Revision 4.1's verifier `V4`: the top-level dispatch over `W`, `A`, `N2`, `N4`, `N8`

BLUEPRINT §3 with revision 4.1's kinds (B-11, B-13). `V4with Vseg Vnode vk c π` reads byte 0:

* `'A'` (`aggByte`): the aggregate leaf, `V_A` (`FRAgg.VAwith`) with segment proofs of
  `piSizeOf seq4 = 798,192` bytes and the segment programs `Vseg`;
* a node kind byte (`N2` `'M'`, `N4` `'N'`, `N8` `'O'`) with `|π| = piSizeOf seq4 = 798,192`: the node program
  `Vnode κ`; another size: reject (`bad`), no query. A node's children are verified inside its
  circuit, not by `V4with`: the check a node of kind `κ` applies to an aggregate child is
  `childOk4 κ` (at most `κ.maxK` segments: `N2` refuses `k > 2`, R-4-m2), a row of the node circuit
  (S-E) and a truth of its soundness (S-G);
* a segment kind byte (`L30`, `L31`, `L32`): reject (`bad`): a segment is never a child of the relation,
  only a part of an aggregate leaf;
* anything else: the witness-sending branch (`W`, completeness, `P := encode`), with **this**
  verifier for a node's children (`accWith4`, well-founded on `|π|`), as 3.x's `Vwith`.

`Vseg` and `Vnode` are parameters (the concrete programs are `FRVerifierC4`'s `VsegC`/`VnodeC`).
`qV4 = 36,000` (B-17).

* **`acc_eq4`**: the contract's `Submission.acc` with `V = V4with Vseg Vnode` and `qV = qV4` is
  `accV4`.
* **`V4_W_sound`**, **`V4_encode`**, **`complete4`**: as 3.x's (`δ = 0`). `complete4` is the
  contract's completeness for `P := encode` (the `W` path); it holds for every `Vseg`/`Vnode` and
  is no evidence for the `A`/node path, whose completeness is `FRAgg.VA_complete` (R-4 Q3).
* **`V4_agg_extract`**: an accepted `A` proof yields its leaf witness (`FRAgg.VA_extract`).
* **`V4_queries_le`**, **`ks_queries4`**: `V4with` asks at most `qV4` queries on every input and
  oracle, given per-program bounds (`A`: `4 ×` a segment program's; a node: its program's; `W`:
  none): `KS`'s first conjunct (R-4-m4).
* Controls: `ctrl4_W_leaf` (accepted), `ctrl4_bad_node_size`, `ctrl4_seg_top`, `ctrl4_bad_byte`
  (rejected, no query); `childOk4_ctrl` (`N2` takes an aggregate child of 2 segments and refuses 3;
  `N4` takes 3).
-/

namespace FR
namespace Rev4
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode decodeF encodeF decodeF_eq encodeF_eq
  size_child_lt)

/-- What `V4` does with a proof. -/
inductive PKind4 where
  | W | bad | agg
  | node (κ : NodeKind)
  deriving DecidableEq, Repr

/-- **The kind of a proof** (byte 0, and the size for a node kind). -/
def kindOf4 (π : Proof) : PKind4 :=
  let b := byteAt π 0
  if b = aggByte then .agg
  else match NodeKind.ofByte? b with
    | some κ => if π.size = piSizeOf seq4 then .node κ else .bad
    | none => if (SegKind.ofByte? b).isSome then .bad else .W

/-- **Acceptance of a signed proof** with the verifier's program `v ()` (`Submission.acc` with
`qV4` and the fast hashes; the first conjunct is core PR #20's). -/
def accWith4 (vk : Digest) (p : Signed) (v : Unit → OProg Bool) : Bool :=
  decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ qV4) &&
    decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOkF vk (traceDigestF p.tr) p.σ &&
    decide ((v ()).runSeq p.tr = some true)

/-- The segment programs' type. -/
abbrev SegProgs := SegKind → Digest → Digest → Proof → OProg Bool
/-- The node programs' type. -/
abbrev NodeProgs := NodeKind → Digest → Digest → Proof → OProg Bool

/-- **The verifier** of revision 4.1. -/
def V4with (Vseg : SegProgs) (Vnode : NodeProgs) (vk c : Digest) (π : Proof) : OProg Bool :=
  match kindOf4 π with
  | .agg => VAwith (piSizeOf seq4) Vseg vk c π
  | .node κ => Vnode κ vk c π
  | .bad => .ret false
  | .W =>
    match decodeF π with
    | some (.leaf s n) =>
      .ret (decide (encodeF (.leaf s n) = π) && decide (n ≤ chainCap) &&
        decide (c = leafStmtF (chainEndF s n) n))
    | some (.node c₁ c₂ p₁ p₂) =>
      if _h : encodeF (.node c₁ c₂ p₁ p₂) = π then
        .ret (decide (c = nodeStmtF c₁ c₂) && accWith4 vk p₁ (fun _ => V4with Vseg Vnode vk c₁ p₁.π) &&
          accWith4 vk p₂ (fun _ => V4with Vseg Vnode vk c₂ p₂.π))
      else .ret false
    | none => .ret false
termination_by π.size
decreasing_by
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).1
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).2

/-- **The acceptance predicate of the relation** (revision 4.1). -/
def accV4 (Vseg : SegProgs) (Vnode : NodeProgs) (vk c : Digest) (p : Signed) : Bool :=
  accWith4 vk p fun _ => V4with Vseg Vnode vk c p.π

/-- **`acc_eq4`**: `Submission.acc` is `accV4` for a submission with verifier `V4with Vseg Vnode`
and query bound `qV4`. -/
theorem acc_eq4 (Vseg : SegProgs) (Vnode : NodeProgs) (S : Submission)
    (hV : S.V = V4with Vseg Vnode) (hq : S.qV = qV4) : S.acc = accV4 Vseg Vnode := by
  funext vk c p
  rw [Submission.acc, accV4, accWith4, hV, hq, SigOkF_eq, traceDigestF_eq]

section Branches
variable (Vseg : SegProgs) (Vnode : NodeProgs) (vk c : Digest) (π : Proof)

theorem V4_bad (h : kindOf4 π = .bad) : V4with Vseg Vnode vk c π = .ret false := by
  rw [V4with, h]

theorem V4_agg (h : kindOf4 π = .agg) :
    V4with Vseg Vnode vk c π = VAwith (piSizeOf seq4) Vseg vk c π := by rw [V4with, h]

theorem V4_node {κ : NodeKind} (h : kindOf4 π = .node κ) : V4with Vseg Vnode vk c π = Vnode κ vk c π := by
  rw [V4with, h]

/-- The `W` branch, with the specification functions. -/
theorem V4_W (h : kindOf4 π = .W) : V4with Vseg Vnode vk c π = .ret (
    match decode π with
    | some (.leaf s n) =>
      decide (encode (.leaf s n) = π) && decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
    | some (.node c₁ c₂ p₁ p₂) =>
      if encode (.node c₁ c₂ p₁ p₂) = π then
        decide (c = nodeStmt c₁ c₂) && accV4 Vseg Vnode vk c₁ p₁ && accV4 Vseg Vnode vk c₂ p₂
      else false
    | none => false) := by
  rw [V4with, h]; simp only [decodeF_eq, encodeF_eq, leafStmtF_eq, chainEndF_eq, nodeStmtF_eq, accV4]
  split <;> (try split) <;> simp_all

/-- **An accepted `W` proof is the canonical encoding of a witness of the relation.** -/
theorem V4_W_sound (h : kindOf4 π = .W) (hacc : V4with Vseg Vnode vk c π = .ret true) :
    ∃ w, decode π = some w ∧ encode w = π ∧ Rel (accV4 Vseg Vnode vk) c w := by
  rw [V4_W Vseg Vnode vk c π h, OProg.ret.injEq] at hacc
  split at hacc
  next s n hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
    exact ⟨.leaf s n, hd, hacc.1.1, hacc.1.2, hacc.2⟩
  next c₁ c₂ p₁ p₂ hd =>
    split at hacc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
      exact ⟨.node c₁ c₂ p₁ p₂, hd, ‹_›, hacc.1.1, hacc.1.2, hacc.2⟩
    · cases hacc
  · cases hacc

/-- **An accepted aggregate leaf yields its leaf witness**, given sound segment programs. -/
theorem V4_agg_extract (h : kindOf4 π = .agg) (hS : SegSound Vseg vk) {tr : Trace}
    (hacc : (V4with Vseg Vnode vk c π).runSeq tr = some true) :
    ∃ s n, aggWit (piSizeOf seq4) π = some (s, n) ∧ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n := by
  rw [V4_agg Vseg Vnode vk c π h] at hacc; exact VA_extract hS hacc

end Branches

/-! ## Queries (`KS`'s first conjunct) -/

/-- **`V4with`'s queries** under `H`: at most `qV4`, given a bound `qS` on every segment program's
with `4 · qS + 3 ≤ qV4` (`A`: `k ≤ 4` is checked before any query, and three spacers; R-A′) and
`qV4` on every node program's.
`W` and `bad` ask none. -/
theorem V4_queries_le (Vseg : SegProgs) (Vnode : NodeProgs) (H : ByteArray → Digest) {qS : ℕ}
    (hS : ∀ κ vk c π, ((Vseg κ vk c π).queries H).length ≤ qS)
    (hN : ∀ κ vk c π, ((Vnode κ vk c π).queries H).length ≤ qV4) (hq : 4 * qS + 3 ≤ qV4)
    (vk c : Digest) (π : Proof) : ((V4with Vseg Vnode vk c π).queries H).length ≤ qV4 := by
  rcases h : kindOf4 π with _ | _ | _ | κ
  · rw [V4_W Vseg Vnode vk c π h]; exact Nat.zero_le _
  · rw [V4_bad Vseg Vnode vk c π h]; exact Nat.zero_le _
  · rw [V4_agg Vseg Vnode vk c π h]; exact (VA_queries_le H hS vk c π).trans hq
  · rw [V4_node Vseg Vnode vk c π h]; exact hN _ _ _ _

/-- **`KS`'s first conjunct** for a submission with verifier `V4with Vseg Vnode` and `qV = qV4`. -/
theorem ks_queries4 (Vseg : SegProgs) (Vnode : NodeProgs) (S : Submission)
    (hV : S.V = V4with Vseg Vnode) (hq : S.qV = qV4) {qS : ℕ}
    (hS : ∀ H κ vk c π, ((Vseg κ vk c π).queries H).length ≤ qS)
    (hN : ∀ H κ vk c π, ((Vnode κ vk c π).queries H).length ≤ qV4) (h4 : 4 * qS + 3 ≤ qV4) (vk : Digest) :
    ∀ H c π, ((S.V vk c π).queries H).length ≤ S.qV := fun H c π => by
  rw [hV, hq]; exact V4_queries_le Vseg Vnode H (hS H) (hN H) h4 vk c π

/-- **The spacer's entry is `spacerBytes` bytes** (`FRNodeLayout4`'s constant is `FRAgg.spacerQ`'s). -/
theorem spacerBytes_eq (a : Digest) : (traceBytes [spEntry a]).length = spacerBytes :=
  spacer_entry_length a

/-! ## A node's aggregate child (R-4-m2) -/

/-- **The check a node of kind `κ` applies to a child proof**: an aggregate leaf (`'A'`) has at most
`κ.maxK` segments (`N2`: 2; `N4`/`N8`: 4), so its digest chain fits H (`childOk4_chain`). Any other
child is unaffected. The node circuit enforces it (S-E); `V4with` does not see a node's children. -/
def childOk4 (κ : NodeKind) (π : Proof) : Bool :=
  match kindOf4 π with
  | .agg => decide ((byteAt π 1).toNat ≤ κ.maxK)
  | _ => true

/-- An aggregate child that passes `childOk4 κ` has a chain of at most H's `aggChainLen κ.maxK`
blocks. -/
theorem childOk4_chain {κ : NodeKind} {π : Proof} (h : childOk4 κ π = true) (ha : kindOf4 π = .agg) :
    aggChainLen (byteAt π 1).toNat ≤ aggChainLen κ.maxK := by
  simp only [childOk4, ha, decide_eq_true_eq] at h; exact aggChainLen_le h

/-- **The check binds only `N2`**: for `N4`/`N8` (`maxK = 4`) every proof `V4with` accepts passes it
(`V_A` checks `k ≤ 4`). -/
theorem childOk4_of_accept {κ : NodeKind} (hκ : κ.maxK = 4) {Vseg : SegProgs} {Vnode : NodeProgs}
    {vk c : Digest} {π : Proof} {tr : Trace} (h : (V4with Vseg Vnode vk c π).runSeq tr = some true) :
    childOk4 κ π = true := by
  unfold childOk4
  split
  · next ha =>
    rw [V4_agg Vseg Vnode vk c π ha] at h
    simpa [hκ] using (VA_k_range h).2
  · rfl

/-- Controls: `N2` takes an aggregate child of 2 segments and refuses 3; `N4` takes 3; a
witness-sending proof is unaffected. -/
theorem childOk4_ctrl : childOk4 .N2 ⟨#[aggByte, 2]⟩ = true ∧ childOk4 .N2 ⟨#[aggByte, 3]⟩ = false ∧
    childOk4 .N4 ⟨#[aggByte, 3]⟩ = true ∧ childOk4 .N2 ⟨#[1, 3]⟩ = true := by
  decide

/-! ## Completeness (§5.5) -/

theorem kindOf4_encode (w : Wit) : kindOf4 (encode w) = .W := by
  rcases encode_byte0 w with h | h
  · have hb : byteAt (encode w) 0 = 0 := by rw [byteAt_eq, Array.getD_eq_getD_getElem?, h]; rfl
    unfold kindOf4; simp only [hb]; rfl
  · have hb : byteAt (encode w) 0 = 1 := by rw [byteAt_eq, Array.getD_eq_getD_getElem?, h]; rfl
    unfold kindOf4; simp only [hb]; rfl

theorem fits_of_accWith4 {vk : Digest} {p : Signed} {v : Unit → OProg Bool}
    (h : accWith4 vk p v = true) : p.Fits := by
  simp only [accWith4, Bool.and_eq_true, decide_eq_true_eq, SigOkF_eq, SigOk] at h
  obtain ⟨⟨⟨⟨hπ, htr⟩, hq⟩, ⟨⟨hi, ho⟩, hp⟩, -⟩, -⟩ := h
  exact ⟨hπ, htr.trans_lt (by decide), fun e he => (hq e he).trans_lt (by decide),
    hi.trans (by decide), ho, hp⟩

theorem fits_of_rel4 {Vseg : SegProgs} {Vnode : NodeProgs} {vk c : Digest} {w : Wit}
    (h : Rel (accV4 Vseg Vnode vk) c w) : w.Fits := by
  cases w with
  | leaf s n => exact h.1.trans_lt (by decide)
  | node c₁ c₂ p₁ p₂ => exact ⟨fits_of_accWith4 h.2.1, fits_of_accWith4 h.2.2⟩

/-- **The honest proof of a witness of the relation is accepted, with no query.** -/
theorem V4_encode (Vseg : SegProgs) (Vnode : NodeProgs) {vk c : Digest} {w : Wit}
    (hR : Rel (accV4 Vseg Vnode vk) c w) : V4with Vseg Vnode vk c (encode w) = .ret true := by
  rw [V4_W Vseg Vnode vk c _ (kindOf4_encode w), decode_encode w (fits_of_rel4 hR)]
  cases w with
  | leaf s n => simp [hR.1, hR.2]
  | node c₁ c₂ p₁ p₂ => simp [hR.1, hR.2.1, hR.2.2]

/-- **Perfect completeness** of `P vk c w := ret (encodeF w)` (§5.5), for every key. -/
theorem complete4 (Vseg : SegProgs) (Vnode : NodeProgs) (S : Submission)
    (hV : S.V = V4with Vseg Vnode) (hq : S.qV = qV4) (hP : S.P = fun _ _ w => .ret (encodeF w))
    (vk : Digest) : CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) 0 := by
  refine complete_withError_zero fun H c w hR => ?_
  rw [acc_eq4 Vseg Vnode S hV hq] at hR
  rw [hP, hV]
  show (V4with Vseg Vnode vk c (encodeF w)).run H = true
  rw [encodeF_eq, V4_encode Vseg Vnode hR]; rfl

/-! ## Controls -/

section Controls
variable (Vseg : SegProgs) (Vnode : NodeProgs) (vk : Digest)

/-- Positive: the honest proof of a one-step leaf witness is accepted, with no query. -/
theorem ctrl4_W_leaf (s : Digest) :
    V4with Vseg Vnode vk (leafStmt (chainEnd s 1) 1) (encode (.leaf s 1)) = .ret true :=
  V4_encode Vseg Vnode ⟨by decide, rfl⟩

/-- Negative: a node kind byte with the wrong size is rejected, with no query. -/
theorem ctrl4_bad_node_size (c : Digest) : V4with Vseg Vnode vk c ⟨#[NodeKind.N4.byte]⟩ = .ret false :=
  V4_bad Vseg Vnode vk c _ (by rw [kindOf4, piSizeOf_seq4]; decide)

/-- Negative: a bare segment proof is not a top-level proof (rejected, no query). -/
theorem ctrl4_seg_top (c : Digest) : V4with Vseg Vnode vk c ⟨#[SegKind.L32.byte]⟩ = .ret false :=
  V4_bad Vseg Vnode vk c _ (by decide)

/-- Negative: a first byte that is no kind byte and no witness tag is rejected (the `W` decoder
fails), with no query. -/
theorem ctrl4_bad_byte (c : Digest) : V4with Vseg Vnode vk c ⟨#[2, 0, 0, 0, 0, 0, 0, 0]⟩ = .ret false := by
  rw [V4_W Vseg Vnode vk c _ (by decide)]
  rfl

/-- Positive: the `A` byte reaches `V_A`. -/
theorem ctrl4_agg (c : Digest) (π : Proof) (h : byteAt π 0 = aggByte) :
    V4with Vseg Vnode vk c π = VAwith (piSizeOf seq4) Vseg vk c π :=
  V4_agg Vseg Vnode vk c π (by unfold kindOf4; simp only [h, ite_true])

end Controls

end Rev4
end FR

end G6_FRVerifier4

section G6_FRVerifierC4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §3, B-11 … B-13, A.9; stage S-F4).

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
    seq4.mStar - 7, true, true, 0, segFams, false, false, [], 0, 0⟩

/-- **The reserve's public cells of slot 0, M-relative** (revision 4.4.2; RSV2 §4.3; prototype 0's
compile, read off `nodedump4`'s `mregs-p0.txt`, `logs/RSV2/nodedump/`): the single cells of the slot
program's stacked `evalM` call (`rsvEOps`): its row point's entries 0 … 22 (the E2 challenges `0 … 21`,
entry 22 the kind-muxed entry kept in one cell), its column point's 0 … 24 (the E4 challenges, entry
24 likewise), the nine coefficients `s^P` (one cell each), and its three outputs. Regenerated with the
prototypes (as `FRNodeRows4Hint`); `logs/RSV2/rsvcells.py` checks that each register is exactly one
cell. -/
def rsvRel : List ℕ :=
  [1318, 1329, 1340, 1351, 1362, 1373, 1384, 1395, 1406, 1417, 1428, 1439, 1450, 1461, 1472, 1483,
   1494, 1505, 1516, 1527, 1538, 1549, 116596,
   1579, 1589, 1599, 1609, 1619, 1629, 1639, 1649, 1659, 1669, 1679, 1689, 1699, 1709, 1719, 1729,
   1739, 1749, 1759, 1769, 1779, 1789, 1799, 1809, 116600,
   116584, 116585, 116586, 116587, 116588, 116589, 116590, 116591, 116592,
   116601, 116602, 116603]

/-- **A node's reserve cells** (absolute: M's `one` cell `3·2^logM` plus the relative cell; slot 0
is the previous node's): none without a previous node (`N8`). -/
def rsvCells (κ : NodeKind) : List ℕ := if κ.hasPrev then rsvRel.map (3 * 2 ^ κ.dims.logM + ·) else []

/-- **A node's** (`cells`: its public cells, S-E12′'s layout; the node group's counts; revision 4.4.2:
the reserve's ops for every node kind, on for a kind with a previous node, its 60 cells, RSV2). -/
def nodeFinP (κ : NodeKind) (cells : List ℕ) : FinP :=
  ⟨seq4, kvOf κ.m true nodeFams nodeE4s (κ.m - 7), κ.dims.logL, κ.dims.logM, κ.m - 7, nodeFams, nodeE4s,
    cells, seq4.mStar - 7, false, true, cells.length, nodeFams, true, κ.hasPrev, rsvCells κ, rsvN, κ.ix⟩

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

end G6_FRVerifierC4
