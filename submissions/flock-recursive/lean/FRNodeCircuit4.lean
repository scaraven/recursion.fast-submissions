-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-13, §4.3 `node_sound`, A.6/A.7 per kind;
-- R-4-m2; stage S-E12a). 3.x templates: `FRNodeCircuit` (`node_sound`, `SlotHolds`, `PubCells`),
-- `FRNodeSoundA` (`NodeResid`, `rel_readWit`), `FRSoundnessExtAll` (`hRes`).
import FRNodeKinds4
import FRVIRFinalsCoreSG
import FRSoundness4Frame
import FRSoundness4P4bRows
import FRVerifierC4
import FRSoundness4P4aNames

/-!
# The revision 4.1 node relation and `node_sound4`

A node of kind `κ` (`N2`/`N4`/`N8`) has two **signed children** `σ ∈ {0, 1}` (`N2`/`N4`: the
previous node, then the aggregate leaf; `N8`: two aggregates) and `κ.vslots` **verifier slots**
(`N2`/`N4`: slot 0 the previous node, slots `1 + i` the aggregate's segments; `N8`: slots `4a + i`
aggregate `a`'s segments). Aggregate `a` (signed child `aggChild κ a`) has `k_a` segments, read from
its header (`kA`): sub-slots `i < k_a` are active, the rest inactive.

* **`StmtN4`** (what the PIOP's truths give on `f⁽⁰⁾ = w`): `truthZ4` (every non-free block meets its
  kind's R1CS with its target, `nodeKind4`), `truthS4` (the chain mask `chainLk4` and the WOTS link
  families, rebased), the L rows, the M rows (indexed, `truthEI`), `PubCells4` (`cells4` carry
  `1, vk, c₁, vk, c₂`).
* **`SlotIface4`**: what S-E12b's compiled rows provide per verifier slot: three predicates (the
  imports `imp`, the replay `rep`, the templates `tpl`), the kind selectors, and the two soundness
  facts `soundN`/`soundS` (rows + imports + R + templates ⇒ the slot's program accepts its input on
  its trace).
* **`Read4`**: the pack map's read of the children from `w` (signed children; slots' proofs and
  traces).
* **`NodeResid4`**: everything the M/L rows must still certify, item by item (the JOURNAL's §0):
  `imp`, `rep`, `tpl`, `selP`, `slotP`, `selA`, `pack`, `chainMsg`, `aggFmt`, `aggTr`, `aggChk`,
  `kOk` (`childOk4`), `aggPad` (R-4-m2's `k`-gated padding), `wots`.
* **`DigLemma4 κ`**: the H side's BLAKE2s chain fact (the digest computed in H, `hDig4`, is the
  trace digest), from `truthZ4`/`truthS4`, the chain's bytes and `AggPad4`. A theorem obligation of
  the H side (3.x: `Stream.blake2s_chain`), a hypothesis here.
* **`node_sound4`**: `StmtN4` + `NodeResid4` + `DigLemma4` give a witness of the relation
  `Rel (accV4 Vseg Vnode vk)` for `nodeStmt c₁ c₂` with both read children, and `childOk4` of
  both. **`nodeSoundLog4_of`**, **`nodeExtLog4_of`**: the node laws of `FRSoundness4Frame` from
  the PIOP's per-run truths (`hRun`) and the residual (`hRes`).
* **`HFit4`**: `RowsFitI` per node kind over S-E12b's indexed rows (parametric), with
  `rowsFitI_of_sorted` (strictly increasing indices give distinctness: the generator's
  certificate).
-/

namespace FR
namespace N4c
open RecursionFast Rev4 Circ

/-! ## The H bits and digests -/

/-- Bit `b` of `f` (A.7: element `⌊b/128⌋`, bit `b mod 128`). -/
noncomputable def zW4 (w : Asg) (b : ℕ) : F := unpack (w (b / 128)) ⟨b % 128, Nat.mod_lt _ (by norm_num)⟩

/-- Block `blk`'s positions. -/
noncomputable def zB4 (w : Asg) (blk : ℕ) : Block.Pos → F := fun k => zW4 w (blk * 2 ^ 14 + k.val)

/-- Block `blk`'s position `p`. -/
noncomputable def zN4 (w : Asg) (blk p : ℕ) : F := zW4 w (blk * 2 ^ 14 + p)

/-- Block `blk`'s bits as Booleans. -/
noncomputable def bitsB4 (w : Asg) (blk : ℕ) : Block.Pos → Bool := fun k => decide (zB4 w blk k = 1)

/-- **The block where signed child `σ`'s chain ends** with `k` segments: an aggregate of `k < maxK`
ends at its candidate final block `F_{a,k}`, otherwise at its main chain's last block. -/
def finBlk (κ : NodeKind) (σ k : ℕ) : ℕ :=
  if isAgg κ σ ∧ k < κ.maxK then finB κ (aggOf κ σ) + (k - 1) else chBase κ σ + chLen κ σ - 1

/-- Blocks and bytes of signed child `σ`'s stream with `k` segments. -/
def streamL (κ : NodeKind) (σ k : ℕ) : ℕ := if isAgg κ σ then aggL k else cLen
def streamB (κ : NodeKind) (σ k : ℕ) : ℕ := if isAgg κ σ then aggB k else segB

/-- **The digest computed in H**: `h_out` of the final block. -/
noncomputable def hDig4 (κ : NodeKind) (σ k : ℕ) (w : Asg) : Digest :=
  Block.readDigest (bitsB4 w (finBlk κ σ k)) 256

/-- Stream block `i` of signed child `σ`'s chain with `k` segments: the main chain's block `i`,
except the last, which is the final block (`finBlk`). -/
def blkOf (κ : NodeKind) (σ k i : ℕ) : ℕ := if i + 1 = streamL κ σ k then finBlk κ σ k else chBase κ σ + i

/-- The chain's blocks as Boolean blocks, in stream order. -/
noncomputable def chainW4 (κ : NodeKind) (σ k : ℕ) (w : Asg) : ℕ → Block.Pos → Bool :=
  fun i => bitsB4 w (blkOf κ σ k i)

/-- **The bytes the chain hashes**: byte `p` is message byte `p mod 64` of stream block `⌊p/64⌋`
(`Stream.streamBytes`). -/
noncomputable def chainBytes4 (κ : NodeKind) (σ k : ℕ) (w : Asg) : List UInt8 :=
  Stream.streamBytes (chainW4 κ σ k w) (streamB κ σ k)

/-- **R-4-m2's `k`-gated last block** of aggregate `a` with `k` segments. With `j = aggL k` blocks
and `r = aggB k − 64 (j − 1)` bytes in the last: if `k < maxK`, the candidate final block's `h_in`
is the main chain's block `j − 2`'s `h_out` and its first `r` message bytes are the main chain's
block `j − 1`'s; in every case the final block's message bytes `r … 63` are zero. -/
def AggPad4 (κ : NodeKind) (a k : ℕ) (w : Asg) : Prop :=
  let σ := aggChild κ a
  let j := aggL k
  let r := aggB k - 64 * (j - 1)
  (k < κ.maxK →
    (∀ x < 256, zN4 w (finBlk κ σ k) x = zN4 w (chBase κ σ + j - 2) (256 + x)) ∧
    ∀ x < 8 * r, zN4 w (finBlk κ σ k) (512 + x) = zN4 w (chBase κ σ + j - 1) (512 + x)) ∧
  ∀ x, 8 * r ≤ x → x < 512 → zN4 w (finBlk κ σ k) (512 + x) = 0

/-! ## The statement (the PIOP's truths on `f⁽⁰⁾`) -/

/-- **Z**: every non-free block meets its kind's R1CS with its public target. -/
def truthZ4 (κ : NodeKind) (w : Asg) : Prop :=
  ∀ blk < κ.blocks, ∀ tgt, nodeKind4 κ blk = some tgt →
    Block.HoldsE (Block.blockR1CS tgt) (Block.targetVal F tgt) (zB4 w blk)

/-- **S**: the chain mask's links and the WOTS link families (A.8, rebased). -/
def truthS4 (κ : NodeKind) (w : Asg) : Prop :=
  (∀ y, chainLk4 κ y = true → ∀ j < 256, zN4 w (y + 1) j = zN4 w y (256 + j)) ∧
    ∀ f < nLinkFam, ∀ σ < 2, ∀ t < (NodeT.fam f).n, ∀ s < NodeT.fbits f,
      zN4 w (srcB4 κ σ f t) (NodeT.fpos f s) = zN4 w (mirB4 κ σ f t) (NodeT.mpos f t s)

/-- **The public cells** (A.7 per kind): `1`, then `vk` and `c_σ`'s halves per signed child. -/
def PubCells4 (κ : NodeKind) (w : Asg) (vk c₁ c₂ : Digest) : Prop :=
  (cells4 κ).map w = Node.pubVals vk c₁ c₂

/-- **The reserve's public cells** (revision 4.4.2; RSV2 §2.4: the V side's 60 cells after the nine,
`Rev4.rsvCells`): slot 0's stacked `evalM` call, its row point's 23 coordinates `x̂`, its column point's
25 `ŷ`, its nine coefficients `s` and its three outputs `X₃`, hold the node's own proof's child claim
`ch` (`fLrEnd`'s `p_x ‖ p_y ‖ s ‖ X₃`, read by `finB′`). Empty for `N8`. Not yet a conjunct of `StmtN4` (the soundness track's). -/
def PubCellsR4 (κ : NodeKind) (w : Asg) (ch : List F) : Prop :=
  (Rev4.rsvCells κ).map w = ch

/-- **`StmtN4`**: the node's truths on `w`, with the L rows `lr` and the indexed M rows `er`. -/
def StmtN4 (κ : NodeKind) (lr : List Row) (er : List (ℕ × Row)) (vk c₁ c₂ : Digest) (w : Asg) : Prop :=
  truthZ4 κ w ∧ truthS4 κ w ∧ (∀ r ∈ lr, r.Holds w) ∧ Snd.P4b.truthEI er w ∧ PubCells4 κ w vk c₁ c₂

/-! ## The slots, the reader, the residual -/

/-- **What the compiled rows provide per verifier slot** (S-E12b): the node kind's L and M rows,
three predicates of slot `v` (imports, the replay `R`, the templates), the kind selectors of the
two kind groups, and the slot's soundness under each. -/
structure SlotIface4 (Vseg : SegProgs) (Vnode : NodeProgs) where
  lrows : NodeKind → List Row
  irows : NodeKind → List (ℕ × Row)
  imp : NodeKind → ℕ → Asg → Input → Trace → Prop
  rep : NodeKind → ℕ → Asg → Input → Trace → Prop
  tpl : NodeKind → ℕ → Asg → Prop
  selN : NodeKind → ℕ → Asg → NodeKind → Prop
  selS : NodeKind → ℕ → Asg → SegKind → Prop
  soundN : ∀ κ v w inp tr κ', (∀ r ∈ lrows κ, r.Holds w) → Snd.P4b.truthEI (irows κ) w →
    selN κ v w κ' → imp κ v w inp tr → rep κ v w inp tr → tpl κ v w →
    (Vnode κ' inp.vk inp.c inp.π).runSeq tr = some true
  soundS : ∀ κ v w inp tr κ', (∀ r ∈ lrows κ, r.Holds w) → Snd.P4b.truthEI (irows κ) w →
    selS κ v w κ' → imp κ v w inp tr → rep κ v w inp tr → tpl κ v w →
    (Vseg κ' inp.vk inp.c inp.π).runSeq tr = some true

/-- **The pack map's read** of a node's children from `w`. -/
structure Read4 where
  /-- Signed child `σ`: proof, trace, signature. -/
  sgn : NodeKind → ℕ → Asg → Signed
  /-- Verifier slot `v`'s proof and trace. -/
  slotπ : NodeKind → ℕ → Asg → Proof
  slotTr : NodeKind → ℕ → Asg → Trace

/-- Aggregate `a`'s segments (its header's byte 1). -/
def kA (rd : Read4) (κ : NodeKind) (w : Asg) (a : ℕ) : ℕ := (byteAt (rd.sgn κ (aggChild κ a) w).π 1).toNat

/-- Aggregate `a`'s sub-slot `i`. -/
def sub (κ : NodeKind) (a i : ℕ) : ℕ := if κ.hasPrev then 1 + i else 4 * a + i

/-- Signed child `σ`'s statement. -/
def stOf (c₁ c₂ : Digest) (σ : ℕ) : Digest := if σ = 0 then c₁ else c₂

/-- Signed child `σ`'s segment count (`0` for a previous node). -/
def kOf (rd : Read4) (κ : NodeKind) (w : Asg) (σ : ℕ) : ℕ := if isAgg κ σ then kA rd κ w (aggOf κ σ) else 0

/-- Verifier slot `v` is active: the previous node's, or a sub-slot below its aggregate's `k`. -/
def Active4 (rd : Read4) (κ : NodeKind) (w : Asg) (v : ℕ) : Prop :=
  (κ.hasPrev = true ∧ v = 0) ∨ ∃ a < nAgg κ, ∃ i < kA rd κ w a, v = sub κ a i

/-- **Slot `v`'s input**: the previous node's `(vk, c₁, π₁)`; a segment's `(vk, cᵢ, πᵢ)` with its
statement `cᵢ = leafStmt eᵢ nᵢ` (`segC`) from its proof's view. -/
def slotIn (rd : Read4) (κ : NodeKind) (vk c₁ : Digest) (w : Asg) (v : ℕ) : Input :=
  if κ.hasPrev = true ∧ v = 0 then ⟨vk, c₁, rd.slotπ κ v w⟩
  else ⟨vk, ((segView (rd.slotπ κ v w)).map segC).getD 0, rd.slotπ κ v w⟩

/-- **The node's residual** (per item; the JOURNAL's §0): what `StmtN4` does not give and the M/L
rows (S-E12b) must certify. -/
structure NodeResid4 {Vseg : SegProgs} {Vnode : NodeProgs} (I : SlotIface4 Vseg Vnode) (rd : Read4)
    (κ : NodeKind) (vk c₁ c₂ : Digest) (w : Asg) : Prop where
  /-- Imports of every active slot (the pack map into M, `vk`, `c`, trace cells, L bits). -/
  imp : ∀ v, Active4 rd κ w v → I.imp κ v w (slotIn rd κ vk c₁ w v) (rd.slotTr κ v w)
  /-- The replay `R` of every active slot. -/
  rep : ∀ v, Active4 rd κ w v → I.rep κ v w (slotIn rd κ vk c₁ w v) (rd.slotTr κ v w)
  /-- The template rows of every active slot. -/
  tpl : ∀ v, Active4 rd κ w v → I.tpl κ v w
  /-- The previous node's slot selects its kind `κ'`, and its proof is a `κ'` node proof. -/
  selP : κ.hasPrev = true → ∃ κ', I.selN κ 0 w κ' ∧ kindOf4 (rd.sgn κ 0 w).π = .node κ'
  /-- The previous node's slot reads signed child 0. -/
  slotP : κ.hasPrev = true → rd.slotπ κ 0 w = (rd.sgn κ 0 w).π ∧ rd.slotTr κ 0 w = (rd.sgn κ 0 w).tr
  /-- An active sub-slot selects its segment's kind. -/
  selA : ∀ a < nAgg κ, ∀ i < kA rd κ w a, ∃ v : SegView,
    segView (rd.slotπ κ (sub κ a i) w) = some v ∧ I.selS κ (sub κ a i) w v.kind
  /-- The signed children's format (`acc`'s word, query and size conjuncts). -/
  pack : ∀ σ < 2, (rd.sgn κ σ w).π.size < 2 ^ 64 ∧ (rd.sgn κ σ w).tr.length ≤ qV4 ∧
    ∀ e ∈ (rd.sgn κ σ w).tr, e.1.size ≤ queryCap
  /-- The chain hashes the child's stream `0x54 ‖ traceBytes tr`. -/
  chainMsg : ∀ σ < 2, chainBytes4 κ σ (kOf rd κ w σ) w = tagTrace :: traceBytes (rd.sgn κ σ w).tr
  /-- `π_A`'s parse: size, kind byte, zero bytes 2–7, its segments are the active sub-slots'. -/
  aggFmt : ∀ a < nAgg κ, (rd.sgn κ (aggChild κ a) w).π.size = 48 + kA rd κ w a * piSizeOf seq4 ∧
    byteAt (rd.sgn κ (aggChild κ a) w).π 0 = aggByte ∧
    bytesAt (rd.sgn κ (aggChild κ a) w).π 2 6 = Vector.replicate 6 0 ∧
    aggSegs (piSizeOf seq4) (kA rd κ w a) (rd.sgn κ (aggChild κ a) w).π =
      (List.range (kA rd κ w a)).map fun i => rd.slotπ κ (sub κ a i) w
  /-- `tr_A` is `V_A`'s trace (R-A′): the active sub-slots' traces in order, the spacer's entry
  `(spacerQ, ans i)` before sub-slot `i ≥ 1`. -/
  aggTr : ∀ a < nAgg κ, ∃ ans, (rd.sgn κ (aggChild κ a) w).tr =
    aggTrace ans ((List.range (kA rd κ w a)).map fun i => rd.slotTr κ (sub κ a i) w)
  /-- `V_A`'s checks against the aggregate's statement `c_A` (the `hashA` block, O-1). -/
  aggChk : ∀ a < nAgg κ, ∃ vs, (aggSegs (piSizeOf seq4) (kA rd κ w a)
      (rd.sgn κ (aggChild κ a) w).π).mapM segView = some vs ∧
    aggChecks (stOf c₁ c₂ (aggChild κ a)) (rdLE64 (rd.sgn κ (aggChild κ a) w).π 8)
      (bytesAt (rd.sgn κ (aggChild κ a) w).π 16 32) vs = true
  /-- **`childOk4`** (R-4-m2): at most `maxK` segments. -/
  kOk : ∀ a < nAgg κ, kA rd κ w a ≤ κ.maxK
  /-- **R-4-m2**: the `k`-gated last block. -/
  aggPad : ∀ a < nAgg κ, AggPad4 κ a (kA rd κ w a) w
  /-- WOTS verifies the digest selected by `k` (the `k`-mux, the digits, the mirrors: O2b). -/
  wots : ∀ σ < 2, SigOk vk (hDig4 κ σ (kOf rd κ w σ) w) (rd.sgn κ σ w).σ = true

/-- **The H side's chain fact** (the BLAKE2s chain over the blocks; 3.x `Stream.blake2s_chain`):
on Z/S truths, a chain whose bytes are `0x54 ‖ traceBytes tr` (and, for an aggregate of `k`
segments, `1 ≤ k ≤ maxK` and `AggPad4`) computes `traceDigest tr`. -/
def DigLemma4 (κ : NodeKind) : Prop :=
  ∀ w σ k tr, σ < 2 → truthZ4 κ w → truthS4 κ w →
    (isAgg κ σ = true → 1 ≤ k ∧ k ≤ κ.maxK ∧ AggPad4 κ (aggOf κ σ) k w) →
    chainBytes4 κ σ k w = tagTrace :: traceBytes tr → hDig4 κ σ k w = traceDigest tr

/-! ## `node_sound4` -/

section Sound
variable {Vseg : SegProgs} {Vnode : NodeProgs}

theorem aggChild_lt (κ : NodeKind) {a : ℕ} (ha : a < nAgg κ) : aggChild κ a < 2 := by
  cases κ <;> simp_all [aggChild, nAgg, NodeKind.hasPrev]

theorem isAgg_aggChild (κ : NodeKind) (a : ℕ) : isAgg κ (aggChild κ a) = true := by
  cases κ <;> simp [isAgg, aggChild, NodeKind.hasPrev]

theorem aggOf_aggChild (κ : NodeKind) {a : ℕ} (ha : a < nAgg κ) : aggOf κ (aggChild κ a) = a := by
  cases κ <;> simp_all [aggOf, aggChild, nAgg, NodeKind.hasPrev]

/-- Every aggregate child is some aggregate's. -/
theorem agg_of_isAgg (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) (h : isAgg κ σ = true) :
    aggOf κ σ < nAgg κ ∧ aggChild κ (aggOf κ σ) = σ := by
  cases κ <;> simp_all [isAgg, aggOf, aggChild, nAgg, NodeKind.hasPrev] <;> omega

theorem sub_active (rd : Read4) (κ : NodeKind) (w : Asg) {a i : ℕ} (ha : a < nAgg κ) (hi : i < kA rd κ w a) :
    Active4 rd κ w (sub κ a i) := .inr ⟨a, ha, i, hi, rfl⟩

theorem slotIn_sub (rd : Read4) (κ : NodeKind) (vk c₁ : Digest) (w : Asg) (a i : ℕ) :
    slotIn rd κ vk c₁ w (sub κ a i) =
      ⟨vk, ((segView (rd.slotπ κ (sub κ a i) w)).map segC).getD 0, rd.slotπ κ (sub κ a i) w⟩ := by
  by_cases hp : κ.hasPrev = true <;> simp [slotIn, sub, hp]

theorem mapM_forall₂4 {l : List Proof} {vs : List SegView} (h : l.mapM segView = some vs) :
    List.Forall₂ (fun p v => segView p = some v) l vs := by
  induction l generalizing vs with
  | nil => simp at h; subst h; exact .nil
  | cons p l ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs', rfl⟩ := h
    exact .cons hv (ih hvs')

variable {I : SlotIface4 Vseg Vnode} {rd : Read4} {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}

/-- **Acceptance of a signed child** from its run: the format (`pack`), the signature over its
trace digest (`wots` and the H side's chain fact `DigLemma4`, with `kOk`/`aggPad` for an
aggregate). -/
theorem sig_of (hS : StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w) (hR : NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : DigLemma4 κ) {σ : ℕ} (hσ : σ < 2) {v : Unit → OProg Bool}
    (hrun : (v ()).runSeq (rd.sgn κ σ w).tr = some true) :
    accWith4 vk (rd.sgn κ σ w) v = true := by
  have hagg : isAgg κ σ = true → 1 ≤ kOf rd κ w σ ∧ kOf rd κ w σ ≤ κ.maxK ∧
      AggPad4 κ (aggOf κ σ) (kOf rd κ w σ) w := fun h => by
    obtain ⟨ha, hc⟩ := agg_of_isAgg κ hσ h
    have hk : kOf rd κ w σ = kA rd κ w (aggOf κ σ) := by simp [kOf, h]
    obtain ⟨vs, hvs, hck⟩ := hR.aggChk _ ha
    refine ⟨?_, hk ▸ hR.kOk _ ha, hk ▸ hR.aggPad _ ha⟩
    have h1 : 1 ≤ vs.length := by
      simp only [aggChecks, Bool.and_eq_true, decide_eq_true_eq] at hck; exact hck.1.1.1.1.2.1
    have h2 := (mapM_forall₂4 hvs).length_eq
    rw [aggSegs, List.length_map, List.length_range] at h2
    rw [hk]; omega
  have hd := hD w σ _ _ hσ hS.1 hS.2.1 hagg (hR.chainMsg σ hσ)
  have hw := hR.wots σ hσ
  rw [hd] at hw
  obtain ⟨h1, h2, h3⟩ := hR.pack σ hσ
  simp only [accWith4, SigOkF_eq, traceDigestF_eq, hw, h1, h2, hrun, decide_true, Bool.true_and,
    Bool.and_true, decide_eq_true_eq]
  exact h3

/-- **An aggregate child is accepted** (`V_A` through `VA_complete`): its parse (`aggFmt`), the
checks (`aggChk`), and every active sub-slot's segment program accepting its trace (`soundS` with
`selA`, `imp`, `rep`, `tpl`), on `tr_A` (`aggTr`: the spacer entries between them). -/
theorem agg_acc (hS : StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w) (hR : NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : DigLemma4 κ) {a : ℕ} (ha : a < nAgg κ) :
    accV4 Vseg Vnode vk (stOf c₁ c₂ (aggChild κ a)) (rd.sgn κ (aggChild κ a) w) = true ∧
      childOk4 κ (rd.sgn κ (aggChild κ a) w).π = true := by
  obtain ⟨hsz, h0, hpad, hsegs⟩ := hR.aggFmt a ha
  obtain ⟨vs, hvs, hck⟩ := hR.aggChk a ha
  have hkind : kindOf4 (rd.sgn κ (aggChild κ a) w).π = .agg := by
    show (if byteAt _ 0 = aggByte then _ else _) = _
    rw [if_pos h0]
  refine ⟨sig_of hS hR hD (aggChild_lt κ ha) ?_, ?_⟩
  · obtain ⟨ans, htr⟩ := hR.aggTr a ha
    rw [V4_agg Vseg Vnode vk _ _ hkind, htr]
    refine VA_complete hsz h0 hpad hvs hck ?_ ans
    change List.Forall₂ _ (segProgs Vseg vk (aggSegs (piSizeOf seq4) (kA rd κ w a) _) vs) _
    rw [hsegs] at hvs ⊢
    have hF := mapM_forall₂4 hvs
    have hl := hF.length_eq
    simp only [List.length_map, List.length_range] at hl
    refine List.forall₂_iff_get.2 ⟨by simp [segProgs, ← hl], fun i h₁ h₂ => ?_⟩
    have hi : i < kA rd κ w a := by simpa using h₂
    have hv := (List.forall₂_iff_get.1 hF).2 i (by simpa using hi) (by rw [← hl]; exact hi)
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at hv
    obtain ⟨v, hv', hsel⟩ := hR.selA a ha i hi
    rw [hv] at hv'
    cases hv'
    simp only [segProgs, List.get_eq_getElem, List.getElem_map, List.getElem_zip, List.getElem_range]
    have hact := sub_active rd κ w ha hi
    have := I.soundS κ (sub κ a i) w _ _ _ hS.2.2.1 hS.2.2.2.1 hsel (hR.imp _ hact) (hR.rep _ hact)
      (hR.tpl _ hact)
    rw [slotIn_sub] at this
    simpa [hv] using this
  · unfold childOk4; rw [hkind]
    exact decide_eq_true (hR.kOk a ha)

/-- **The previous node is accepted**: its slot's kind `κ'` (`selP`), the node program `Vnode κ'`
accepting its trace (`soundN`), the format and the signature. -/
theorem prev_acc (hS : StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w) (hR : NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : DigLemma4 κ) (hp : κ.hasPrev = true) :
    accV4 Vseg Vnode vk c₁ (rd.sgn κ 0 w) = true ∧ childOk4 κ (rd.sgn κ 0 w).π = true := by
  obtain ⟨κ', hsel, hkind⟩ := hR.selP hp
  obtain ⟨hπ, htr⟩ := hR.slotP hp
  have hact : Active4 rd κ w 0 := .inl ⟨hp, rfl⟩
  have hin : slotIn rd κ vk c₁ w 0 = ⟨vk, c₁, (rd.sgn κ 0 w).π⟩ := by simp [slotIn, hp, hπ]
  refine ⟨sig_of hS hR hD (by norm_num) ?_, ?_⟩
  · rw [V4_node Vseg Vnode vk _ _ hkind]
    have := I.soundN κ 0 w _ _ _ hS.2.2.1 hS.2.2.2.1 hsel (hR.imp _ hact) (hR.rep _ hact) (hR.tpl _ hact)
    rw [hin, htr] at this
    exact this
  · unfold childOk4; rw [hkind]

/-- **`node_sound4`** (§4.3 at revision 4.1): the node's truths `StmtN4`, the residual
`NodeResid4` and the H side's chain fact give a witness of the relation for `nodeStmt c₁ c₂`:
both read signed children are accepted (`accV4`), and both pass `childOk4 κ`. -/
theorem node_sound4 (hS : StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w) (hR : NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : DigLemma4 κ) :
    Rel (accV4 Vseg Vnode vk) (nodeStmt c₁ c₂) (.node c₁ c₂ (rd.sgn κ 0 w) (rd.sgn κ 1 w)) ∧
      ∀ σ < 2, childOk4 κ (rd.sgn κ σ w).π = true := by
  have hch : ∀ σ < 2, accV4 Vseg Vnode vk (stOf c₁ c₂ σ) (rd.sgn κ σ w) = true ∧
      childOk4 κ (rd.sgn κ σ w).π = true := fun σ hσ => by
    by_cases hA : isAgg κ σ = true
    · obtain ⟨ha, hc⟩ := agg_of_isAgg κ hσ hA
      rw [← hc]; exact agg_acc hS hR hD ha
    · have hp : κ.hasPrev = true ∧ σ = 0 := by
        cases κ <;> simp_all [isAgg, NodeKind.hasPrev]
      obtain ⟨hp, rfl⟩ := hp
      exact prev_acc hS hR hD hp
  exact ⟨⟨rfl, (hch 0 (by norm_num)).1, (hch 1 (by norm_num)).1⟩, fun σ hσ => (hch σ hσ).2⟩

end Sound

/-! ## The node laws of `FRSoundness4Frame` -/

section Laws
variable {Vseg : SegProgs} {Vnode : NodeProgs}

/-- **`NodeSoundLog` from the node circuit**: if an accepted node run on a good log carries the key
and its truths `StmtN4` hold on some `f⁽⁰⁾` for `c = nodeStmt c₁ c₂` (`hRun`: the PIOP's per-run
soundness, X4/S-G), and the truths give the residual (`hRes`: S-E12b's rows), then the statement has
a witness (`node_sound4`). -/
theorem nodeSoundLog4_of (I : SlotIface4 Vseg Vnode) (rd : Read4) {vk : Digest} {Good : Log → Prop}
    (hD : ∀ κ, DigLemma4 κ)
    (hRun : ∀ κ L c π, Good L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
      X.vkOf π = vk ∧ ∃ w c₁ c₂, c = nodeStmt c₁ c₂ ∧ StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w)
    (hRes : ∀ κ w c₁ c₂, StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w → NodeResid4 I rd κ vk c₁ c₂ w) :
    NodeSoundLog Vnode vk Good (Rel (accV4 Vseg Vnode vk)) := fun κ L c π hG hk h => by
  obtain ⟨hvk, w, c₁, c₂, rfl, hS⟩ := hRun κ L c π hG hk h
  exact ⟨hvk, _, (node_sound4 hS (hRes κ w c₁ c₂ hS) (hD κ)).1⟩

/-- **`NodeExtLog`** for an extractor that, on an accepted node run on a good log with the run's
key, returns a witness whenever one exists (S-H3's interface, a parameter: `hE`). -/
theorem nodeExtLog4_of (I : SlotIface4 Vseg Vnode) (rd : Read4) {vk : Digest} {Good : Log → Prop}
    {E : Digest → Proof → Log → Option Wit} (hD : ∀ κ, DigLemma4 κ)
    (hRun : ∀ κ L c π, Good L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
      X.vkOf π = vk ∧ ∃ w c₁ c₂, c = nodeStmt c₁ c₂ ∧ StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w)
    (hRes : ∀ κ w c₁ c₂, StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w → NodeResid4 I rd κ vk c₁ c₂ w)
    (hE : ∀ κ L c π, Good L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
      X.vkOf π = vk → (∃ w, Rel (accV4 Vseg Vnode vk) c w) →
        ∃ w, E c π L = some w ∧ Rel (accV4 Vseg Vnode vk) c w) :
    NodeExtLog Vnode vk Good E (Rel (accV4 Vseg Vnode vk)) := fun κ L c π hG hk h => by
  obtain ⟨hvk, hw⟩ := nodeSoundLog4_of I rd hD hRun hRes κ L c π hG hk h
  exact hE κ L c π hG hk h hvk hw

/-- **At the concrete verifier** (`VC4`, `acc_eqC4`): `NodeSoundLog` with the submission's `acc`,
and `NodeExtLog` at the specification extractor `E4 S.acc` (`nodeExt_E4`), the forms `ks4_of`/
`ks4_E4` take. -/
theorem nodeLaws4C (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ)
    (S : Submission) (vk : Digest) (hV : S.V = VC4 impl₀ implN cells) (hq : S.qV = qV4)
    {Good : Log → Prop} (I : SlotIface4 (VsegC impl₀) (VnodeC implN cells)) (rd : Read4)
    (hD : ∀ κ, DigLemma4 κ)
    (hRun : ∀ κ L c π, Good L → kindOf4 π = .node κ → (VnodeC implN cells κ vk c π).runLog L = some true →
      X.vkOf π = vk ∧ ∃ w c₁ c₂, c = nodeStmt c₁ c₂ ∧ StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w)
    (hRes : ∀ κ w c₁ c₂, StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w → NodeResid4 I rd κ vk c₁ c₂ w) :
    NodeSoundLog (VnodeC implN cells) vk Good (Rel (S.acc vk)) ∧
      NodeExtLog (VnodeC implN cells) vk Good (E4 S.acc) (Rel (S.acc vk)) := by
  have h : NodeSoundLog (VnodeC implN cells) vk Good (Rel (S.acc vk)) := by
    rw [acc_eqC4 impl₀ implN cells S hV hq]; exact nodeSoundLog4_of I rd hD hRun hRes
  exact ⟨h, nodeExt_E4 hq h⟩

end Laws

/-! ## The PIOP's node parameters (P4a's `zlm4`) -/

/-- **`zlm4 indN4 etN4` meets `IndKinds`**: a node has no `chain` block. -/
theorem zlm4_indKinds : (Snd.P4a.zlm4 indN4 etN4).IndKinds := fun κ t => by
  cases κ with
  | seg σ => exact ⟨fun h => by simp [Snd.CKind.isNode] at h, fun _ j hj => by
      simp [Snd.P4a.zlm4, hj]⟩
  | node ν => exact ⟨fun _ => indN4_chain ν t, fun h => by simp [Snd.CKind.isNode] at h⟩

/-- The node indicators and targets are bits (`ZLM4.Bits`' node half). -/
theorem indN4_etN4_bits (κ : NodeKind) (j : Fin 9) (t : ℕ) (p : Fin (2 ^ 14)) :
    (indN4 κ j t = 0 ∨ indN4 κ j t = 1) ∧ (etN4 κ t p = 0 ∨ etN4 κ t p = 1) := by
  refine ⟨by unfold indN4; split_ifs <;> simp, ?_⟩
  unfold etN4 NodeT.tgtE NodeT.bF
  split <;> (try split) <;> simp

/-- **P4b's `hcells`** at `cells4` (the `cells` parameter of `single_B4`, and of `VC4`'s node
finals `nodeFinP κ (cells κ)`). -/
theorem hcells4P4b : ∀ ν, (cells4 ν).length = 9 ∧ ∀ c ∈ cells4 ν, c < 2 ^ Snd.P4b.ncR ν :=
  fun ν => ⟨(hcells4 ν).1, (hcells4 ν).2.1⟩

/-! ## `hfit` per node kind (P4b's O1 over S-E12b's indexed rows) -/

/-- **`hfit4`**: per node kind, the indexed M rows fit `evalM`'s `e2R κ` row and `ncR κ` cell
variables with distinct indices (P4b F1). Parametric in S-E12b's rows. -/
def HFit4 (irows : NodeKind → List (ℕ × Row)) : Prop :=
  ∀ κ, Snd.P4b.RowsFitI (irows κ) (Snd.P4b.e2R κ) (Snd.P4b.ncR κ)

/-- **The generator's certificate**: strictly increasing indices (by construction) give the
distinct indices `RowsFitI` asks; with the last index and every cell in range. -/
theorem rowsFitI_of_sorted {rows : List (ℕ × Row)} {a b : ℕ}
    (hs : (rows.map Prod.fst).Pairwise (· < ·)) (ha : ∀ p ∈ rows, p.1 < 2 ^ a)
    (hb : ∀ p ∈ rows, ∀ t ∈ p.2.a ++ p.2.b ++ p.2.c, t.1 < 2 ^ b) : Snd.P4b.RowsFitI rows a b :=
  ⟨hs.imp fun h => Nat.ne_of_lt h, ha, hb⟩

/-- `HFit4` from the per-kind certificates. -/
theorem hfit4_of {irows : NodeKind → List (ℕ × Row)}
    (hs : ∀ κ, ((irows κ).map Prod.fst).Pairwise (· < ·))
    (ha : ∀ κ, ∀ p ∈ irows κ, p.1 < 2 ^ Snd.P4b.e2R κ)
    (hb : ∀ κ, ∀ p ∈ irows κ, ∀ t ∈ p.2.a ++ p.2.b ++ p.2.c, t.1 < 2 ^ Snd.P4b.ncR κ) : HFit4 irows :=
  fun κ => rowsFitI_of_sorted (hs κ) (ha κ) (hb κ)

/-! ## Controls -/

/-- (−) `PubCells4` is not trivial: the zero assignment fails it (the `one` cell must be `1`). -/
theorem not_pubCells4_zero (κ : NodeKind) (vk c₁ c₂ : Digest) : ¬ PubCells4 κ (fun _ => 0) vk c₁ c₂ := by
  intro h
  have := congrArg List.head? h
  simp [cells4, Node.pubVals] at this

/-- (+/−) **The reserve's cells** (revision 4.4.2): 52 for `N2`/`N4` (slot 0's E2 and E4
challenges, `evalM`'s outputs, the kind element), none for `N8`; inside `f` and slot 0's M region,
distinct, and disjoint from the nine public cells. -/
theorem rsvCells_ctl : (Rev4.rsvCells .N2).length = 60 ∧ (Rev4.rsvCells .N4).length = 60 ∧
    Rev4.rsvCells .N8 = [] ∧
    (∀ κ, ∀ c ∈ Rev4.rsvCells κ, κ.oneCell ≤ c ∧ c < κ.oneCell + 2 ^ 20 ∧ c < 2 ^ (κ.m - 7)) ∧
    (∀ κ, (Rev4.rsvCells κ).Nodup ∧ ∀ c ∈ Rev4.rsvCells κ, c ∉ cells4 κ) := by
  refine ⟨rfl, rfl, rfl, fun κ => ?_, fun κ => ?_⟩ <;> cases κ <;> decide

/-- (+) `AggPad4` holds on the zero assignment (every bit `0`: the links and the padding). -/
theorem aggPad4_zero (κ : NodeKind) (a k : ℕ) : AggPad4 κ a k (fun _ => 0) := by
  have h0 : ∀ b, zN4 (fun _ => 0) b = fun _ => 0 := fun b => by
    funext p; simp [zN4, zW4, unpack, bitF_zero]
  simp only [AggPad4, h0, implies_true, and_self]

/-- (−) `AggPad4` binds the padding: a nonzero padding bit of the final block fails it. -/
theorem not_aggPad4 {κ : NodeKind} {a k x : ℕ} {w : Asg}
    (hx : 8 * (aggB k - 64 * (aggL k - 1)) ≤ x) (hx' : x < 512)
    (h : zN4 w (finBlk κ (aggChild κ a) k) (512 + x) ≠ 0) : ¬ AggPad4 κ a k w :=
  fun hp => h (hp.2 x hx hx')

/-- (−) `NodeResid4` binds `childOk4` (R-4-m2): an `N2` node whose aggregate has 3 segments has no
residual. -/
theorem not_resid_N2_k3 {Vseg : SegProgs} {Vnode : NodeProgs} {I : SlotIface4 Vseg Vnode} {rd : Read4}
    {vk c₁ c₂ : Digest} {w : Asg} (hk : kA rd .N2 w 0 = 3) : ¬ NodeResid4 I rd .N2 vk c₁ c₂ w := fun hR => by
  have := hR.kOk 0 (by decide); rw [hk] at this; exact absurd this (by decide)

/-- (+/−) The active slots: an `N2` node with a 2-segment aggregate uses slots 0, 1, 2; an `N8`
node's slot 5 is aggregate 1's second sub-slot (and inactive if that aggregate has one segment and
aggregate 0 at most `maxK = 4`, as `kOk` asks). -/
theorem active4_ctrl (rd : Read4) (w : Asg) (h2 : kA rd .N2 w 0 = 2) (h1 : kA rd .N8 w 1 = 1)
    (h0 : kA rd .N8 w 0 ≤ 4) :
    Active4 rd .N2 w 0 ∧ Active4 rd .N2 w 2 ∧ ¬ Active4 rd .N2 w 3 ∧ sub .N8 1 1 = 5 ∧
      ¬ Active4 rd .N8 w 5 := by
  refine ⟨.inl ⟨rfl, rfl⟩, .inr ⟨0, by decide, 1, by omega, rfl⟩, ?_, rfl, ?_⟩
  · rintro (⟨-, h⟩ | ⟨a, ha, i, hi, h⟩)
    · cases h
    · simp only [nAgg, NodeKind.hasPrev, if_true] at ha
      obtain rfl : a = 0 := by omega
      simp only [sub, NodeKind.hasPrev, if_true] at h; omega
  · rintro (⟨h, -⟩ | ⟨a, ha, i, hi, h⟩)
    · cases h
    · simp only [nAgg, NodeKind.hasPrev, Bool.false_eq_true, if_false] at ha
      simp only [sub, NodeKind.hasPrev, Bool.false_eq_true, if_false] at h
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · simp at h; omega
      · rw [h1] at hi; simp at h; omega

end N4c
end FR
