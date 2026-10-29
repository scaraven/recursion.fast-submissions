-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.3; R-4-m2; stage S-N2, residual 4 of `ks_rev4F`).
-- The 3.x analogue is `FRNodeSoundA` (`NodeResid`, O2/O2b).
import FRNodeRead4W

/-!
# `hRes` item by item: `StmtN4` and the circuit's gaps give `NodeResid4` at `I4`, `rd4`

`resid4_of` proves `N4c.NodeResid4 (I4 …) (rd4 pf)` from the node's truths `StmtN4` (at
`lRows4`, `nodeIRows4`) and **`Gap4`**, which lists, field by field, what no row of the circuit
binds. Item by item:

| `NodeResid4` field | Source |
|---|---|
| `tpl` | the M rows (`slotRows_of`; `one = 1` from `PubCells4` rules out the rejecting rows) |
| `rep` | `True` in `I4`: the circuit has no replay `R` |
| `selP`, `selA` (selectors) | the link and activity rows (S-E12c's `selP_sel`, `selA_sel`, with `ActK` from the reader's `kAct`: `actK_kAct`) |
| `selP`, `selA` (kind byte) | **gap** `kindN`, `kindS`: no row ties the selector copies to the child proof's byte 0 |
| `slotP`, `aggTr`, `aggFmt`, `kOk` | the reader (`rd4`): `π_A`'s header with the circuit's `k`, fitted slot proofs |
| `pack` | the reader: sizes, trace lengths `≤ qV4` (`traces_le_qV`), queries `≤ queryCap` (`itemsOf_qlen_le`, one `decide` over `seq4`'s phase shapes) |
| `imp` | **gap**: the run on the trace, the auxiliary/import/foreign facts and the statement fact (`SlotImp`): no pack map, no `R` |
| `chainMsg` | `chainMsg_of_wf` from **gap** `wf`: the stream's tag byte, the items' length words and (R-A′) the spacers' length words and queries (constant bytes at fixed stream offsets) are not pinned by any target or row |
| `aggChk` | **gap**: no row checks `V_A`'s checks against `c_A` (statement, `1 ≤ k ≤ 4`, lengths, sum, end, chaining) |
| `aggPad` | **gap**: no row links the candidate final block `F_{a,k}` (R-4-m2) to the main chain at `k` |
| `wots` | **gap**: the WOTS rows (the `k`-mux, the digits, the mirrors) are not built (O2b) |
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## Facts from the statement's rows -/

theorem one_of_pubCells {κ : NodeKind} {w : Asg} {vk c₁ c₂ : Digest} (h : N4c.PubCells4 κ w vk c₁ c₂) :
    w κ.oneCell = 1 := by
  unfold N4c.PubCells4 at h
  have := congrArg List.head? h
  simpa [N4c.cells4, Node.pubVals] using this

/-- On `one = 1`, the M rows are the prototypes' (the rejecting row fails). -/
theorem protoFit_of {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) : ProtoFit := by
  by_contra hF
  refine rejectRows_ctl κ w hone fun p hp => hE p ?_
  rw [nodeIRows4, if_neg hF]; exact hp

theorem map_snd_zipIdx_map' {α : Type*} (l : List α) (f : α × ℕ → ℕ) :
    (l.zipIdx.map fun p => (f p, p.1)).map Prod.snd = l :=
  (map_snd_zipIdx_map l f id).trans (List.map_id _)

/-- **A slot's link rows hold** (they are in the M rows). -/
theorem linkRows_hold {κ : NodeKind} {σ : ℕ} {w : Asg} (hF : ProtoFit) (hσ : σ < κ.vslots)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) : ∀ r ∈ linkRows4 κ σ, r.Holds w := by
  intro r hr
  have hm : r ∈ (linkIRows4 κ σ).map Prod.snd := by
    rw [linkIRows4, map_snd_zipIdx_map']; exact hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
  exact hE p (mem_node_link hF hσ hp)

/-- **The reader's segment count meets `ActK`**: the activity rows make the sub-slots below the
first inactive one active, the first sub-slot is active, and the activity is a bit. -/
theorem actK_kAct {κ : NodeKind} {a : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (ha : a < N4c.nAgg κ)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w) :
    ActK κ a (kAct κ a w) w := by
  classical
  have h2 : 2 ≤ κ.maxK := by cases κ <;> decide
  have hspec := Nat.find_spec (⟨κ.maxK, Or.inl rfl⟩ : ∃ i, i = κ.maxK ∨ (selSum κ (N4c.sub κ a i)).ev w ≠ 1)
  have hmin := fun j (hj : j < kAct κ a w) =>
    Nat.find_min (⟨κ.maxK, Or.inl rfl⟩ : ∃ i, i = κ.maxK ∨ (selSum κ (N4c.sub κ a i)).ev w ≠ 1) hj
  have hle := kAct_le κ a w
  change _ ∨ _ at hspec
  have h0 : (selSum κ (N4c.sub κ a 0)).ev w = 1 := by
    obtain ⟨hv, hx, -, -⟩ := sub_facts κ ha (by omega : 0 < κ.maxK)
    exact act_first hone hv hL (hk 0 (by omega)) (Or.inr hx)
  have hpos : 1 ≤ kAct κ a w := by
    by_contra h
    have hz : kAct κ a w = 0 := by omega
    unfold kAct at hz; rw [hz] at hspec
    rcases hspec with h | h
    · omega
    · exact h h0
  refine ⟨hpos, hle, ?_, fun hlt => ?_⟩
  · have := hmin (kAct κ a w - 1) (by omega)
    simp only [not_or, ne_eq, not_not] at this
    exact this.2
  · unfold kAct at hlt ⊢
    rcases hspec with h | h
    · omega
    · obtain ⟨hv, -, -, -⟩ := sub_facts κ ha hlt
      rcases selSum_bit hone hv hL (hk _ hlt) with h' | h'
      · exact h'
      · exact absurd h' h

/-! ## Format facts of the read proofs -/

theorem kindOf4_of {π : Proof} {ν : NodeKind} (hb : byteAt π 0 = ν.byte) (hs : π.size = piSizeOf seq4) :
    kindOf4 π = .node ν := by
  unfold kindOf4
  dsimp only
  rw [hb, NodeKind.ofByte?_byte]
  dsimp only
  rw [if_pos hs]
  cases ν <;> rfl

theorem segView_of {π : Proof} {κ : SegKind} (hb : byteAt π 0 = κ.byte) :
    ∃ v, segView π = some v ∧ v.kind = κ :=
  ⟨⟨κ, bytesAt π 16 32, bytesAt π 49 32, rdLE64 π 81⟩,
    by simp only [segView, hb, SegKind.ofByte?_byte, Option.map_some], rfl⟩

theorem segTr_length (κ : NodeKind) (σ k i : ℕ) (w : Asg) : (segTr κ σ k i w).length = 8783 := by
  rw [segTr, Read.readItems_length, itemsOf_seq4_length]

theorem slotTr4_length (κ : NodeKind) (v : ℕ) (w : Asg) : (slotTr4 κ v w).length = 8783 := by
  unfold slotTr4; split_ifs <;> exact segTr_length ..

theorem slotPf_length (pf : Trace → Proof) (κ : NodeKind) (v : ℕ) (w : Asg) :
    (slotPf pf κ v w).length = piSizeOf seq4 := fitL_length _ _

theorem aggPf_size (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) :
    (aggPf pf κ a w).size = 48 + kAct κ a w * piSizeOf seq4 := by
  simp only [aggPf, ByteArray.size, List.size_toArray, List.length_append, aggHdr_length,
    List.length_flatten, List.map_map, Function.comp_def, slotPf_length, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]

/-- **An aggregate's read trace length** (R-A′): `k` segments and `k − 1` spacer entries. -/
theorem aggTr_length (κ : NodeKind) (k : ℕ) (f : ℕ → ℕ) (ans : ℕ → Digest) (w : Asg) :
    (aggTrace ans ((List.range k).map fun i => slotTr4 κ (f i) w)).length = k * 8783 + (k - 1) :=
  aggTrace_length ans _ 8783 (fun i => slotTr4_length κ (f i) w) k

/-- A `seq4` phase shape's largest query (3.x's `shapeQ` on `Sh`). -/
def shQ4 : Sh → ℕ
  | .seed => 119
  | .absorb _ len => 40 + len
  | .squeezes _ _ => 40
  | .uni _ => 40 + uniBytes
  | .rounds _ _ _ inK => 40 + roundBytes inK
  | .queries i => max (8 + colBytes i) 72

theorem sh_qlen4 (lv : ℕ → Level) (sh : Sh) : ∀ it ∈ sh.itemsL lv, it.qlen ≤ shQ4 sh := by
  intro it hit
  cases sh with
  | seed => simp [Sh.itemsL] at hit; subst hit; rfl
  | absorb f len => simp [Sh.itemsL] at hit; subst hit; simp [Item.qlen, shQ4]
  | squeezes n ch =>
    simp only [Sh.itemsL, List.mem_replicate] at hit; rw [hit.2]; simp [Item.qlen, shQ4]
  | uni f =>
    simp only [Sh.itemsL, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> simp [Item.qlen, shQ4] <;> omega
  | rounds f n deg inK =>
    simp only [Sh.itemsL, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp [Item.qlen, shQ4] <;> omega
  | queries i =>
    simp only [Sh.itemsL, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
    simp only [posItemsL, List.mem_cons, List.mem_map, List.mem_range] at hl
    rcases hl with rfl | ⟨h, -, rfl⟩ <;> simp [Item.qlen, shQ4]

/-- Every `seq4` phase's largest query is within `queryCap` (its shape parameters only). -/
theorem phasesOf_shQ4 : (phasesOf seq4).all (fun p => decide (shQ4 p.2 ≤ queryCap)) = true := by
  rw [seq4_eq]; decide +kernel

/-- **Every `seq4` item's query is within `queryCap`.** -/
theorem itemsOf_qlen_le : ∀ it ∈ itemsOf seq4, it.qlen ≤ queryCap := by
  intro it hit
  simp only [itemsOf, List.mem_flatMap] at hit
  obtain ⟨p, hp, hit⟩ := hit
  have := List.all_eq_true.1 phasesOf_shQ4 p hp
  simp only [decide_eq_true_eq] at this
  exact (sh_qlen4 _ _ it hit).trans this

theorem slotTr4_qcap (κ : NodeKind) (v : ℕ) (w : Asg) : ∀ e ∈ slotTr4 κ v w, e.1.size ≤ queryCap := by
  intro e he
  have h : ∀ σ k i, ∀ e ∈ segTr κ σ k i w, e.1.size ≤ queryCap := fun σ k i e he => by
    obtain ⟨it, hit, hle⟩ := Snd.readItems_qlen _ _ _ e he
    exact hle.trans (itemsOf_qlen_le it hit)
  unfold slotTr4 at he; split_ifs at he <;> exact h _ _ _ e he

/-- **A read child's queries are within `queryCap`.** -/
theorem sgn4_qcap (pf : Trace → Proof) (κ : NodeKind) (σ : ℕ) (w : Asg) :
    ∀ e ∈ (sgn4 pf κ σ w).tr, e.1.size ≤ queryCap := by
  intro e he
  unfold sgn4 at he
  split_ifs at he
  · rcases mem_aggTrace he with ⟨i, -, he⟩ | ⟨i, rfl⟩
    · exact slotTr4_qcap κ _ w e he
    · show spacerQ.size ≤ queryCap
      rw [spacerQ_size]; decide
  · exact slotTr4_qcap κ 0 w e he

/-! ## The chain's message from the stream's constant bytes -/

/-- Signed child `σ`'s segment count as read (`1` for a previous node). -/
noncomputable def nSeg (κ : NodeKind) (σ : ℕ) (w : Asg) : ℕ :=
  if N4c.isAgg κ σ then kAct κ (N4c.aggOf κ σ) w else 1

theorem slotA_sub (κ : NodeKind) {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) :
    slotA κ (N4c.sub κ a i) = a := by
  cases κ <;> simp only [slotA, N4c.sub, N4c.nAgg, NodeKind.hasPrev, NodeKind.maxK, if_true,
    Bool.false_eq_true, if_false] at ha hi ⊢ <;> omega

theorem slotTr4_sub (κ : NodeKind) {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) (w : Asg) :
    slotTr4 κ (N4c.sub κ a i) w = segTr κ (N4c.aggChild κ a) (kAct κ a w) i w := by
  obtain ⟨-, hx, hp, -⟩ := sub_facts κ ha hi
  rw [slotTr4, if_neg (by simp [hp]), slotA_sub κ ha hi, hx]

/-- **`NodeResid4.chainMsg` from the streams' constant bytes**: if signed child `σ`'s stream starts
with the tag and has every item's length word and (R-A′) every spacer's length word and query in
place, it is `0x54 ‖ traceBytes` of the read trace. -/
theorem chainMsg_of_wf (pf : Trace → Proof) {κ : NodeKind} {σ : ℕ} {w : Asg} (hσ : σ < 2)
    (h0 : (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w).head? = some tagTrace)
    (hw : ∀ i < nSeg κ σ w, WfAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (1 + i * N4c.strideB)
      (itemsOf seq4) ∧ (0 < i → SpAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (i * N4c.strideB - 128))) :
    N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w = tagTrace :: traceBytes ((rd4 pf).sgn κ σ w).tr := by
  have hlen : ∀ k, (N4c.chainBytes4 κ σ k w).length = N4c.streamB κ σ k := fun k =>
    Stream.streamBytes_length _ _
  by_cases hA : N4c.isAgg κ σ = true
  · obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
    have hk : N4c.kOf (rd4 pf) κ w σ = kAct κ (N4c.aggOf κ σ) w := by
      rw [N4c.kOf, if_pos hA, kA_rd4 pf κ ha]
    have hn : nSeg κ σ w = kAct κ (N4c.aggOf κ σ) w := by rw [nSeg, if_pos hA]
    rw [hk] at h0 hw ⊢
    rw [hn] at hw
    rw [stream_of_wf (by rw [hlen, N4c.streamB, if_pos hA]) h0 (fun i hi => (hw i hi).1)
      (fun i hi => (hw i hi).2)]
    congr 2
    conv_rhs => rw [← hc]
    show _ = (sgn4 pf κ (N4c.aggChild κ (N4c.aggOf κ σ)) w).tr
    rw [sgn4_agg pf κ ha]
    dsimp only
    rw [hc]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [slotTr4_sub κ ha (lt_of_lt_of_le hi' (kAct_le κ _ w)) w, hc]
    rfl
  · have hp : κ.hasPrev = true ∧ σ = 0 := by
      cases κ <;> simp_all [N4c.isAgg, NodeKind.hasPrev]
    obtain ⟨hp, rfl⟩ := hp
    have hk : N4c.kOf (rd4 pf) κ w 0 = 0 := by rw [N4c.kOf, if_neg hA]
    have hn : nSeg κ 0 w = 1 := by rw [nSeg, if_neg hA]
    rw [hk] at h0 hw ⊢
    rw [hn] at hw
    rw [stream_of_wf (n := 1) (by rw [hlen, N4c.streamB, if_neg hA]; rfl) h0 (fun i hi => (hw i hi).1)
      (fun i hi => (hw i hi).2)]
    simp only [rd4, sgn4, if_neg hA, slotTr4, isPrevSlot, hp, Bool.true_and, beq_self_eq_true, if_true,
      List.range_one, List.map_cons, List.map_nil, aggTrace, aggTrAt, List.nil_append, List.append_nil,
      zero_mul, add_zero]
    rfl

/-! ## The gaps -/

/-- **What no row of the 4.1 node circuit binds** (S-N2's soundness gap), field by field, for the
reader `rd4 pf` and the slot interface `I4`'s `imp` (`SlotImp`). -/
structure Gap4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (pf : Trace → Proof) (κ : NodeKind)
    (vk c₁ c₂ : Digest) (w : Asg) : Prop where
  /-- Every active slot's run on its trace, its auxiliary/import/foreign facts and the statement
  fact (the pack map, the `input` alias, the replay `R`). -/
  imp : ∀ v, N4c.Active4 (rd4 pf) κ w v →
    SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)
  /-- The previous node's proof has the selected node kind's byte. -/
  kindN : κ.hasPrev = true → ∀ ι, SelOk (slotAsg κ 0 w) (protoP 0) ι →
    byteAt ((rd4 pf).sgn κ 0 w).π 0 = (nodeAt ι).byte
  /-- An active sub-slot's proof has the selected segment kind's byte. -/
  kindS : ∀ a < N4c.nAgg κ, ∀ i < kAct κ a w, ∀ ι, SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι →
    byteAt ((rd4 pf).slotπ κ (N4c.sub κ a i) w) 0 = (segAt ι).byte
  /-- H's streams' constant bytes (for `NodeResid4.chainMsg`): the tag `0x54` at byte 0, each read
  item's 8-byte length word `enc64 |q|` at its offset, and (R-A′) before each later segment the
  spacer's length word and query `enc64 89 ‖ spacerQ`. -/
  wf : ∀ σ < 2, (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w).head? = some tagTrace ∧
    ∀ i < nSeg κ σ w, WfAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (1 + i * N4c.strideB)
      (itemsOf seq4) ∧ (0 < i → SpAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (i * N4c.strideB - 128))
  /-- `NodeResid4.aggChk`: `V_A`'s checks against `c_A`. -/
  aggChk : ∀ a < N4c.nAgg κ, ∃ vs, (aggSegs (piSizeOf seq4) (N4c.kA (rd4 pf) κ w a)
      ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π).mapM segView = some vs ∧
    aggChecks (N4c.stOf c₁ c₂ (N4c.aggChild κ a)) (rdLE64 ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 8)
      (bytesAt ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 16 32) vs = true
  /-- `NodeResid4.aggPad` (R-4-m2): the `k`-gated final block. -/
  aggPad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf) κ w a) w
  /-- `NodeResid4.wots`: WOTS on the `k`-selected H digest. -/
  wots : ∀ σ < 2, SigOk vk (N4c.hDig4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) ((rd4 pf).sgn κ σ w).σ = true

/-! ## `hRes` -/

section Resid
variable {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν))
  (pf : Trace → Proof) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}

theorem vslots_pos (κ : NodeKind) : 0 < κ.vslots := by cases κ <;> decide

theorem active_lt {v : ℕ} (h : N4c.Active4 (rd4 pf) κ w v) : v < κ.vslots := by
  rcases h with ⟨-, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · exact vslots_pos κ
  · rw [kA_rd4 pf κ ha] at hi
    exact (sub_facts κ ha (lt_of_lt_of_le hi (kAct_le κ a w))).1

theorem isAgg_zero {κ : NodeKind} (hp : κ.hasPrev = true) : N4c.isAgg κ 0 = false := by
  simp [N4c.isAgg, hp]

theorem protoOf_zero {κ : NodeKind} (hp : κ.hasPrev = true) : protoOf κ 0 = 0 := by
  simp [protoOf, isPrevSlot, hp]

/-- **`hRes`**: the node's truths and the circuit's gaps give `NodeResid4` at `I4`, `rd4 pf`. -/
theorem resid4_of (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hG : Gap4 impl₀ base pf κ vk c₁ c₂ w) : N4c.NodeResid4 (I4 impl₀ base hT₀ hT) (rd4 pf) κ vk c₁ c₂ w := by
  obtain ⟨-, -, hL, hE, hP⟩ := hS
  have hone := one_of_pubCells hP
  have hF := protoFit_of hone hE
  have hk : ∀ a < N4c.nAgg κ, N4c.kA (rd4 pf) κ w a = kAct κ a w := fun a ha => kA_rd4 pf κ ha w
  have hlk : ∀ a < N4c.nAgg κ, ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w :=
    fun a ha i hi => linkRows_hold hF (sub_facts κ ha hi).1 hE
  refine ⟨hG.imp, fun _ _ => trivial, fun v hv => slotRows_of hone (active_lt pf hv) hE, ?_, ?_, ?_, ?_,
    fun σ hσ => chainMsg_of_wf pf hσ (hG.wf σ hσ).1 (hG.wf σ hσ).2, ?_, ?_, hG.aggChk, ?_, hG.aggPad, hG.wots⟩
  · -- selP
    intro hp
    obtain ⟨ι, hι⟩ := selP_sel hone hp hL (linkRows_hold hF (vslots_pos κ) hE)
    rw [protoOf_zero hp] at hι
    refine ⟨nodeAt ι, ⟨by simp [isPrevSlot, hp], ι, rfl, hι⟩, kindOf4_of (hG.kindN hp ι hι) ?_⟩
    simp only [rd4, sgn4, isAgg_zero hp, Bool.false_eq_true, ite_false, ByteArray.size, List.size_toArray,
      slotPf_length]
  · -- slotP
    intro hp
    simp only [rd4, sgn4, isAgg_zero hp, Bool.false_eq_true, ite_false, and_self]
  · -- selA
    intro a ha i hi
    rw [hk a ha] at hi
    obtain ⟨ι, hι⟩ := selA_sel hone ha hL (hlk a ha) (actK_kAct hone ha hL (hlk a ha)) i hi
    obtain ⟨-, -, hp, -⟩ := sub_facts κ ha (lt_of_lt_of_le hi (kAct_le κ a w))
    rw [protoOf_seg hp] at hι
    obtain ⟨v, hv, hk'⟩ := segView_of (hG.kindS a ha i hi ι hι)
    exact ⟨v, hv, hp, ι, hk'.symm, hι⟩
  · -- pack
    intro σ hσ
    refine ⟨?_, ?_, sgn4_qcap pf κ σ w⟩
    · by_cases hA : N4c.isAgg κ σ = true
      · obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
        rw [← hc]
        simp only [rd4, sgn4_agg pf κ ha, aggPf_size, piSizeOf_seq4]
        have := kAct_le κ (N4c.aggOf κ σ) w
        have h4 : κ.maxK ≤ 4 := by cases κ <;> decide
        omega
      · simp only [rd4, sgn4, hA, Bool.false_eq_true, ite_false, ByteArray.size, List.size_toArray,
          slotPf_length, piSizeOf_seq4]
        norm_num
    · have hq := traces_spacers_le_qV
      rw [itemsOf_seq4_length] at hq
      by_cases hA : N4c.isAgg κ σ = true
      · obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
        rw [← hc]
        simp only [rd4, sgn4_agg pf κ ha, aggTr_length]
        have := kAct_le κ (N4c.aggOf κ σ) w
        have h4 : κ.maxK ≤ 4 := by cases κ <;> decide
        have h48 := Nat.mul_le_mul_right 8783 (this.trans h4)
        exact le_trans (Nat.add_le_add h48 (Nat.sub_le_sub_right (this.trans h4) 1)) hq
      · simp only [rd4, sgn4, hA, Bool.false_eq_true, ite_false, slotTr4_length]
        omega
  · -- aggFmt
    intro a ha
    rw [hk a ha]
    simp only [rd4, sgn4_agg pf κ ha]
    refine ⟨aggPf_size pf κ a w, ?_, ?_, ?_⟩
    · simp [aggPf, aggHdr]
    · refine Vector.ext fun i hi => ?_
      simp only [bytesAt, Vector.getElem_ofFn, Vector.getElem_replicate, aggPf, byteAt_mk, aggHdr]
      interval_cases i <;> rfl
    · rw [aggPf, aggSegs_flat _ _ (aggHdr_length _ _ _)
        (fun s hs => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
          exact slotPf_length pf κ _ w) (by simp), List.map_map]
      rfl
  · -- aggTr
    intro a ha
    rw [hk a ha]
    exact ⟨spAns κ (N4c.aggChild κ a) (kAct κ a w) w, by simp only [rd4, sgn4_agg pf κ ha]⟩
  · -- kOk
    intro a ha
    rw [hk a ha]; exact kAct_le κ a w

end Resid

end N4s
end FR
