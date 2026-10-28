-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2 digest chains, R-4-m2; stage S-E12a).
-- 3.x template: `FRBlockStream.stream_sound`/`stream_traceDigest`.
import FRNodeCircuit4

/-!
# The H side of `node_sound4`: the digest chains compute the trace digests (`DigLemma4`)

**`digLemma4 κ`**: on the node's Z and S truths, a signed child's chain whose stream (`chainBytes4`,
with the final block `F_{a,k}` for an aggregate of `k < maxK` segments) is `0x54 ‖ traceBytes tr`
carries `traceDigest tr` at its final block's `h_out` (`hDig4`), given for an aggregate
`1 ≤ k ≤ maxK` and R-4-m2's `AggPad4` (the final block's `h_in` link and zero padding).

* **`chain_digest`**: `Stream.stream_sound` with per-block compressions as hypotheses (the blocks'
  targets differ: block 0 is `streamStart`, a final block `F_{a,k}` sits in the tail).
* The per-block facts: the main chain's targets (`main_tgt`), the final block's (`fin_tgt`: in
  every case `streamTarget L (N − 1)` with `L` the stream's bytes), the links (`chainLk4` and
  `AggPad4`'s `h_in` link), the padding (`AggPad4`'s zeros).

With it, **`node_sound4'`** and **`nodeLaws4C'`** drop the hypothesis `DigLemma4`.
-/

namespace FR
namespace N4c
open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit Rev4 Circ
open FR.Block FR.Stream

/-! ## The chain argument with per-block compressions -/

/-- **A digest chain** (`Stream.stream_sound` with the compressions as hypotheses): blocks starting
at `h0`, each the compression of its `h_in` and message with the stream's counter and flag, linked
`h_out(i) = h_in(i + 1)`, padded past `L` bytes, carry the BLAKE2s digest of their `L` bytes. -/
theorem chain_digest (L : ℕ) (W : ℕ → Pos → Bool) (hstart : hIn (W 0) = chainState (Stream.streamBytes W L) 0)
    (hc : ∀ i < nBlocks L, hOut (W i) =
      compress (hIn (W i)) (block (msgBytes (W i))) (ctrAt L i).toUInt64 (flagAt L i) 0)
    (hl : ∀ i, i + 1 < nBlocks L → ∀ j < 256, W (i + 1) (pos j) = W i (pos (256 + j)))
    (hpad : Padded W L) :
    readDigest (W (nBlocks L - 1)) 256 = blake2sDigest (Stream.streamBytes W L) := by
  set B := Stream.streamBytes W L with hB
  have hBl : B.length = L := Stream.streamBytes_length W L
  have hs : ∀ j, chainState B (j + 1) =
      compress (chainState B j) (block (B.drop (64 * j))) (ctrAt L j).toUInt64 (flagAt L j) 0 :=
    fun j ↦ by rw [chainState, hBl]
  have key : ∀ i < nBlocks L, hIn (W i) = chainState B i ∧ hOut (W i) = chainState B (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro h0'
      refine ⟨hstart, ?_⟩
      rw [hc 0 h0', hstart, msg_eq hpad h0', ← hB]
      exact (hs 0).symm
    | succ i ih =>
      intro hi
      have hin : hIn (W (i + 1)) = chainState B (i + 1) := hIn_of_bits fun j hj ↦ by
        rw [hl i hi j hj, ← hOut_bit (W i) hj, (ih (by omega)).2]
      refine ⟨hin, ?_⟩
      rw [hc _ hi, hin, msg_eq hpad hi, ← hB]
      exact (hs (i + 1)).symm
  have hN : nBlocks L - 1 + 1 = nBlocks L := by simp [nBlocks]
  rw [readDigest_hOut, (key _ (by simp [nBlocks])).2, hN, blake2s_chain, hBl]

/-! ## Bits -/

theorem lift_bitsB4 (w : Asg) (blk : ℕ) : liftBlock F (bitsB4 w blk) = zB4 w blk := by
  have key : ∀ x : F, (x = 0 ∨ x = 1) → ofBool F (decide (x = 1)) = x := by
    rintro x (rfl | rfl) <;> simp [ofBool]
  funext k
  exact key (zB4 w blk k) (by simp only [zB4, zW4]; exact unpack_boolean _ _)

theorem bitsB4_pos (w : Asg) (blk : ℕ) {j : ℕ} (hj : j < 2 ^ 14) :
    bitsB4 w blk (pos j) = decide (zN4 w blk j = 1) := by
  unfold bitsB4 zB4 zN4; rw [pos_val hj]

/-- A block's Z truth on its Boolean bits. -/
theorem holds_of_Z {κ : NodeKind} {w : Asg} (hZ : truthZ4 κ w) {blk : ℕ} (hb : blk < κ.blocks)
    {tgt : Target} (ht : nodeKind4 κ blk = some tgt) :
    HoldsE (blockR1CS tgt) (targetVal F tgt) (liftBlock F (bitsB4 w blk)) := by
  rw [lift_bitsB4]; exact hZ blk hb tgt ht

theorem readByte_zero {w : Pos → Bool} {b : ℕ} (h : ∀ i < 8, w (pos (b + i)) = false) : readByte w b = 0 := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [readByte_getLsbD _ _ hi, h i hi]
  simp

/-! ## The chain's blocks and targets -/

theorem mem_lt {κ : NodeKind} {iv : TIv} (h : iv ∈ nodeLayout4 κ) {blk : ℕ} (hk : iv.mem blk = true) :
    blk < κ.blocks := by
  have := layout_bounds κ h; simp only [TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hk; omega

/-- The main chain's block `0` (`streamStart`) and blocks `1 … chLen − 1` (`stream`, the full
chain's counters). -/
theorem main_tgt (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) {i : ℕ} (hi : i < chLen κ σ) :
    chBase κ σ + i < κ.blocks ∧ nodeKind4 κ (chBase κ σ + i) =
      some (if i = 0 then Kinds.streamStart.target else streamTarget (chBytes κ σ) i) := by
  have hmem := chainIvs_mem κ hσ
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have hm := hmem ⟨.streamStart, chBase κ σ, chBase κ σ + 1, fun _ => some Kinds.streamStart.target⟩
      (by simp [chainIvs])
    have hk : TIv.mem ⟨.streamStart, chBase κ σ, chBase κ σ + 1, fun _ => some Kinds.streamStart.target⟩
        (chBase κ σ + 0) = true := by simp [TIv.mem]
    exact ⟨mem_lt hm hk, by rw [tgt_of_mem hm hk]; simp⟩
  · have hm := hmem ⟨.stream, chBase κ σ + 1, chBase κ σ + chLen κ σ,
      fun o => some (streamTarget (chBytes κ σ) (o + 1))⟩ (by simp [chainIvs])
    have hk : TIv.mem ⟨.stream, chBase κ σ + 1, chBase κ σ + chLen κ σ,
        fun o => some (streamTarget (chBytes κ σ) (o + 1))⟩ (chBase κ σ + i) = true := by
      simp [TIv.mem]; omega
    refine ⟨mem_lt hm hk, ?_⟩
    rw [tgt_of_mem hm hk, if_neg (by omega)]
    simp only
    congr 2; omega

theorem tailIvs_mem (κ : NodeKind) {a : ℕ} (ha : a < nAgg κ) : ∀ iv ∈ tailIvs κ a, iv ∈ nodeLayout4 κ :=
  fun iv h => by
    simp only [nodeLayout4, List.mem_append, List.mem_flatMap, List.mem_range]
    exact .inl (.inr ⟨a, ha, h⟩)

/-- Hypotheses on the segment count `k` (vacuous for a previous node). -/
def KOk (κ : NodeKind) (σ k : ℕ) : Prop := isAgg κ σ = true → 1 ≤ k ∧ k ≤ κ.maxK

theorem aggL_mono {k k' : ℕ} (h : k ≤ k') : aggL k ≤ aggL k' := by
  rw [aggL_eq, aggL_eq]; exact aggChainLen_le h

theorem aggL_ge {k : ℕ} (hk : 1 ≤ k) : 2 ≤ aggL k :=
  le_trans (by decide) (aggL_mono hk)

/-- **The stream's shape**: `nBlocks L = streamL`, at least two blocks, inside the main chain. -/
theorem stream_shape (κ : NodeKind) (σ k : ℕ) (hk : KOk κ σ k) :
    nBlocks (streamB κ σ k) = streamL κ σ k ∧ 2 ≤ streamL κ σ k ∧ streamL κ σ k ≤ chLen κ σ := by
  unfold streamB streamL chLen
  by_cases hA : isAgg κ σ = true
  · obtain ⟨h1, h2⟩ := hk hA
    simp only [hA, if_true]
    exact ⟨aggL_nBlocks k, aggL_ge h1, aggL_mono h2⟩
  · simp only [hA, if_false, Bool.false_eq_true]
    exact ⟨by decide, by decide, le_rfl⟩

/-- **The final block's target is the stream's last**: `streamTarget L (N − 1)` (a candidate block
`F_{a,k}`, or the main chain's last at `k = maxK` and for a previous node). -/
theorem fin_tgt (κ : NodeKind) {σ k : ℕ} (hσ : σ < 2) (hk : KOk κ σ k) :
    finBlk κ σ k < κ.blocks ∧
      nodeKind4 κ (finBlk κ σ k) = some (streamTarget (streamB κ σ k) (streamL κ σ k - 1)) := by
  obtain ⟨-, h2, hle⟩ := stream_shape κ σ k hk
  by_cases hF : isAgg κ σ = true ∧ k < κ.maxK
  · obtain ⟨hA, hlt⟩ := hF
    obtain ⟨ha, hc⟩ := agg_of_isAgg κ hσ hA
    have h1 := (hk hA).1
    set a := aggOf κ σ
    have hm := tailIvs_mem κ ha ⟨.stream, finB κ a + (k - 1), finB κ a + (k - 1) + 1,
      fun _ => some (streamTarget (aggB (k - 1 + 1)) (aggL (k - 1 + 1) - 1))⟩
      (by simp only [tailIvs, List.mem_append, List.mem_map, List.mem_range]
          exact .inl ⟨k - 1, by omega, rfl⟩)
    have hfb : finBlk κ σ k = finB κ a + (k - 1) := by simp [finBlk, hA, hlt, a]
    have hk' : TIv.mem ⟨.stream, finB κ a + (k - 1), finB κ a + (k - 1) + 1,
        fun _ => some (streamTarget (aggB (k - 1 + 1)) (aggL (k - 1 + 1) - 1))⟩ (finBlk κ σ k) = true := by
      rw [hfb]; simp [TIv.mem]
    refine ⟨mem_lt hm hk', ?_⟩
    rw [tgt_of_mem hm hk', Nat.sub_add_cancel h1]
    simp [streamB, streamL, hA]
  · have hfb : finBlk κ σ k = chBase κ σ + (chLen κ σ - 1) := by
      simp only [finBlk, if_neg hF]; omega
    have hL : streamL κ σ k = chLen κ σ ∧ streamB κ σ k = chBytes κ σ := by
      unfold streamL streamB chLen chBytes
      by_cases hA : isAgg κ σ = true
      · have hkm : k = κ.maxK := by
          have := hk hA; have : ¬ k < κ.maxK := fun h => hF ⟨hA, h⟩; omega
        simp [hA, hkm]
      · simp [hA]
    obtain ⟨hb, ht⟩ := main_tgt κ hσ (i := chLen κ σ - 1) (by omega)
    rw [hfb]
    refine ⟨hb, ?_⟩
    rw [ht, if_neg (by omega), hL.1, hL.2]

/-! ## `DigLemma4` -/

theorem ctr_mid {X L i : ℕ} (hX : i + 1 ≠ nBlocks X) (hL : i + 1 ≠ nBlocks L) :
    ctrAt X i = ctrAt L i ∧ flagAt X i = flagAt L i := by
  simp [ctrAt, flagAt, hX, hL]

/-- **The H side's chain fact.** -/
theorem digLemma4 (κ : NodeKind) : DigLemma4 κ := by
  intro w σ k tr hσ hZ hS hagg hmsg
  have hk : KOk κ σ k := fun h => ⟨(hagg h).1, (hagg h).2.1⟩
  obtain ⟨hN, h2, hle⟩ := stream_shape κ σ k hk
  set L := streamB κ σ k
  set W := chainW4 κ σ k w
  have hWi : ∀ i, i + 1 < streamL κ σ k → W i = bitsB4 w (chBase κ σ + i) := fun i hi => by
    simp only [W, chainW4, blkOf, if_neg (show i + 1 ≠ streamL κ σ k by omega)]
  have hWl : W (streamL κ σ k - 1) = bitsB4 w (finBlk κ σ k) := by
    simp only [W, chainW4, blkOf, if_pos (show streamL κ σ k - 1 + 1 = streamL κ σ k by omega)]
  -- the links
  have hlink : ∀ y, chainLk4 κ y = true → ∀ j < 256, bitsB4 w (y + 1) (pos j) = bitsB4 w y (pos (256 + j)) :=
    fun y hy j hj => by
      rw [bitsB4_pos w _ (by omega), bitsB4_pos w _ (by omega), hS.1 y hy j hj]
  have hlk : ∀ i, i + 1 < chLen κ σ → chainLk4 κ (chBase κ σ + i) = true := fun i hi => by
    unfold chainLk4 chBase
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl
    · simp only [zero_mul, zero_add]; simp [hi]
    · simp only [one_mul]; simp; omega
  have hdig : hDig4 κ σ k w = readDigest (W (nBlocks L - 1)) 256 := by rw [hN, hWl]; rfl
  rw [hdig, traceDigest, ← hmsg]
  refine chain_digest L W ?_ ?_ ?_ ?_
  · -- block 0 is `streamStart`: `h_in = h0`
    rw [hWi 0 (by omega)]
    obtain ⟨hb, ht⟩ := main_tgt κ hσ (i := 0) (by omega)
    rw [if_pos rfl] at ht
    exact Kinds.Kind.hIn_eq_h0 (κ := Kinds.streamStart) rfl (holds_of_Z hZ hb ht)
  · intro i hi
    rw [hN] at hi
    by_cases hlast : i + 1 = streamL κ σ k
    · obtain ⟨hb, ht⟩ := fin_tgt κ hσ hk
      have hi' : i = streamL κ σ k - 1 := by omega
      subst hi'
      rw [hWl]
      exact block_sound (holds_of_Z hZ hb ht)
    · rw [hWi i (by omega)]
      obtain ⟨hb, ht⟩ := main_tgt κ hσ (i := i) (by omega)
      have hX : nBlocks (chBytes κ σ) = chLen κ σ := by
        unfold chBytes chLen; split_ifs
        · exact aggL_nBlocks _
        · decide
      by_cases h0 : i = 0
      · subst h0
        rw [if_pos rfl] at ht
        rw [Kinds.Kind.block_sound (κ := Kinds.streamStart) (holds_of_Z hZ hb ht)]
        simp [ctrAt, flagAt, hN, show ¬ 1 = streamL κ σ k by omega, Kinds.streamStart, Stream.flagOf]
      · rw [if_neg h0] at ht
        rw [block_sound (holds_of_Z hZ hb ht)]
        obtain ⟨e1, e2⟩ := ctr_mid (X := chBytes κ σ) (L := L) (i := i) (by omega) (by omega)
        rw [e1, e2]
  · intro i hi j hj
    rw [hN] at hi
    rw [hWi i (by omega)]
    by_cases hlast : i + 2 = streamL κ σ k
    · have hw : W (i + 1) = bitsB4 w (finBlk κ σ k) := by rw [← hWl]; congr 1; omega
      rw [hw]
      by_cases hF : isAgg κ σ = true ∧ k < κ.maxK
      · obtain ⟨hA, hlt⟩ := hF
        obtain ⟨ha, hc⟩ := agg_of_isAgg κ hσ hA
        have hp := ((hagg hA).2.2.1 hlt).1 j hj
        simp only [hc] at hp
        rw [bitsB4_pos w _ (by omega), bitsB4_pos w _ (by omega), hp]
        have : aggL k = streamL κ σ k := by simp [streamL, hA]
        rw [this, show chBase κ σ + streamL κ σ k - 2 = chBase κ σ + i by omega]
      · have hfb : finBlk κ σ k = chBase κ σ + i + 1 := by
          have : streamL κ σ k = chLen κ σ := by
            unfold streamL chLen
            by_cases hA : isAgg κ σ = true
            · have hkm : k = κ.maxK := by
                have := hk hA; have : ¬ k < κ.maxK := fun h => hF ⟨hA, h⟩; omega
              simp [hA, hkm]
            · simp [hA]
          simp only [finBlk, if_neg hF]; omega
        rw [hfb]
        exact hlink _ (hlk i (by omega)) j hj
    · rw [hWi (i + 1) (by omega), ← add_assoc]
      exact hlink _ (hlk i (by omega)) j hj
  · intro p hp1 hp2
    rw [hN] at hp2
    have hq : p / 64 = streamL κ σ k - 1 := by
      have : streamL κ σ k - 1 ≤ p / 64 := by
        by_cases hA : isAgg κ σ = true
        · have hL : L = aggB k := by simp [L, streamB, hA]
          have hl : streamL κ σ k = aggL k := by simp [streamL, hA]
          rw [hl]; rw [hL] at hp1; simp only [aggL, aggB] at hp1 ⊢; omega
        · have hL : L = segB := by simp [L, streamB, hA]
          have hl : streamL κ σ k = cLen := by simp [streamL, hA]
          rw [hL] at hp1; rw [hl] at hp2; simp only [segB, cLen] at hp1 hp2; omega
      omega
    rw [hq, hWl]
    by_cases hA : isAgg κ σ = true
    · obtain ⟨ha, hc⟩ := agg_of_isAgg κ hσ hA
      have hpad := (hagg hA).2.2.2
      simp only [hc] at hpad
      have hL : L = aggB k := by simp [L, streamB, hA]
      have hl : streamL κ σ k = aggL k := by simp [streamL, hA]
      apply readByte_zero
      intro b hb
      rw [hl] at hq
      rw [bitsB4_pos w _ (by simp only [msgBase]; omega), show msgBase + 8 * (p % 64) + b = 512 + (8 * (p % 64) + b) by
        simp only [msgBase]; omega, hpad _ (by rw [hL] at hp1; omega) (by omega)]
      decide
    · -- a previous node's stream fills its last block
      have hL : L = segB := by simp [L, streamB, hA]
      have hl : streamL κ σ k = cLen := by simp [streamL, hA]
      rw [hL] at hp1; rw [hl] at hp2; simp only [segB, cLen] at hp1 hp2; omega

/-! ## `node_sound4` and the node laws without the chain hypothesis -/

/-- **`node_sound4`**, the H side discharged (`digLemma4`). -/
theorem node_sound4' {Vseg : SegProgs} {Vnode : NodeProgs} {I : SlotIface4 Vseg Vnode} {rd : Read4}
    {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hS : StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w) (hR : NodeResid4 I rd κ vk c₁ c₂ w) :
    Rel (accV4 Vseg Vnode vk) (nodeStmt c₁ c₂) (.node c₁ c₂ (rd.sgn κ 0 w) (rd.sgn κ 1 w)) ∧
      ∀ σ < 2, childOk4 κ (rd.sgn κ σ w).π = true :=
  node_sound4 hS hR (digLemma4 κ)

/-- **The node laws at the concrete verifier** from the PIOP's per-run truths (`hRun`) and the
residual (`hRes`) alone. -/
theorem nodeLaws4C' (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ)
    (S : Submission) (vk : Digest) (hV : S.V = VC4 impl₀ implN cells) (hq : S.qV = qV4)
    {Good : Log → Prop} (I : SlotIface4 (VsegC impl₀) (VnodeC implN cells)) (rd : Read4)
    (hRun : ∀ κ L c π, Good L → kindOf4 π = .node κ → (VnodeC implN cells κ vk c π).runLog L = some true →
      X.vkOf π = vk ∧ ∃ w c₁ c₂, c = nodeStmt c₁ c₂ ∧ StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w)
    (hRes : ∀ κ w c₁ c₂, StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w → NodeResid4 I rd κ vk c₁ c₂ w) :
    NodeSoundLog (VnodeC implN cells) vk Good (Rel (S.acc vk)) ∧
      NodeExtLog (VnodeC implN cells) vk Good (E4 S.acc) (Rel (S.acc vk)) :=
  nodeLaws4C impl₀ implN cells S vk hV hq I rd digLemma4 hRun hRes

end N4c
end FR
