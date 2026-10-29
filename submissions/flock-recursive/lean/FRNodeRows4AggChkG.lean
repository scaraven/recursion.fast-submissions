-- New for `flock-recursive` (PACK-4.4.1 §1.3 `input`/`hashStmt` rows, §4.3, §7 B4; stage B4, track L-circ).
import FRNodeRows4AggChkS
import FRNodeRows4PackSound

/-!
# `Gap4R.aggChk` from the node rows

**`aggChk_of_rows`**: on the node's truths (`StmtN4` at `lRows4`, `nodeIRows4`), with the proof
decoder's positional facts `PfHdr pf` (byte 0) and `PfView pf` (the view's fields), every
aggregate meets `V_A`'s checks (`aggChecks`) against its statement `c_A`:

* the views exist (`kindS_of_rows`) and read the sub-slots' stream elements (`view_sub`):
  `start = dg2 (6, 7)`, `h = sh1 (13, 14, 15)`, `n = n8 (15)`;
* `c_A = leafStmt e n` with `π_A`'s `e`, `n` (`stmt_A`): the `hashA` block `cAB` (Z truth,
  `hashA_leafStmt`) hashes `tagLeaf ‖ e ‖ enc64 n`, and its `h_out` is `c_A` (`PubCells4`). No row;
* `1 ≤ k ≤ 4` (`actK_kAct`); the lengths, the sum, the end and the chaining from the check rows
  (`FRNodeRows4AggChkS`).

**`gap4_of_rowsI`**: `StmtN4`, `PfHdr pf`, `PfView pf` and `Gap4R.imp` give S-N2's `Gap4`: B4 leaves
`imp` as the node circuit's only gap.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Finset

/-! ## The proof decoder's view fields -/

/-- **What `pf` must do with the header and the statement** (A.5's `reassemble`, fields 0 and 1):
the proof's bytes `0 … 47` (`hdr`) are the seed query's bytes `71 … 118`, its bytes `48 … 175`
(`stmt`) the second query's message (bytes `40 … 167`). A segment view reads `hdr.pub` (`16 … 47`)
and `stmt[1 … 41)`. -/
def PfView (pf : Trace → Proof) : Prop :=
  ∀ e₀ e₁ tr, (∀ j < 48, byteAt (pf (e₀ :: e₁ :: tr)) j = byteAt e₀.1 (71 + j)) ∧
    ∀ j < 128, byteAt (pf (e₀ :: e₁ :: tr)) (48 + j) = byteAt e₁.1 (40 + j)

theorem byteAt_slotPfP (pf : Trace → Proof) (κ : NodeKind) (v : ℕ) (w : Asg) {p : ℕ} (hp : p < piSizeOf seq4) :
    byteAt (⟨(slotPf pf κ v w).toArray⟩ : Proof) p = byteAt (pf (slotTr4 κ v w)) p := by
  rw [byteAt_mk, slotPf, fitL]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hp, List.getElem?_append]
  conv_rhs => rw [show pf (slotTr4 κ v w) = ⟨(pf (slotTr4 κ v w)).data.toList.toArray⟩ from rfl, byteAt_mk]
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (not_lt.1 h), List.getElem?_replicate]
    split_ifs <;> rfl

theorem itemsOf_seq4_two : ∃ rest, itemsOf seq4 = .seed :: .absorb 128 :: rest := ⟨_, rfl⟩

theorem entry_byte (B : List UInt8) (o : ℕ) (it : Item) {j : ℕ} (hj : j < it.qlen) :
    byteAt (Read.entryAt B o it).1 j = B.getD (o + 8 + j) 0 := by
  show byteAt ⟨((B.drop (o + 8)).take it.qlen).toArray⟩ j = _
  rw [byteAt_mk, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]

theorem fb_eq (a : F) {r : ℕ} (hr : r < 16) : fb a r = (F.toBytes a)[r] := by
  unfold fb; simp only [Nat.mod_eq_of_lt hr]

/-- **Byte `p` of sub-slot `i`'s segment** is byte `p mod 16` of its element `p / 16`. -/
theorem seg_byte {κ : NodeKind} {a k i : ℕ} (w : Asg) (hi : i < k) {p : ℕ} (hp : p < 400) :
    (N4c.chainBytes4 κ (N4c.aggChild κ a) k w).getD (i * N4c.strideB + p) 0 =
      fb (w (sE κ (N4c.aggChild κ a) i (p / 16))) (p % 16) := by
  have h := segi_elem w (N4c.isAgg_aggChild κ a) hi (e := p / 16) (r := p % 16) (Nat.mod_lt _ (by norm_num))
    (by simp only [N4c.segB]; omega)
  rw [show i * N4c.strideB + 16 * (p / 16) + p % 16 = i * N4c.strideB + p by omega] at h
  rw [h, fb_eq _ (Nat.mod_lt _ (by norm_num))]
  rfl

theorem fb_congr_mod (a : F) {k k' : ℕ} (h : k % 16 = k' % 16) : fb a k = fb a k' := by
  rw [← fb_mod a k, ← fb_mod a k', h]

section View
variable {pf : Trace → Proof} {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}

/-- Sub-slot `i` of aggregate `a` reads its segment of the aggregate's stream. -/
theorem slotTr_sub {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) :
    slotTr4 κ (N4c.sub κ a i) w = segTr κ (N4c.aggChild κ a) (kAct κ a w) i w := by
  obtain ⟨-, hx, hpv, -⟩ := sub_facts κ ha hi
  simp only [slotTr4, hpv, Bool.false_eq_true, if_false, slotA_sub κ ha hi, hx]

/-- **An active sub-slot's view** reads its stream: kind from the selector, start from elements
`6, 7`, end from `13–15`, length from `15`. -/
theorem view_sub (hpf : PfHdr pf) (hpv : PfView pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    {a : ℕ} (ha : a < N4c.nAgg κ) {i : ℕ} (hi : i < kAct κ a w) {ι : Kind}
    (hι : SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι) :
    segView ((rd4 pf).slotπ κ (N4c.sub κ a i) w) = some ⟨segAt ι,
      dg2 (w (sE κ (N4c.aggChild κ a) i 6)) (w (sE κ (N4c.aggChild κ a) i 7)),
      sh1 (w (sE κ (N4c.aggChild κ a) i 13)) (w (sE κ (N4c.aggChild κ a) i 14)) (w (sE κ (N4c.aggChild κ a) i 15)),
      n8 (w (sE κ (N4c.aggChild κ a) i 15))⟩ := by
  have hkm := kAct_le κ a w
  have hb0 := kindS_of_rows pf hpf hS a ha i hi ι hι
  set σ := N4c.aggChild κ a
  set B := N4c.chainBytes4 κ σ (kAct κ a w) w
  obtain ⟨rest, hr⟩ := itemsOf_seq4_two
  have htr : slotTr4 κ (N4c.sub κ a i) w = Read.entryAt B (1 + i * N4c.strideB) .seed ::
      Read.entryAt B (1 + i * N4c.strideB + 159) (.absorb 128) :: Read.readItems B (1 + i * N4c.strideB + 159 + 208) rest := by
    rw [slotTr_sub ha (by omega), segTr, hr]; rfl
  obtain ⟨hv1, hv2⟩ := hpv (Read.entryAt B (1 + i * N4c.strideB) .seed)
    (Read.entryAt B (1 + i * N4c.strideB + 159) (.absorb 128)) (Read.readItems B (1 + i * N4c.strideB + 159 + 208) rest)
  have hps : 89 ≤ piSizeOf seq4 := by rw [piSizeOf_seq4]; norm_num
  -- the proof's bytes `16 … 47` and `49 … 88`
  have hP1 : ∀ j < 32, byteAt ((rd4 pf).slotπ κ (N4c.sub κ a i) w) (16 + j) =
      fb (w (sE κ σ i ((96 + j) / 16))) ((96 + j) % 16) := fun j hj => by
    show byteAt (⟨(slotPf pf κ _ w).toArray⟩ : Proof) _ = _
    rw [byteAt_slotPfP pf κ _ w (by omega), htr, hv1 (16 + j) (by omega),
      entry_byte _ _ _ (by simp [Item.qlen]; omega),
      show 1 + i * N4c.strideB + 8 + (71 + (16 + j)) = i * N4c.strideB + (96 + j) by ring, seg_byte w hi (by omega)]
  have hP2 : ∀ j < 40, byteAt ((rd4 pf).slotπ κ (N4c.sub κ a i) w) (49 + j) =
      fb (w (sE κ σ i ((209 + j) / 16))) ((209 + j) % 16) := fun j hj => by
    show byteAt (⟨(slotPf pf κ _ w).toArray⟩ : Proof) _ = _
    rw [byteAt_slotPfP pf κ _ w (by omega), htr, show 49 + j = 48 + (1 + j) by ring, hv2 (1 + j) (by omega),
      entry_byte _ _ _ (by simp [Item.qlen]; omega),
      show 1 + i * N4c.strideB + 159 + 8 + (40 + (1 + j)) = i * N4c.strideB + (209 + j) by ring,
      seg_byte w hi (by omega)]
  simp only [segView, hb0, SegKind.ofByte?_byte, Option.map_some, Option.some.injEq, SegView.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · refine Vector.ext fun j hj => ?_
    rw [bytesAt, Vector.getElem_ofFn, hP1 j hj, dg2, Vector.getElem_ofFn, catByte]
    simp only [Fin.val_mk]
    refine (fb_congr_mod _ (show (96 + j) % 16 % 16 = j % 16 by omega)).trans ?_
    congr 1
    rcases (by omega : j / 16 = 0 ∨ j / 16 = 1) with h | h
    · rw [h, show (96 + j) / 16 = 6 by omega]; rfl
    · rw [h, show (96 + j) / 16 = 7 by omega]; rfl
  · refine Vector.ext fun j hj => ?_
    rw [bytesAt, Vector.getElem_ofFn, hP2 j (by omega), sh1, Vector.getElem_ofFn, catByte]
    simp only [Fin.val_mk]
    refine (fb_congr_mod _ (show (209 + j) % 16 % 16 = (1 + j) % 16 by omega)).trans ?_
    congr 1
    rcases (by omega : (1 + j) / 16 = 0 ∨ (1 + j) / 16 = 1 ∨ (1 + j) / 16 = 2) with h | h | h
    · rw [h, show (209 + j) / 16 = 13 by omega]; rfl
    · rw [h, show (209 + j) / 16 = 14 by omega]; rfl
    · rw [h, show (209 + j) / 16 = 15 by omega]; rfl
  · rw [rdLE64, n8, lsum_range]
    refine sum_congr rfl fun t ht => ?_
    have ht := mem_range.1 ht
    rw [show 81 + t = 49 + (32 + t) by ring, hP2 _ (by omega), show (209 + (32 + t)) / 16 = 15 by omega]
    congr 2
    exact fb_congr_mod _ (by omega)

end View

/-! ## The aggregate's statement: `c_A = leafStmt e n` -/

theorem hA_get (κ : NodeKind) (a : ℕ) (w : Asg) {p : ℕ} (hp : p < 41) :
    (hA κ a w).getD p 0 = fb (w (hc (N4c.cAB κ a) (4 + p / 16))) (p % 16) := by
  rw [hA, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
    Option.map_some, Option.getD_some, Nat.mod_eq_of_lt (show p < 64 by omega),
    show Blake2sCircuit.msgBase + 8 * p = 8 * (64 + p) by rw [show Blake2sCircuit.msgBase = 512 from rfl]; ring,
    readByte_hc w _ (by omega),
    show (64 + p) / 16 = 4 + p / 16 by omega]
  exact fb_congr_mod _ (by omega)

theorem hAe_eq (κ : NodeKind) (a : ℕ) (w : Asg) :
    hAe κ a w = sh1 (w (hc (N4c.cAB κ a) 4)) (w (hc (N4c.cAB κ a) 5)) (w (hc (N4c.cAB κ a) 6)) := by
  refine Vector.ext fun j hj => ?_
  rw [hAe, Vector.getElem_ofFn, hA_get κ a w (by omega), sh1, Vector.getElem_ofFn, catByte]
  simp only [Fin.val_mk]
  refine (fb_mod _ _).trans ?_
  congr 1
  rcases (by omega : (1 + j) / 16 = 0 ∨ (1 + j) / 16 = 1 ∨ (1 + j) / 16 = 2) with h | h | h <;> rw [h] <;> rfl

theorem hAn_eq (κ : NodeKind) (a : ℕ) (w : Asg) : hAn κ a w = n8 (w (hc (N4c.cAB κ a) 6)) := by
  rw [hAn, n8, lsum_range]
  refine sum_congr rfl fun t ht => ?_
  have ht := mem_range.1 ht
  rw [hA_get κ a w (by omega), show (33 + t) / 16 = 2 by omega]
  congr 2
  exact fb_congr_mod _ (by omega)

theorem ofListLE_sum : ∀ l : List UInt8,
    CompPoly.Bytes.ofListLE l = ∑ t ∈ range l.length, (l.getD t 0).toNat * 256 ^ t
  | [] => rfl
  | d :: l => by
    rw [CompPoly.Bytes.ofListLE_cons, ofListLE_sum l, List.length_cons, sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [Nat.add_comm]; congr 1
    refine sum_congr rfl fun t _ => by ring

/-- `hA`'s last eight bytes are `enc64 hAn`. -/
theorem hA_drop (κ : NodeKind) (a : ℕ) (w : Asg) : (hA κ a w).drop 33 = enc64 (hAn κ a w) := by
  have hl : ((hA κ a w).drop 33).length = 8 := by simp [hA, Stream.streamBytes_length]
  have hn : hAn κ a w = CompPoly.Bytes.ofListLE ((hA κ a w).drop 33) := by
    rw [ofListLE_sum, hl, hAn, lsum_range]
    refine sum_congr rfl fun t _ => ?_
    simp [List.getD_eq_getElem?_getD]
  rw [hn, Snd.enc64_toListLE, ← hl, CompPoly.Bytes.toListLE_ofListLE]

/-- **`hashA`'s message is `tagLeaf ‖ hAe ‖ enc64 hAn`** (its first byte is the kind's tag). -/
theorem hA_eq (κ : NodeKind) (a : ℕ) (w : Asg) (h0 : (hA κ a w).getD 0 0 = tagLeaf) :
    hA κ a w = tagLeaf :: (hAe κ a w).toList ++ enc64 (hAn κ a w) := by
  have hl : (hA κ a w).length = 41 := by simp [hA, Stream.streamBytes_length]
  conv_lhs => rw [← List.take_append_drop 33 (hA κ a w)]
  rw [hA_drop]
  congr 1
  refine List.ext_getElem (by simp [hl]) fun p h₁ h₂ => ?_
  rw [List.getElem_take, ← List.getD_eq_getElem _ 0]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [h0, List.getElem_cons_zero]
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [List.getElem_cons_succ, Vector.getElem_toList]
    unfold hAe
    rw [Vector.getElem_ofFn]
    congr 1; simp only [Fin.val_mk]; omega


/-- `cAB` is a `hashA` block of the node. -/
theorem cAB_tgt (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) :
    N4c.cAB κ a < κ.blocks ∧ N4c.nodeKind4 κ (N4c.cAB κ a) = some Kinds.hashA.target := by
  have hm := N4c.tailIvs_mem κ ha ⟨.hashA, N4c.cAB κ a, N4c.cAB κ a + 1, fun _ => some Kinds.hashA.target⟩
    (by simp [N4c.tailIvs])
  have hk : N4c.TIv.mem ⟨.hashA, N4c.cAB κ a, N4c.cAB κ a + 1, fun _ => some Kinds.hashA.target⟩
      (N4c.cAB κ a) = true := by simp [N4c.TIv.mem]
  exact ⟨N4c.mem_lt hm hk, N4c.tgt_of_mem hm hk⟩

/-- **The statement cells of an aggregate child are `c_A`**: `cAB`'s `h_out` (`PubCells4`). -/
theorem stmt_cells {κ : NodeKind} {w : Asg} {vk c₁ c₂ : Digest} (hP : N4c.PubCells4 κ w vk c₁ c₂) {a : ℕ}
    (ha : a < N4c.nAgg κ) :
    Read.digestOf w (hc (N4c.cAB κ a) 2) (hc (N4c.cAB κ a) 3) = N4c.stOf c₁ c₂ (N4c.aggChild κ a) := by
  have hσ := N4c.aggChild_lt κ ha
  have hs : ∀ h, N4c.stC κ (N4c.aggChild κ a) h = hc (N4c.cAB κ a) (2 + h) := fun h => by
    simp only [N4c.stC, N4c.isAgg_aggChild, if_true, N4c.aggOf_aggChild κ ha, hc]; ring
  unfold N4c.PubCells4 at hP
  simp only [N4c.cells4, List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.cons_append,
    Node.pubVals, Node.halves, List.cons.injEq] at hP
  rw [← hs 0, ← hs 1]
  rcases (by omega : N4c.aggChild κ a = 0 ∨ N4c.aggChild κ a = 1) with h | h <;> rw [h] <;> simp only [N4c.stOf]
  · exact Snd.digestOf_halves hP.2.2.2.1 hP.2.2.2.2.1
  · exact Snd.digestOf_halves hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.1

/-- **`c_A = leafStmt e n`** with `e`, `n` read off `cAB`'s message (no row: the `hashA` block). -/
theorem stmt_A {κ : NodeKind} {w : Asg} {vk c₁ c₂ : Digest} (hZ : N4c.truthZ4 κ w) (hP : N4c.PubCells4 κ w vk c₁ c₂)
    {a : ℕ} (ha : a < N4c.nAgg κ) : N4c.stOf c₁ c₂ (N4c.aggChild κ a) = leafStmtF (hAe κ a w) (hAn κ a w) := by
  obtain ⟨hb, ht⟩ := cAB_tgt κ ha
  have hh := N4c.holds_of_Z hZ hb ht
  have hmsg : (Block.msgBytes (N4c.bitsB4 w (N4c.cAB κ a))).take 41 = hA κ a w := by
    refine List.ext_getElem (by simp [Block.msgBytes, hA, Stream.streamBytes_length]) fun p h₁ h₂ => ?_
    have hp : p < 41 := by simpa [hA, Stream.streamBytes_length] using h₂
    rw [List.getElem_take, ← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, Block.msgBytes_getD _ (by omega)]
    simp only [hA, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some, Nat.mod_eq_of_lt (show p < 64 by omega)]
  have h0 : (hA κ a w).getD 0 0 = tagLeaf := by
    rw [← hmsg, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by norm_num),
      ← List.getD_eq_getElem?_getD, Block.msgBytes_getD _ (by norm_num), Nat.mul_zero, Nat.add_zero]
    exact (Kinds.hashA_sound (R := F) hh).2
  rw [← stmt_cells hP ha, ← readDigest_digestOf, Kinds.hashA_leafStmt (R := F) hh (by rw [hmsg]; exact hA_eq κ a w h0),
    leafStmtF_eq]


/-! ## `aggChk` -/

theorem mapM_map_some {γ β : Type} (P : ℕ → γ) (f : γ → Option β) (g : ℕ → β) :
    ∀ l : List ℕ, (∀ i ∈ l, f (P i) = some (g i)) → (l.map P).mapM f = some (l.map g)
  | [], _ => rfl
  | i :: l, h => by
    rw [List.map_cons, List.mapM_cons, h i List.mem_cons_self,
      mapM_map_some P f g l fun j hj => h j (List.mem_cons_of_mem _ hj)]
    rfl

/-- **The chaining** of views whose consecutive starts and ends meet. -/
theorem chainOk_range' (V : ℕ → SegView) : ∀ k m, (∀ i, m + 1 ≤ i → i < m + k → (V i).start = (V (i - 1)).h) →
    chainOk ((List.range' m k).map V) = true
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | k + 2, m, h => by
    rw [show List.range' m (k + 2) = m :: List.range' (m + 1) (k + 1) from rfl, List.map_cons,
      show List.range' (m + 1) (k + 1) = (m + 1) :: List.range' (m + 1 + 1) k from rfl, List.map_cons, chainOk,
      ← List.map_cons, show (m + 1) :: List.range' (m + 1 + 1) k = List.range' (m + 1) (k + 1) from rfl,
      chainOk_range' V (k + 1) (m + 1) fun i h1 h2 => h i (by omega) (by omega),
      h (m + 1) le_rfl (by omega), Nat.add_sub_cancel]
    simp

theorem cap_segAt (ι : Kind) : (segAt ι).cap = 2 ^ capE ι := by cases ι <;> rfl

theorem selc_eq (κ : NodeKind) (v : ℕ) (ι : Kind) : selc κ v ι = κ.oneCell + selR v ι := by
  cases ι <;> rfl

/-- **`V_A`'s checks on views indexed by the sub-slots.** -/
theorem aggChecks_of {c e : Digest} {n k : ℕ} {V : ℕ → SegView} (hc : c = leafStmtF e n)
    (hk : 1 ≤ k ∧ k ≤ 4) (hr : ∀ i < k, 1 ≤ (V i).n ∧ (V i).n ≤ (V i).kind.cap)
    (hs : ∑ i ∈ range k, (V i).n = n) (he : (V (k - 1)).h = e)
    (hch : ∀ i, 1 ≤ i → i < k → (V i).start = (V (i - 1)).h) :
    aggChecks c n e ((List.range k).map V) = true := by
  rw [aggChecks]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_map, List.length_range]
  refine ⟨⟨⟨⟨⟨hc, hk⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact decide_eq_true (hr i (List.mem_range.1 hi))
  · rw [List.map_map, lsum_range]; exact hs
  · rw [List.getLast?_map, show (List.range k).getLast? = some (k - 1) by
      rw [List.getLast?_eq_getElem?, List.length_range, List.getElem?_range (by omega)], Option.map_some,
      Option.map_some, he]
  · rw [List.range_eq_range']
    exact chainOk_range' V k 0 fun i h1 h2 => hch i (by omega) (by omega)

section Agg
variable {impl₀ : OpImpl} {base : NodeKind → OpImpl} {pf : Trace → Proof} {κ : NodeKind}
  {vk c₁ c₂ : Digest} {w : Asg}

/-- **The check rows hold** (folded into slot 1's link rows; otherwise the rejecting row). -/
theorem chk_hold (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ a < N4c.nAgg κ, ∀ r ∈ aggRowsC κ a (actW κ a), r.Holds w := by
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hone := one_of_pubCells hP
  have hF := protoFit_of hone hE
  have h1 : 1 < κ.vslots := by cases κ <;> decide
  by_cases h : xOkK κ = true
  · intro a ha r hr
    refine linkRows_hold hF h1 hE r (List.mem_append_right _ ?_)
    rw [extRowsC, if_pos rfl, if_pos h, xRowsK_eq]
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, hr⟩)
  · exfalso
    have := linkRows_hold hF h1 hE (rejR κ)
      (List.mem_append_right _ (by rw [extRowsC, if_pos rfl, if_neg h]; simp))
    simp [rejR, Row.Holds, hone] at this

theorem aggPf_hdr (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) {p : ℕ} (hp : p < 48) :
    byteAt (aggPf pf κ a w) p = (aggHdr (kAct κ a w) (hAn κ a w) (hAe κ a w)).getD p 0 := by
  rw [aggPf, byteAt_mk, List.getD_append _ _ _ _ (by rw [aggHdr_length]; exact hp)]

theorem aggHdr_n (k n : ℕ) (e : Digest) {t : ℕ} (ht : t < 8) : (aggHdr k n e).getD (8 + t) 0 = (enc64 n).getD t 0 := by
  unfold aggHdr
  rw [List.append_assoc, List.append_assoc, List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp [enc64_length]; omega)]
  congr 1; simp; omega

theorem aggHdr_e (k n : ℕ) (e : Digest) {j : ℕ} (hj : j < 32) : (aggHdr k n e).getD (16 + j) 0 = e[j] := by
  unfold aggHdr
  rw [List.append_assoc, List.append_assoc, List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp [enc64_length]; omega)]
  simp [enc64_length, List.getD_eq_getElem?_getD, show 16 + j - 2 - 6 - 8 = j by omega, hj]

theorem rdLE64_aggPf (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) (hl : hAn κ a w < 2 ^ 64) :
    rdLE64 (aggPf pf κ a w) 8 = hAn κ a w := by
  rw [rdLE64, lsum_range]
  conv_rhs => rw [← CompPoly.Bytes.ofListLE_toListLE_of_lt (w := 8) (show hAn κ a w < 256 ^ 8 by simpa using hl),
    ← Snd.enc64_toListLE, ofListLE_sum, enc64_length]
  refine sum_congr rfl fun t ht => ?_
  rw [aggPf_hdr pf κ a w (by have := mem_range.1 ht; omega), aggHdr_n _ _ _ (mem_range.1 ht)]

theorem bytesAt_aggPf (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) :
    bytesAt (aggPf pf κ a w) 16 32 = hAe κ a w :=
  Vector.ext fun j hj => by rw [bytesAt, Vector.getElem_ofFn, aggPf_hdr pf κ a w (by omega), aggHdr_e _ _ _ hj]

/-- **`Gap4R.aggChk` from the node rows** (B4): every aggregate meets `V_A`'s checks against its
statement `c_A`. -/
theorem aggChk_of_rows (hpf : PfHdr pf) (hpv : PfView pf)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ a < N4c.nAgg κ, ∃ vs, (aggSegs (piSizeOf seq4) (N4c.kA (rd4 pf) κ w a)
      ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π).mapM segView = some vs ∧
    aggChecks (N4c.stOf c₁ c₂ (N4c.aggChild κ a)) (rdLE64 ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 8)
      (bytesAt ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 16 32) vs = true := by
  intro a ha
  have hS' := hS
  obtain ⟨hZ, -, hL, hE, hP⟩ := hS'
  have hone := one_of_pubCells hP
  have hF := protoFit_of hone hE
  have hlk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w :=
    fun i hi => linkRows_hold hF (sub_facts κ ha hi).1 hE
  have hK := actK_kAct hone ha hL hlk
  have hPr := act_profile hone ha hL hlk hK
  obtain ⟨hk1, hkm, -⟩ := hK
  have hR := chk_hold hS a ha
  have hP' : ∀ i < κ.maxK, (actW κ a i).ev w = if i < kAct κ a w then 1 else 0 := fun i hi => by
    rw [actW_eq]; exact hPr i hi
  have h4 : κ.maxK ≤ 4 := by cases κ <;> decide
  set k := kAct κ a w with hkdef
  have hsel : ∀ i < k, ∃ ι, SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι := fun i hi => by
    obtain ⟨ι, hι⟩ := selA_sel hone ha hL hlk (actK_kAct hone ha hL hlk) i hi
    rw [protoOf_seg (sub_facts κ ha (by omega : i < κ.maxK)).2.2.1] at hι
    exact ⟨ι, hι⟩
  classical
  let ιf : ℕ → Kind := fun i => if h : i < k then Classical.choose (hsel i h) else .L32
  have hιf : ∀ i (h : i < k), SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) (ιf i) := fun i h => by
    simp only [ιf, dif_pos h]; exact Classical.choose_spec (hsel i h)
  let V : ℕ → SegView := fun i => ⟨segAt (ιf i), dg2 (w (sE κ (N4c.aggChild κ a) i 6)) (w (sE κ (N4c.aggChild κ a) i 7)),
    sh1 (w (sE κ (N4c.aggChild κ a) i 13)) (w (sE κ (N4c.aggChild κ a) i 14)) (w (sE κ (N4c.aggChild κ a) i 15)),
    n8 (w (sE κ (N4c.aggChild κ a) i 15))⟩
  have hπ : ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π = aggPf pf κ a w := by simp only [rd4, sgn4_agg pf κ ha]
  refine ⟨(List.range k).map V, ?_, ?_⟩
  · -- the views
    rw [kA_rd4 pf κ ha, hπ, aggPf, aggSegs_flat _ _ (aggHdr_length _ _ _)
      (fun s hs => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
        exact slotPf_length pf κ _ w) (by simp), List.map_map]
    exact mapM_map_some _ segView V _ fun i hi => view_sub hpf hpv hS ha (List.mem_range.1 hi) (hιf i (List.mem_range.1 hi))
  · -- the checks
    have hl : hAn κ a w < 2 ^ 64 := by rw [hAn_eq, n8_bits]; exact nOfBits_lt _ 64
    have hact : ∀ i < k, (actW κ a i).ev w = 1 := fun i hi => by rw [hP' i (by omega), if_pos hi]
    rw [hπ, rdLE64_aggPf pf κ a w hl, bytesAt_aggPf]
    refine aggChecks_of (stmt_A hZ hP ha) ⟨hk1, by omega⟩ (fun i hi => ?_) ?_ ?_
      (fun i h1 h2 => chain_sub hone hR (by omega) (by omega) (hact i (by omega)))
    · -- the lengths' range
      have hselc : ∀ ι', w (selc κ (N4c.sub κ a i) ι') = if ι' = ιf i then 1 else 0 := fun ι' => by
        have h := (hιf i hi).2 ι'
        have hp := protoOf_seg (sub_facts κ ha (by omega : i < κ.maxK)).2.2.1
        have e := slotAsg_sel κ (N4c.sub κ a i) w ι'
        rw [hp] at e
        simp only [protoP, Lin.ev_cell, e] at h
        rw [selc_eq]; exact h
      have := rng_sub hone hR (by omega : i < κ.maxK) (hact i hi) hselc
      rw [show (V i).kind.cap = 2 ^ capE (ιf i) from cap_segAt _]
      exact this
    · -- the sum
      rw [hAn_eq]
      exact sum_sub hone hR hk1 hkm hP'
    · -- the end
      rw [hAe_eq]
      have hind : (ind κ (actW κ a) (k - 1 + 1)).ev w = 1 := by
        rw [Nat.sub_add_cancel hk1, ind_ev hk1 hkm hPr hk1 hkm, if_pos rfl]
      exact end_sub hone hR (by omega) hind

/-- **`Gap4R` reduces to `imp`** (B4): with the node rows, `PfHdr pf` and `PfView pf`, the slots'
imports alone give S-N2's `Gap4`. -/
theorem gap4_of_rowsI (hpf : PfHdr pf) (hpv : PfView pf)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (himp : ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)) :
    Gap4 impl₀ base pf κ vk c₁ c₂ w :=
  gap4_of_rows pf hpf hS ⟨himp, aggChk_of_rows hpf hpv hS⟩

end Agg

end N4s
end FR
