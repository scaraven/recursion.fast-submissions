-- New for `flock-recursive` (PACK-4.4 §1.3 `input`/`stmtOk4`, PK-m7; track IMP): what the statement
-- rows give — `stmtOk4` at every active slot, and the cells of every slot's `input` registers.
import FRNodeRows4AggChkG
import FRSoundness4R4Stmt

/-!
# The statement rows' soundness (PK-m7)

With `StmtN4` (Z truth on the statement blocks, `PubCells4`), the statement rows
(`W4.stmtRows`, folded into `xRowsA`) and the proof decoder's positional facts (`PfHdr`, `PfView`):

* **`stmtOk4_of_rows`**: every active slot meets the statement fact `stmtOk4` at every index its
  selectors may pick (`SlotImp`'s second conjunct, so `SlotImpA`'s third). A segment slot needs no
  row: its `c` *is* `leafStmt` of the bytes `stmtOk4` hashes (`stmtOk_seg`, from the slot's kind byte);
  the previous node needs `hashB1`/`hashB2` tied to its `stmt` field and to `c₁` (`stmtOk_prev`).
* **The `input` registers' cells** (the targets of the `input` alias, PACK §1.3): a segment slot's
  `c` is its `hashA` block's `h_out` (`stmtC_sub`), the previous node's `c` is `c₁`'s public cells
  (`stmtC_prev`), every slot's `vk` its signed child's public `vk` cells (`stmtVk`).
* The block-generic forms of B4's `hA_*` (`hBm_*`, `leaf_blk`): a `hashA` block's output is
  `leafStmt` of the element-aligned fields of its message.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Finset

/-! ## A `hashA` block's message (block-generic B4 `hA_*`) -/

/-- A block's first 41 message bytes. -/
noncomputable def hBm (blk : ℕ) (w : Asg) : List UInt8 :=
  Stream.streamBytes (fun _ => N4c.bitsB4 w blk) 41

/-- Its bytes `1 … 32` (`h`) and its bytes `33 … 40` read little-endian (`n`). -/
noncomputable def hBe (blk : ℕ) (w : Asg) : Digest := Vector.ofFn fun i : Fin 32 => (hBm blk w).getD (1 + i) 0
noncomputable def hBn (blk : ℕ) (w : Asg) : ℕ :=
  ((List.range 8).map fun i => ((hBm blk w).getD (33 + i) 0).toNat * 256 ^ i).sum

theorem hBm_get (blk : ℕ) (w : Asg) {p : ℕ} (hp : p < 41) :
    (hBm blk w).getD p 0 = fb (w (hc blk (4 + p / 16))) (p % 16) := by
  rw [hBm, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
    Option.map_some, Option.getD_some, Nat.mod_eq_of_lt (show p < 64 by omega),
    show Blake2sCircuit.msgBase + 8 * p = 8 * (64 + p) by rw [show Blake2sCircuit.msgBase = 512 from rfl]; ring,
    readByte_hc w _ (by omega),
    show (64 + p) / 16 = 4 + p / 16 by omega]
  exact fb_congr_mod _ (by omega)

theorem hBe_eq (blk : ℕ) (w : Asg) :
    hBe blk w = sh1 (w (hc blk 4)) (w (hc blk 5)) (w (hc blk 6)) := by
  refine Vector.ext fun j hj => ?_
  rw [hBe, Vector.getElem_ofFn, hBm_get blk w (by omega), sh1, Vector.getElem_ofFn, catByte]
  simp only [Fin.val_mk]
  refine (fb_mod _ _).trans ?_
  congr 1
  rcases (by omega : (1 + j) / 16 = 0 ∨ (1 + j) / 16 = 1 ∨ (1 + j) / 16 = 2) with h | h | h <;> rw [h] <;> rfl

theorem hBn_eq (blk : ℕ) (w : Asg) : hBn blk w = n8 (w (hc blk 6)) := by
  rw [hBn, n8, lsum_range]
  refine sum_congr rfl fun t ht => ?_
  have ht := mem_range.1 ht
  rw [hBm_get blk w (by omega), show (33 + t) / 16 = 2 by omega]
  congr 2
  exact fb_congr_mod _ (by omega)

theorem hBm_drop (blk : ℕ) (w : Asg) : (hBm blk w).drop 33 = enc64 (hBn blk w) := by
  have hl : ((hBm blk w).drop 33).length = 8 := by simp [hBm, Stream.streamBytes_length]
  have hn : hBn blk w = CompPoly.Bytes.ofListLE ((hBm blk w).drop 33) := by
    rw [ofListLE_sum, hl, hBn, lsum_range]
    refine sum_congr rfl fun t _ => ?_
    simp [List.getD_eq_getElem?_getD]
  rw [hn, Snd.enc64_toListLE, ← hl, CompPoly.Bytes.toListLE_ofListLE]

theorem hBm_eq (blk : ℕ) (w : Asg) (h0 : (hBm blk w).getD 0 0 = tagLeaf) :
    hBm blk w = tagLeaf :: (hBe blk w).toList ++ enc64 (hBn blk w) := by
  have hl : (hBm blk w).length = 41 := by simp [hBm, Stream.streamBytes_length]
  conv_lhs => rw [← List.take_append_drop 33 (hBm blk w)]
  rw [hBm_drop]
  congr 1
  refine List.ext_getElem (by simp [hl]) fun p h₁ h₂ => ?_
  rw [List.getElem_take, ← List.getD_eq_getElem _ 0]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [h0, List.getElem_cons_zero]
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [List.getElem_cons_succ, Vector.getElem_toList]
    unfold hBe
    rw [Vector.getElem_ofFn]
    congr 1; simp only [Fin.val_mk]; omega

/-- **A `hashA` block outputs `leafStmt` of its message's `h` and `n`** (its `h_out` cells). -/
theorem leaf_blk {κ : NodeKind} {w : Asg} (hZ : N4c.truthZ4 κ w) {blk : ℕ} (hb : blk < κ.blocks)
    (ht : N4c.nodeKind4 κ blk = some Kinds.hashA.target) :
    Read.digestOf w (hc blk 2) (hc blk 3) = leafStmtF (hBe blk w) (hBn blk w) := by
  have hh := N4c.holds_of_Z hZ hb ht
  have hmsg : (Block.msgBytes (N4c.bitsB4 w blk)).take 41 = hBm blk w := by
    refine List.ext_getElem (by simp [Block.msgBytes, hBm, Stream.streamBytes_length]) fun p h₁ h₂ => ?_
    have hp : p < 41 := by simpa [hBm, Stream.streamBytes_length] using h₂
    rw [List.getElem_take, ← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, Block.msgBytes_getD _ (by omega)]
    simp only [hBm, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some, Nat.mod_eq_of_lt (show p < 64 by omega)]
  have h0 : (hBm blk w).getD 0 0 = tagLeaf := by
    rw [← hmsg, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by norm_num),
      ← List.getD_eq_getElem?_getD, Block.msgBytes_getD _ (by norm_num), Nat.mul_zero, Nat.add_zero]
    exact (Kinds.hashA_sound (R := F) hh).2
  rw [← readDigest_digestOf, Kinds.hashA_leafStmt (R := F) hh (by rw [hmsg]; exact hBm_eq blk w h0),
    leafStmtF_eq]

/-! ## The statement blocks -/

/-- **Slot `v`'s statement blocks** are a `hashA`, a `hashB1 tagNode` and a `hashB2` block. -/
theorem stmt_tgt (κ : NodeKind) {v : ℕ} (hv : v < κ.vslots) :
    (N4c.stmtB κ + 3 * v < κ.blocks ∧ N4c.nodeKind4 κ (N4c.stmtB κ + 3 * v) = some Kinds.hashA.target) ∧
    (N4c.stmtB κ + 3 * v + 1 < κ.blocks ∧
      N4c.nodeKind4 κ (N4c.stmtB κ + 3 * v + 1) = some (Kinds.hashB1 RecursionFast.tagNode).target) ∧
    (N4c.stmtB κ + 3 * v + 2 < κ.blocks ∧ N4c.nodeKind4 κ (N4c.stmtB κ + 3 * v + 2) = some Kinds.hashB2.target) := by
  have hm : ∀ iv ∈ N4c.stmtIvs κ, iv ∈ N4c.nodeLayout4 κ := fun iv h => by
    simp only [N4c.nodeLayout4, List.mem_append]; tauto
  have hi : ∀ iv ∈ ([⟨.hashA, N4c.stmtB κ + 3 * v, N4c.stmtB κ + 3 * v + 1, fun _ => some Kinds.hashA.target⟩,
      ⟨.hashB1, N4c.stmtB κ + 3 * v + 1, N4c.stmtB κ + 3 * v + 2, fun _ => some (Kinds.hashB1 RecursionFast.tagNode).target⟩,
      ⟨.hashB2, N4c.stmtB κ + 3 * v + 2, N4c.stmtB κ + 3 * v + 3, fun _ => some Kinds.hashB2.target⟩] : List N4c.TIv),
      iv ∈ N4c.nodeLayout4 κ := fun iv h => hm iv (List.mem_flatMap.2 ⟨v, List.mem_range.2 hv, h⟩)
  have key : ∀ iv ∈ ([⟨.hashA, N4c.stmtB κ + 3 * v, N4c.stmtB κ + 3 * v + 1, fun _ => some Kinds.hashA.target⟩,
      ⟨.hashB1, N4c.stmtB κ + 3 * v + 1, N4c.stmtB κ + 3 * v + 2,
        fun _ => some (Kinds.hashB1 RecursionFast.tagNode).target⟩,
      ⟨.hashB2, N4c.stmtB κ + 3 * v + 2, N4c.stmtB κ + 3 * v + 3, fun _ => some Kinds.hashB2.target⟩] :
      List N4c.TIv), iv.lo < iv.hi → iv.lo < κ.blocks ∧ N4c.nodeKind4 κ iv.lo = iv.tgt 0 := by
    intro iv h hlt
    have hk : iv.mem iv.lo = true := by
      simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq]; omega
    refine ⟨N4c.mem_lt (hi iv h) hk, ?_⟩
    rw [N4c.tgt_of_mem (hi iv h) hk, Nat.sub_self]
  exact ⟨key _ List.mem_cons_self (by simp), key _ (List.mem_cons_of_mem _ List.mem_cons_self) (by simp),
    key _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by simp)⟩

section Stmt
variable {pf : Trace → Proof} {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}

/-- **The statement rows hold** on the node statement (slot 1's node rows, as `chk_hold`). -/
theorem stmtRows_hold (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ r ∈ stmtRows κ (actW κ), r.Holds w := by
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hone := one_of_pubCells hP
  have hF := protoFit_of hone hE
  have h1 : 1 < κ.vslots := by cases κ <;> decide
  by_cases h : xOkK κ = true
  · intro r hr
    refine linkRows_hold hF h1 hE r (List.mem_append_right _ ?_)
    rw [extRowsC, if_pos rfl, if_pos h, xRowsK_eq]
    exact List.mem_append_right _ (List.mem_append_right _ hr)
  · exfalso
    have := linkRows_hold hF h1 hE (rejR κ)
      (List.mem_append_right _ (by rw [extRowsC, if_pos rfl, if_neg h]; simp))
    simp [rejR, Row.Holds, hone] at this

/-- **The public `vk` cells** of signed child `σ` are `vk` (`PubCells4`). -/
theorem stmtVk (hP : N4c.PubCells4 κ w vk c₁ c₂) {σ : ℕ} (hσ : σ < 2) :
    Read.digestOf w (N4c.seedC κ σ 0) (N4c.seedC κ σ 1) = vk := by
  unfold N4c.PubCells4 at hP
  simp only [N4c.cells4, List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.cons_append,
    Node.pubVals, Node.halves, List.cons.injEq] at hP
  rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl
  · exact Snd.digestOf_halves hP.2.1 hP.2.2.1
  · exact Snd.digestOf_halves hP.2.2.2.2.2.1 hP.2.2.2.2.2.2.1

/-- **The previous node's public statement cells** are `c₁` (`PubCells4`). -/
theorem stmtC_prev (hP : N4c.PubCells4 κ w vk c₁ c₂) (hp : κ.hasPrev = true) :
    Read.digestOf w (N4c.seedC κ 0 2) (N4c.seedC κ 0 3) = c₁ := by
  have hs : ∀ h, N4c.stC κ 0 h = N4c.seedC κ 0 (2 + h) := fun h => by
    simp [N4c.stC, N4c.isAgg, hp]
  unfold N4c.PubCells4 at hP
  simp only [N4c.cells4, List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil, List.map_cons, List.map_nil, List.cons_append,
    Node.pubVals, Node.halves, List.cons.injEq, hs] at hP
  exact Snd.digestOf_halves hP.2.2.2.1 hP.2.2.2.2.1

/-- An active sub-slot's statement rows: its `hashA` message elements are its stream's `13 … 16`. -/
theorem stmt_cells_sub (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) {a : ℕ} (ha : a < N4c.nAgg κ)
    {i : ℕ} (hi : i < kAct κ a w) {e : ℕ} (he : e < 4) :
    w (hc (N4c.stmtB κ + 3 * N4c.sub κ a i) (4 + e)) = w (sE κ (N4c.aggChild κ a) i (13 + e)) := by
  obtain ⟨-, -, hL, hE, hP⟩ := id hS
  have hone := one_of_pubCells hP
  have hF := protoFit_of hone hE
  have hlk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w :=
    fun i hi => linkRows_hold hF (sub_facts κ ha hi).1 hE
  have hi' : i < κ.maxK := lt_of_lt_of_le hi (kAct_le κ a w)
  have hact : (actW κ a i).ev w = 1 := by
    rw [actW_eq, act_profile hone ha hL hlk (actK_kAct hone ha hL hlk) i hi', if_pos hi]
  refine eqRowG_holds hact (stmtRows_hold hS _ (List.mem_append_left _ (List.mem_append_left _ ?_)))
  exact List.mem_flatMap.2 ⟨a, List.mem_range.2 ha,
    List.mem_flatMap.2 ⟨i, List.mem_range.2 hi', List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩⟩⟩

/-- **An active sub-slot's `c` is its `hashA` block's `h_out`** (the cells of its `input c`). -/
theorem stmtC_sub (hpf : PfHdr pf) (hpv : PfView pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    {a : ℕ} (ha : a < N4c.nAgg κ) {i : ℕ} (hi : i < kAct κ a w) {ι : Kind}
    (hι : SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι) :
    (N4c.slotIn (rd4 pf) κ vk c₁ w (N4c.sub κ a i)).c =
      Read.digestOf w (hc (N4c.stmtB κ + 3 * N4c.sub κ a i) 2) (hc (N4c.stmtB κ + 3 * N4c.sub κ a i) 3) := by
  have hi' : i < κ.maxK := lt_of_lt_of_le hi (kAct_le κ a w)
  obtain ⟨hv, -, hpv', -⟩ := sub_facts κ ha hi'
  have hnp : ¬ (κ.hasPrev = true ∧ N4c.sub κ a i = 0) := fun ⟨h1, h2⟩ => by
    simp [isPrevSlot, h1, h2] at hpv'
  have hc := fun e (he : e < 4) => stmt_cells_sub hS ha hi he
  obtain ⟨hb, ht⟩ := (stmt_tgt κ hv).1
  rw [N4c.slotIn, if_neg hnp, view_sub hpf hpv hS ha hi hι]
  simp only [Option.map_some, Option.getD_some, segC]
  rw [leaf_blk hS.1 hb ht, hBe_eq, hBn_eq, hc 0 (by norm_num), hc 1 (by norm_num),
    hc 2 (by norm_num)]

/-! ## The statement fact `stmtOk4` -/

theorem byteAt_toList (q : ByteArray) (k : ℕ) : byteAt q k = q.data.toList.getD k 0 := by
  conv_lhs => rw [show q = ⟨q.data.toList.toArray⟩ from rfl]
  exact byteAt_mk _ _

/-- Byte `j < n` of `π.extract a (a + n)` is byte `a + j` of `π`. -/
theorem byteAt_extract (π : ByteArray) (a n : ℕ) {j : ℕ} (hj : j < n) :
    byteAt (π.extract a (a + n)) j = byteAt π (a + j) := by
  rw [byteAt_toList, byteAt_toList, ByteArray.data_extract, Array.toList_extract, List.extract,
    Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, if_pos hj, List.getElem?_drop]

/-- A message byte of an H block is a byte of its message element (A.7's pack). -/
theorem msg_byte (w : Asg) (blk : ℕ) {p : ℕ} (hp : p < 64) :
    (Block.msgBytes (N4c.bitsB4 w blk)).getD p 0 = fb (w (hc blk (4 + p / 16))) (p % 16) := by
  rw [Block.msgBytes_getD _ hp, show Blake2sCircuit.msgBase + 8 * p = 8 * (64 + p) by rw [show Blake2sCircuit.msgBase = 512 from rfl]; ring,
    readByte_hc w _ (by omega), show (64 + p) / 16 = 4 + p / 16 by omega]
  exact fb_congr_mod _ (by omega)

theorem vec_getD {n : ℕ} (v : Vector UInt8 n) {i : ℕ} (hi : i < n) : v.toList.getD i 0 = v[i] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), Vector.getElem_toList]

/-- The node statement's message `tag ‖ s[1, 33) ‖ s[33, 65)` read byte-wise (the vectors are
generalised away: `whnf` on a concrete `bytesAt` evaluates it). -/
theorem nodeMsg_getD (t : UInt8) (s : ByteArray) {p : ℕ} (h1 : 1 ≤ p) (h2 : p < 65) :
    (t :: (bytesAt s 1 32).toList ++ (bytesAt s 33 32).toList).getD p 0 = byteAt s p := by
  have gX : ∀ i < 32, (bytesAt s 1 32).toList.getD i 0 = byteAt s (1 + i) := fun i hi => by
    rw [vec_getD _ hi, bytesAt, Vector.getElem_ofFn]
  have gY : ∀ i < 32, (bytesAt s 33 32).toList.getD i 0 = byteAt s (33 + i) := fun i hi => by
    rw [vec_getD _ hi, bytesAt, Vector.getElem_ofFn]
  have hX : (bytesAt s 1 32).toList.length = 32 := Vector.length_toList
  generalize (bytesAt s 1 32).toList = X at gX hX
  generalize (bytesAt s 33 32).toList = Y at gY
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [List.cons_append, List.getD_cons_succ]
  rcases Nat.lt_or_ge q 32 with hq | hq
  · rw [List.getD_append _ _ _ _ (by omega), gX q hq, Nat.add_comm 1 q]
  · rw [List.getD_append_right _ _ _ _ (by omega), hX, gY _ (by omega)]
    congr 1; omega

theorem nodeMsg_length (t : UInt8) (s : ByteArray) :
    (t :: (bytesAt s 1 32).toList ++ (bytesAt s 33 32).toList).length = 65 := by
  simp only [List.length_append, List.length_cons, Vector.length_toList]

/-- **The previous node's `stmt` field** (proof bytes `48 … 175`) is its stream's elements `13 … 20`. -/
theorem stmtByte_prev (hpv : PfView pf) (hp : κ.hasPrev = true) {j : ℕ} (hj : j < 128) :
    byteAt ((rd4 pf).slotπ κ 0 w) (48 + j) = fb (w (sE κ 0 0 (13 + j / 16))) (j % 16) := by
  set B := N4c.chainBytes4 κ 0 0 w
  obtain ⟨rest, hr⟩ := itemsOf_seq4_two
  have htr : slotTr4 κ 0 w = Read.entryAt B (1 + 0 * N4c.strideB) .seed ::
      Read.entryAt B (1 + 0 * N4c.strideB + 159) (.absorb 128) ::
        Read.readItems B (1 + 0 * N4c.strideB + 159 + 208) rest := by
    simp only [slotTr4, isPrevSlot, hp, Bool.true_and, beq_self_eq_true, if_true]
    rw [segTr, hr]; rfl
  obtain ⟨-, hv2⟩ := hpv (Read.entryAt B (1 + 0 * N4c.strideB) .seed)
    (Read.entryAt B (1 + 0 * N4c.strideB + 159) (.absorb 128)) (Read.readItems B (1 + 0 * N4c.strideB + 159 + 208) rest)
  have hps : 176 ≤ piSizeOf seq4 := by rw [piSizeOf_seq4]; norm_num
  have hk0 : N4c.isAgg κ 0 = true → 1 ≤ 0 := fun h => by simp [isAgg_zero hp] at h
  show byteAt (⟨(slotPf pf κ 0 w).toArray⟩ : Proof) _ = _
  rw [byteAt_slotPfP pf κ 0 w (by omega), htr, hv2 j hj, entry_byte _ _ _ (by simp [Item.qlen]; omega)]
  have h := seg0_elem (κ := κ) (σ := 0) (k := 0) w hk0 (e := 13 + j / 16) (r := j % 16) (Nat.mod_lt _ (by norm_num))
    (by simp only [N4c.segB]; omega)
  rw [show 1 + 0 * N4c.strideB + 159 + 8 + (40 + j) = 16 * (13 + j / 16) + j % 16 by omega, h,
    fb_eq _ (Nat.mod_lt _ (by norm_num))]
  simp [sE]

/-- **The previous node's statement fact**: `nodeStmt` of its `stmt` field is `c₁` (`hashB1`/`hashB2`
tied to the field and to `c₁`'s public cells by the statement rows). -/
theorem stmtOk_prev (hpv : PfView pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hp : κ.hasPrev = true) (ι : Kind) :
    stmtOk4 seq4 (kindP 0 ι) (N4c.slotIn (rd4 pf) κ vk c₁ w 0) = true := by
  obtain ⟨hZ, -, -, -, hP⟩ := id hS
  have hone := one_of_pubCells hP
  obtain ⟨-, ⟨hb1, ht1⟩, ⟨hb2, ht2⟩⟩ := stmt_tgt κ (vslots_pos κ)
  simp only [Nat.mul_zero, Nat.add_zero] at hb1 ht1 hb2 ht2
  set B1 := N4c.stmtB κ + 1
  set B2 := N4c.stmtB κ + 2
  have hR : ∀ r ∈ stmtRowsP κ, r.Holds w := fun r hr =>
    stmtRows_hold hS r (List.mem_append_left _ (List.mem_append_right _ hr))
  rw [stmtRowsP, if_pos hp] at hR
  have e1 : ∀ e < 4, w (hc B1 (4 + e)) = w (sE κ 0 0 (13 + e)) := fun e he => eqRow_holds hone
    (hR _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩)))))
  have e2 : ∀ e < 4, w (hc B2 (4 + e)) = w (sE κ 0 0 (17 + e)) := fun e he => eqRow_holds hone
    (hR _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩)))))
  have e3 : ∀ h < 2, w (hc B2 h) = w (hc B1 (2 + h)) := fun h hh => eqRow_holds hone
    (hR _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩))))
  have e4 : ∀ h < 2, w (hc B2 (2 + h)) = w (N4c.seedC κ 0 (2 + h)) := fun h hh => eqRow_holds hone
    (hR _ (List.mem_append_right _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩)))
  have hh1 := N4c.holds_of_Z hZ hb1 ht1
  have hh2 := N4c.holds_of_Z hZ hb2 ht2
  have hl : ∀ j < 256, N4c.bitsB4 w B2 (ProductCircuit.pos j) = N4c.bitsB4 w B1 (ProductCircuit.pos (256 + j)) :=
    fun j hj => by
      rw [bitsB4_bit w _ (by omega), bitsB4_bit w _ (by omega)]
      have h := e3 (j / 128) (by omega)
      simp only [hc] at h
      rw [show (256 + j) / 128 = 2 + j / 128 by omega, ← h]
      simp only [W4.bitN, show (256 + j) % 128 = j % 128 by omega]
  set π := (rd4 pf).slotπ κ 0 w
  set s := π.extract 48 (48 + 128)
  have hsz : ∀ j < 128, byteAt s j = fb (w (sE κ 0 0 (13 + j / 16))) (j % 16) := fun j hj => by
    rw [byteAt_extract _ _ _ hj, stmtByte_prev hpv hp hj]
  have hm : Block.msgBytes (N4c.bitsB4 w B1) ++ (Block.msgBytes (N4c.bitsB4 w B2)).take 1 =
      RecursionFast.tagNode :: (bytesAt s 1 32).toList ++ (bytesAt s 33 32).toList := by
    have hl1 : (Block.msgBytes (N4c.bitsB4 w B1)).length = 64 := by simp [Block.msgBytes]
    have hl2 : (Block.msgBytes (N4c.bitsB4 w B2)).length = 64 := by simp [Block.msgBytes]
    refine List.ext_getElem (by rw [nodeMsg_length, List.length_append, hl1, List.length_take, hl2]; rfl)
      fun p h₁ h₂ => ?_
    have hp65 : p < 65 := by rw [nodeMsg_length] at h₂; exact h₂
    rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [List.getD_append _ _ _ _ (by rw [hl1]; norm_num), List.cons_append, List.getD_cons_zero,
        ← (Kinds.hashB_sound (R := F) hh1 hh2 hl).2, Block.msgBytes_getD _ (by norm_num), Nat.mul_zero,
        Nat.add_zero]
    rw [nodeMsg_getD _ _ hp0 hp65, hsz _ (by omega)]
    rcases Nat.lt_or_ge p 64 with hp64 | hp64
    · rw [List.getD_append _ _ _ _ (by rw [hl1]; exact hp64), msg_byte w _ hp64, e1 _ (by omega)]
    · obtain rfl : p = 64 := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl1]), hl1, Nat.sub_self, List.getD_eq_getElem?_getD,
        List.getElem?_take, if_pos (by norm_num), ← List.getD_eq_getElem?_getD, msg_byte w _ (by norm_num),
        e2 0 (by norm_num)]
  have hout : Read.digestOf w (N4c.seedC κ 0 2) (N4c.seedC κ 0 3) = nodeStmt (bytesAt s 1 32) (bytesAt s 33 32) := by
    have e40 := e4 0 (by norm_num)
    have e41 := e4 1 (by norm_num)
    norm_num at e40 e41
    rw [show Read.digestOf w (N4c.seedC κ 0 2) (N4c.seedC κ 0 3) = Read.digestOf w (hc B2 2) (hc B2 3) by
      unfold Read.digestOf; rw [e40, e41], ← readDigest_digestOf,
      Kinds.hashB_nodeStmt (R := F) hh1 hh2 hl hm]
  rw [N4c.slotIn, if_pos ⟨hp, rfl⟩, kindP, if_pos rfl]
  simp only [stmtOk4, decide_eq_true_eq, KindP.ofNode, stmtDigest, stmtBytes4, Snd.R4.stmtOff4]
  rw [nodeStmtF_eq, ← hout, stmtC_prev hP hp]

theorem data_getD (s : ByteArray) (k : ℕ) : s.data.getD k 0 = byteAt s k := by
  rw [byteAt_toList, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **A segment's statement fact holds by the reader's definition**: once its byte 0 is a segment
kind's (its view exists), its `c` is `leafStmt` of exactly the bytes `stmtOk4` hashes. -/
theorem stmtOk_seg (π : Proof) {σ : SegKind} (hb : byteAt π 0 = σ.byte) (σ' : SegKind) (vk : Digest) :
    stmtOk4 seq4 (.ofSeg σ') ⟨vk, ((segView π).map segC).getD 0, π⟩ = true := by
  simp only [stmtOk4, decide_eq_true_eq, KindP.ofSeg, stmtDigest, stmtBytes4, Snd.R4.stmtOff4, segView, hb,
    SegKind.ofByte?_byte, Option.map_some, Option.getD_some, segC]
  refine congrArg₂ leafStmtF ?_ ?_
  · refine Vector.ext fun j hj => ?_
    rw [bytesAt, bytesAt, Vector.getElem_ofFn, Vector.getElem_ofFn, byteAt_extract _ _ _ (by omega)]
    congr 1; omega
  · rw [rdLE64]
    refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    have hi := List.mem_range.1 hi
    rw [data_getD, byteAt_extract _ _ _ (by omega)]
    congr 3; omega

/-- **`stmtOk4` at every active slot and selectable index** (`SlotImp`'s second conjunct): the
previous node's from the statement rows (`stmtOk_prev`), a segment's from its kind byte
(`kindS_of_rows`, `stmtOk_seg`). -/
theorem stmtOk4_of_rows (hpf : PfHdr pf) (hpv : PfView pf)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      stmtOk4 seq4 (kindP (protoOf κ v) ι) (N4c.slotIn (rd4 pf) κ vk c₁ w v) = true := by
  rintro v (⟨hp, rfl⟩ | ⟨a, ha, i, hi, rfl⟩) ι hι
  · rw [protoOf_zero hp]; exact stmtOk_prev hpv hS hp ι
  · rw [kA_rd4 pf κ ha] at hi
    have hi' : i < κ.maxK := lt_of_lt_of_le hi (kAct_le κ a w)
    obtain ⟨-, -, hpv', -⟩ := sub_facts κ ha hi'
    have hnp : ¬ (κ.hasPrev = true ∧ N4c.sub κ a i = 0) := fun ⟨h1, h2⟩ => by
      simp [isPrevSlot, h1, h2] at hpv'
    rw [protoOf_seg hpv'] at hι ⊢
    have hb := kindS_of_rows pf hpf hS a ha i hi ι hι
    rw [N4c.slotIn, if_neg hnp, kindP, if_neg one_ne_zero]
    exact stmtOk_seg _ hb _ vk

end Stmt

end N4s
end FR
