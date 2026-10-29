-- New for `flock-recursive` (PACK-4.4.1 §4.3; ASK-P-RESULT §6 item 1; track ASK-T): every byte of an
-- active slot's segment is an H cell (the last block by `aggPad`), and the pinned tags.
import FRNodeRows4AskTB

/-!
# The whole segment off H, and the tags

ASK-P's bridge (`slot_byte`) stops before the segment's last block: for an aggregate with `k < maxK`
its stream's last block is the candidate final block `finB + (k − 1)`, not the main chain's. Here:

* **`readByte_eqz`**, **`chainBytes4_elem'`**: a stream byte is the main chain's H cell wherever the
  final block's message equals the main chain's block (`AggPad4`, R-4-m2: whole blocks, `aggB k =
  64·aggL k`, so its `r` is 64 and the whole message is tied);
* **`slot_byte'`**: every byte `x < segB` of an active slot's segment (given `AggPad4` at every
  aggregate, a theorem of the statement's rows: `wots_aggPad_of_rows`); **`slot_qbyte'`**,
  **`slot_ans'`**: entry `k`'s query bytes and answer for every item, the last one included;
* **`tag_byte`**: an entry's query tag is its item's (`itemTag`), from the pack rows (`wfSeg`'s pins;
  the seed's from `HeadOk`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## The last block -/

/-- A block's message byte depends only on its message bits. -/
theorem readByte_eqz (w : Asg) {b₁ b₂ p : ℕ} (hp : 512 ≤ p) (hp' : p + 8 ≤ 1024)
    (h : ∀ x < 512, N4c.zN4 w b₁ (512 + x) = N4c.zN4 w b₂ (512 + x)) :
    Block.readByte (N4c.bitsB4 w b₁) p = Block.readByte (N4c.bitsB4 w b₂) p := by
  refine UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi => ?_)
  rw [Block.readByte_getLsbD _ _ hi, Block.readByte_getLsbD _ _ hi, N4c.bitsB4_pos w _ (by omega),
    N4c.bitsB4_pos w _ (by omega), show p + i = 512 + (p + i - 512) by omega, h _ (by omega)]

/-- **A stream byte is its main-chain cell's**, the last block included where its block is the main
chain's or carries the main chain's message. -/
theorem chainBytes4_elem' {κ : NodeKind} {σ k : ℕ} (w : Asg) {e r : ℕ} (hr : r < 16)
    (hp : 16 * e + r < N4c.streamB κ σ k)
    (hfin : e / 4 + 1 = N4c.streamL κ σ k → N4c.finBlk κ σ k = N4c.chBase κ σ + e / 4 ∨
      ∀ x < 512, N4c.zN4 w (N4c.finBlk κ σ k) (512 + x) = N4c.zN4 w (N4c.chBase κ σ + e / 4) (512 + x)) :
    (N4c.chainBytes4 κ σ k w).getD (16 * e + r) 0 = (F.toBytes (w (sCell (N4c.chBase κ σ) e)))[r] := by
  obtain ⟨h1, h2⟩ := Stream.elem_slot e r hr
  rw [N4c.chainBytes4, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hp, Option.map_some, Option.getD_some, h1, h2]
  simp only [N4c.chainW4, N4c.blkOf]
  rw [show 128 * (4 + e % 4) + 8 * r = 512 + 128 * (e % 4) + 8 * r by ring]
  have hm : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
  split_ifs with hb
  · rcases hfin hb with h | h
    · rw [h, readByte_cell w _ hm hr]; rfl
    · rw [readByte_eqz w (by omega) (by omega) h, readByte_cell w _ hm hr]; rfl
  · rw [readByte_cell w _ hm hr]; rfl

/-- **The last block reads the main chain**: for an aggregate with `k < maxK`, `AggPad4`'s message
tie (its `r` is 64: whole blocks); otherwise the final block is the main chain's last. -/
theorem fin_main {κ : NodeKind} {a k : ℕ} {w : Asg} (hk : 1 ≤ k) (hkm : k ≤ κ.maxK)
    (hpad : N4c.AggPad4 κ a k w) {e : ℕ} (he : e / 4 + 1 = N4c.streamL κ (N4c.aggChild κ a) k) :
    N4c.finBlk κ (N4c.aggChild κ a) k = N4c.chBase κ (N4c.aggChild κ a) + e / 4 ∨
      ∀ x < 512, N4c.zN4 w (N4c.finBlk κ (N4c.aggChild κ a) k) (512 + x) =
        N4c.zN4 w (N4c.chBase κ (N4c.aggChild κ a) + e / 4) (512 + x) := by
  have hA := isAgg_aggChild κ a
  simp only [N4c.streamL, hA, if_true] at he
  obtain ⟨hb, -, -⟩ := N4c.aggB_blocks hk
  rcases Nat.lt_or_ge k κ.maxK with hlt | hge
  · refine .inr fun x hx => ?_
    have h2 := (hpad.1 hlt).2 x (by omega)
    rwa [show N4c.chBase κ (N4c.aggChild κ a) + N4c.aggL k - 1 = N4c.chBase κ (N4c.aggChild κ a) + e / 4 by
      omega] at h2
  · refine .inl ?_
    have hk' : k = κ.maxK := by omega
    simp only [N4c.finBlk, N4c.chLen, hA, true_and, if_true, show ¬ k < κ.maxK by omega, if_false]
    rw [← hk']; omega

/-- **Every byte of an active slot's segment** (`x < segB`) is byte `x mod 16` of the H cell of its
element `⌊x/16⌋`, given `AggPad4` at every aggregate. -/
theorem slot_byte' {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    (hpad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf) κ w a) w) {x : ℕ} (hx : x < N4c.segB) :
    (slotStr κ v w).getD (segIx κ v * N4c.strideB + x) 0 =
      (F.toBytes (w (sCell (slotB0 κ v) (x / 16))))[x % 16]'(Nat.mod_lt _ (by norm_num)) := by
  obtain ⟨h1, -, h3⟩ := N4c.strideB_eq
  rcases active_cases hv with ⟨hp, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · have h0 : isPrevSlot κ 0 = true := by simp [isPrevSlot, hp]
    have hA : N4c.isAgg κ 0 = false := by
      cases h : N4c.isAgg κ 0
      · rfl
      · simp [N4c.isAgg, hp] at h
    simp only [slotStr, slotSg, slotK, segIx, slotB0, h0, if_true, Nat.zero_mul, Nat.zero_add]
    conv_lhs => rw [show x = 16 * (x / 16) + x % 16 by omega]
    refine chainBytes4_elem' w (Nat.mod_lt _ (by norm_num)) (by simp [N4c.streamB, hA]; omega) fun hb => .inl ?_
    simp only [N4c.streamL, hA, Bool.false_eq_true, if_false] at hb
    simp only [N4c.finBlk, N4c.chLen, hA, Bool.false_eq_true, false_and, if_false]
    omega
  · have hk := kAct_le κ a w
    obtain ⟨-, hsi, hps, -⟩ := sub_facts κ ha (lt_of_lt_of_le hi hk)
    have hsa := slotA_sub κ ha (lt_of_lt_of_le hi hk)
    have hag : aggSlot κ (N4c.sub κ a i) = slotA κ (N4c.sub κ a i) := by unfold aggSlot slotA; rfl
    simp only [slotStr, slotSg, slotK, segIx, slotB0, hps, if_false, Bool.false_eq_true, hsi, hsa, hag]
    have hA := isAgg_aggChild κ a
    have hk1 : 1 ≤ kAct κ a w := by omega
    obtain ⟨-, -, hB⟩ := N4c.aggB_blocks hk1
    have hik : i * N4c.strideB + N4c.strideB ≤ kAct κ a w * N4c.strideB := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    have hm : i * N4c.strideB = 64 * (i * N4c.sBlk) := by rw [h1]; ring
    have hs : N4c.strideB = N4c.segB + 128 := by decide
    rw [show i * N4c.strideB + x = 16 * (4 * (i * N4c.sBlk) + x / 16) + x % 16 by omega,
      chainBytes4_elem' w (Nat.mod_lt _ (by norm_num))
        (by simp only [N4c.streamB, hA, if_true]; omega)
        (fin_main hk1 hk (by rw [← kA_rd4 pf κ ha w]; exact hpad a ha)), sCell_add]

/-! ## Entries -/

theorem itOff_slen {k : ℕ} (hk : k < (itemsOf seq4).length) : 1 + itOff k + 8 + (itAt k).qlen + 32 ≤ N4c.segB := by
  have := itOff_le hk; have : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl; omega

/-- **Entry `k`'s query byte `j`** at an active slot, every item. -/
theorem slot_qbyte' {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    (hpad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf) κ w a) w)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    {j : ℕ} (hj : j < (itAt k).qlen) :
    byteAt e.1 j = (F.toBytes (w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j) / 16))))[(1 + itOff k + 8 + j) % 16]'(
      Nat.mod_lt _ (by norm_num)) := by
  rw [slotTr4_getElem?, itAt_eq hk, Option.map_some, Option.some.injEq] at he
  subst he
  have hs := itOff_slen hk
  have hL := slotStr_len hv
  rw [entryAt_qbyte _ _ _ hj (by omega),
    show 1 + segIx κ v * N4c.strideB + itOff k + 8 + j = segIx κ v * N4c.strideB + (1 + itOff k + 8 + j) by omega,
    slot_byte' hv hpad (by omega)]

/-- **Entry `k`'s answer** at an active slot, every item: its halves are the H cells of elements
`ansE k`, `ansE k + 1`. -/
theorem slot_ans' {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    (hpad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf) κ w a) w)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e) :
    dlo e.2 = w (sCell (slotB0 κ v) (ansE k)) ∧ dhi e.2 = w (sCell (slotB0 κ v) (ansE k + 1)) := by
  rw [slotTr4_getElem?, itAt_eq hk, Option.map_some, Option.some.injEq] at he
  subst he
  have hal := ans_al hk
  have hs := itOff_slen hk
  have key : ∀ (h : ℕ) (r : Fin 16) (_hh : h < 2),
      (Read.entryAt (slotStr κ v w) (1 + segIx κ v * N4c.strideB + itOff k) (itAt k)).2[16 * h + r.1]'(by omega) =
        (F.toBytes (w (sCell (slotB0 κ v) (ansE k + h))))[r.1] := fun h r hh => by
    rw [entryAt_abyte _ _ _ (16 * h + r.1) (by omega)]
    rw [show 1 + segIx κ v * N4c.strideB + itOff k + 8 + (itAt k).qlen + (16 * h + r.1) =
        segIx κ v * N4c.strideB + (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) by omega,
      slot_byte' hv hpad (by have := r.2; omega)]
    have e1 : (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) / 16 = ansE k + h := by unfold ansE; omega
    have e2 : (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) % 16 = r.1 := by omega
    simp only [e1, e2]
  constructor
  · rw [dlo, ← F.ofBytes_toBytes (w (sCell (slotB0 κ v) (ansE k)))]
    refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
    rw [Vector.getElem_ofFn]
    simpa using key 0 ⟨r, hr⟩ (by norm_num)
  · rw [dhi, ← F.ofBytes_toBytes (w (sCell (slotB0 κ v) (ansE k + 1)))]
    refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
    rw [Vector.getElem_ofFn]
    exact key 1 ⟨r, hr⟩ (by norm_num)

/-! ## The tags -/

theorem wfData_get : ∀ (its : List Item) (o k : ℕ), (wfData o its)[k]? =
    its[k]?.map fun it => ((o + ((its.take k).map Item.slen).sum) / 16, winF (o + ((its.take k).map Item.slen).sum) it)
  | [], _, _ => rfl
  | it :: its, o, 0 => by simp [wfData]
  | it :: its, o, k + 1 => by
    rw [wfData, List.getElem?_cons_succ, wfData_get its, List.getElem?_cons_succ, List.take_succ_cons,
      List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **Item `k ≥ 1`'s first element is pinned** (`wfSeg`). -/
theorem wfSeg_mem {k : ℕ} (hk1 : 1 ≤ k) (hk : k < (itemsOf seq4).length) :
    (itE k, winF (1 + itOff k) (itAt k)) ∈ wfSeg := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine List.mem_of_getElem? (i := j) ?_
  rw [wfSeg, List.getElem?_tail, wfData_get, itAt_eq hk]; rfl

theorem itAt_seed : itAt 0 = .seed := by
  obtain ⟨rest, hr, -⟩ := itemsOf_seq4_al; simp [itAt, hr]

theorem itAt_ne_seed {k : ℕ} (hk1 : 1 ≤ k) (hk : k < (itemsOf seq4).length) : itAt k ≠ .seed := by
  obtain ⟨rest, hr, hal⟩ := itemsOf_seq4_al
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : j < rest.length := by rw [hr] at hk; simpa using hk
  have hit : itAt (j + 1) = rest[j] := by simp [itAt, hr, List.getD_eq_getElem?_getD, hj]
  intro h
  have := (hal rest[j] (List.getElem_mem hj)).1
  rw [← hit, h] at this; exact absurd this (by decide)

theorem toBytes_idx {a b : F} (h : a = b) {r s : ℕ} (hrs : r = s) (hr : r < 16) :
    (F.toBytes a)[r]'hr = (F.toBytes b)[s]'(hrs ▸ hr) := by subst h hrs; rfl

theorem itemTag_len (it : Item) : (itemTag it).length = if it = .seed then 7 else 8 := by
  cases it <;> rfl

/-- **The first query element's alignment**: past the length word and the tag, item `k`'s query is on
an element boundary (the seed's `vk` at element 1, every other query's first digest). -/
theorem qAl {k : ℕ} (hk : k < (itemsOf seq4).length) : (1 + itOff k + 8 + (itemTag (itAt k)).length) % 16 = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [itAt_seed]; rfl
  · rw [itemTag_len, if_neg (itAt_ne_seed hk1 hk)]; have := itOff_al hk1; omega

/-- **An entry's tag is its item's**, at an active slot whose rows hold. -/
theorem tag_byte {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {v : ℕ}
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) (hv : N4c.Active4 (rd4 pf4) κ w v)
    (hvs : v < κ.vslots) (hpad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf4) κ w a) w)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    {j : ℕ} (hj : j < (itemTag (itAt k)).length) : byteAt e.1 j = (itemTag (itAt k)).getD j 0 := by
  have hjq : j < (itAt k).qlen := by
    have := itemTag_len (itAt k); cases h : itAt k <;> simp [h, Item.qlen] at this hj ⊢ <;> omega
  rw [slot_qbyte' hv hpad hk he hjq]
  obtain ⟨G, hG⟩ : ∃ G, packB κ v = some (slotB0 κ v, G) := by
    have := packB_b0 κ v
    rcases h : packB κ v with _ | ⟨b, G⟩
    · rw [h] at this; cases this
    · rw [h] at this; simp at this; exact ⟨G, by rw [this]⟩
  obtain ⟨hpin, -, hhd⟩ := pins_of hS hvs hG
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [itAt_seed] at hj ⊢
    have hj7 : j < 7 := by simpa [itemTag, tagSeed] using hj
    have e1 : (1 + itOff 0 + 8 + j) / 16 = 0 := by simp [itOff]; omega
    have e2 : (1 + itOff 0 + 8 + j) % 16 = 9 + j := by simp [itOff]; omega
    simp only [e1, e2]
    rw [hhd.e0 _ (by omega) (by omega), seedW, winF, winFB, F.toBytes_ofBytes, Vector.getElem_ofFn]
    interval_cases j <;> rfl
  · have hal := itOff_al hk1
    have hne := itAt_ne_seed hk1 hk
    have hj8 : j < 8 := by rw [itemTag_len, if_neg hne] at hj; exact hj
    have e1 : (1 + itOff k + 8 + j) / 16 = itE k := by unfold itE; omega
    have e2 : (1 + itOff k + 8 + j) % 16 = 8 + j := by omega
    have hm := wfSeg_mem hk1 hk
    have hp := hpin _ hm
    dsimp only at hp
    have hp' : w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j) / 16)) = winF (1 + itOff k) (itAt k) := by
      rw [e1]; exact hp
    rw [toBytes_idx hp' e2, winF, winFB, F.toBytes_ofBytes,
      Vector.getElem_ofFn]
    simp only [winB, show (1 + itOff k) % 16 ≠ 1 by omega, if_false, List.nil_append]
    rw [List.getD_append_right _ _ _ _ (by simp [enc64])]
    simp [enc64]

end N4s
end FR
