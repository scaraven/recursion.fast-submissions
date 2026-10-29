-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2, A.5, A.7; stage S-E13a, track L-circ):
-- S-N2's `Gap4.kindN`, `.kindS` (first sub-slot) and `.wf` (aligned segments) from the pack rows.
import FRNodeSound4K
import FRNodeRows4Pack
import FRNodeRows4Agg

/-!
# What the pack rows give: the kind tie and the stream's constant bytes

The pack rows of `FRNodeRows4.packRows4` sit in the link region of the slots whose stream segment is
16-aligned (the previous node's slot and each aggregate's first sub-slot). From them and the node's
truths (`StmtN4` at `lRows4`, `nodeIRows4`):

* **the bytes of an H element** (`chainBytes4_elem`): stream byte `16e + r` is byte `r` of the F
  element in cell `sCell b0 e` (A.7's pack; `unpack`, `bitF`, `F.toBytes`);
* **the kind tie** (`kindN_of_rows`, `kindS0_of_rows`): stream element 5 is `hdr[0…16)`, which the
  kind row equates to the selected index's constant, so byte 0 of the read proof is the selected
  kind's byte — given that `pf` takes `hdr` from the seed query (`PfHdr`, A.5's `reassemble`);
* **`wf`** (`wf0_of_rows`): the stream's tag and every item's length word of the aligned segment.

**`Gap4R`** is `Gap4` without what these rows give: `kindN` entirely, `kindS` at the first
sub-slot, `wf`'s tag and segment 0. **`gap4_of_rows`**: `StmtN4` + `PfHdr pf` + `Gap4R` give
`Gap4`; **`ks_rev4GR`**, **`certificate_rev4GR`**: `ks_rev4GH`, `certificate_rev4GH` with `hGap`
replaced by `PfHdr pf` and `Gap4R`.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval ProductCircuit

/-! ## The bytes of an H element -/

theorem toBytes_get (a : F) (r : ℕ) (hr : r < 16) :
    (F.toBytes a)[r] = if r < 8 then (a.c₀.val >>> (8 * r).toUInt64).toUInt8
      else (a.c₁.val >>> (8 * (r - 8)).toUInt64).toUInt8 := by
  interval_cases r <;> rfl

/-- Bit `i` of byte `r` of an element is its pack bit `8r + i` (A.7). -/
theorem toBytes_bit (a : F) (r i : ℕ) (hr : r < 16) (hi : i < 8) :
    (F.toBytes a)[r].toBitVec.getLsbD i = bitF a ⟨8 * r + i, by omega⟩ := by
  rw [toBytes_get a r hr, bitF]
  simp only [Fin.val_mk]
  split_ifs with h1 h2 h2
  · simp [hi]; congr 1; omega
  · omega
  · omega
  · simp [hi]; congr 1; omega

theorem decide_unpack (a : F) (j : Fin 128) : decide (unpack a j = 1) = bitF a j := by
  unfold unpack; cases bitF a j <;> simp

/-- A block's message position `512 + 128 s + 8 r + i` is bit `8 r + i` of the block's element
`4 + s`. -/
theorem bitsB4_cell (w : Asg) (blk : ℕ) {s r i : ℕ} (hs : s < 4) (hr : r < 16) (hi : i < 8) :
    N4c.bitsB4 w blk (pos (512 + 128 * s + 8 * r + i)) = bitF (w (blk * 128 + 4 + s)) ⟨8 * r + i, by omega⟩ := by
  rw [N4c.bitsB4_pos w blk (by omega), N4c.zN4, N4c.zW4, ← decide_unpack]
  have h1 : (blk * 2 ^ 14 + (512 + 128 * s + 8 * r + i)) / 128 = blk * 128 + 4 + s := by omega
  have h2 : (blk * 2 ^ 14 + (512 + 128 * s + 8 * r + i)) % 128 = 8 * r + i := by omega
  simp only [h1, h2]

/-- **A message byte is a byte of the block's element** (A.7's pack). -/
theorem readByte_cell (w : Asg) (blk : ℕ) {s r : ℕ} (hs : s < 4) (hr : r < 16) :
    Block.readByte (N4c.bitsB4 w blk) (512 + 128 * s + 8 * r) = (F.toBytes (w (blk * 128 + 4 + s)))[r] := by
  refine UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi => ?_)
  rw [Block.readByte_getLsbD _ _ hi, bitsB4_cell w blk hs hr hi, toBytes_bit _ _ _ hr hi]

/-- **Stream byte `16 e + r` is byte `r` of the H cell `sCell` of element `e`** (outside the last
block, which may be an aggregate's candidate final block). -/
theorem chainBytes4_elem {κ : NodeKind} {σ k : ℕ} (w : Asg) {e r : ℕ} (hr : r < 16)
    (hp : 16 * e + r < N4c.streamB κ σ k) (hb : e / 4 + 1 ≠ N4c.streamL κ σ k) :
    (N4c.chainBytes4 κ σ k w).getD (16 * e + r) 0 = (F.toBytes (w (sCell (N4c.chBase κ σ) e)))[r] := by
  obtain ⟨h1, h2⟩ := Stream.elem_slot e r hr
  rw [N4c.chainBytes4, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hp, Option.map_some, Option.getD_some, h1, h2]
  simp only [N4c.chainW4, N4c.blkOf, if_neg hb]
  rw [show 128 * (4 + e % 4) + 8 * r = 512 + 128 * (e % 4) + 8 * r by ring,
    readByte_cell w _ (Nat.mod_lt _ (by norm_num)) hr]
  rfl

/-- The stream of a signed child (an aggregate with `k ≥ 1` segments) holds one trace: its bytes
and blocks bound those of a segment. -/
theorem stream_ge {κ : NodeKind} {σ k : ℕ} (hk : N4c.isAgg κ σ = true → 1 ≤ k) :
    N4c.segB ≤ N4c.streamB κ σ k ∧ N4c.cLen ≤ N4c.streamL κ σ k := by
  have hs : N4c.segB = 64 * N4c.cLen := by decide
  unfold N4c.streamB N4c.streamL N4c.aggL N4c.aggB
  by_cases h : N4c.isAgg κ σ = true
  · have := hk h
    rw [if_pos h, if_pos h]
    have : N4c.segB - 1 ≤ k * (N4c.segB - 1) := Nat.le_mul_of_pos_left _ this
    have : N4c.segB ≤ 1 + k * (N4c.segB - 1) := by omega
    exact ⟨this, by omega⟩
  · rw [if_neg h, if_neg h]; exact ⟨le_rfl, le_rfl⟩

/-- **An element of the stream's first segment** (`16 e + 80 ≤ segB`) is read off its main-chain
cell. -/
theorem seg0_elem {κ : NodeKind} {σ k : ℕ} (w : Asg) (hk : N4c.isAgg κ σ = true → 1 ≤ k) {e r : ℕ}
    (hr : r < 16) (he : 16 * e + 80 ≤ N4c.segB) :
    (N4c.chainBytes4 κ σ k w).getD (16 * e + r) 0 = (F.toBytes (w (sCell (N4c.chBase κ σ) e)))[r] := by
  obtain ⟨h1, h2⟩ := stream_ge hk
  have hs : N4c.segB = 64 * N4c.cLen := by decide
  exact chainBytes4_elem w hr (by omega) (by omega)

/-! ## `seq4`'s items: the seed, then 16-byte multiples -/

/-- The shapes whose items all take a multiple of 16 bytes (the seed's take 159). -/
def shAl : Sh → Bool
  | .seed => false
  | .absorb _ len => len % 16 == 0
  | .squeezes _ _ => true
  | .uni _ => true
  | .rounds _ _ _ _ => true
  | .queries i => colBytes i % 16 == 0 && decide (32 ≤ colBytes i)

theorem sh_al (lv : ℕ → Level) {sh : Sh} (h : shAl sh = true) :
    ∀ it ∈ sh.itemsL lv, it.slen % 16 = 0 ∧ 80 ≤ it.slen := by
  intro it hit
  cases sh with
  | seed => exact absurd h (by decide)
  | absorb f len =>
    simp only [shAl, beq_iff_eq] at h
    simp [Sh.itemsL] at hit; subst hit; simp [Item.slen, Item.qlen]; omega
  | squeezes n ch =>
    simp only [Sh.itemsL, List.mem_replicate] at hit; rw [hit.2]; simp [Item.slen, Item.qlen]
  | uni f =>
    simp only [Sh.itemsL, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> simp [Item.slen, Item.qlen, uniBytes]
  | rounds f n deg inK =>
    simp only [Sh.itemsL, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> cases inK <;> simp [Item.slen, Item.qlen, roundBytes]
  | queries i =>
    simp only [shAl, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    simp only [Sh.itemsL, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
    simp only [posItemsL, List.mem_cons, List.mem_map, List.mem_range] at hl
    rcases hl with rfl | ⟨h', -, rfl⟩ <;> simp [Item.slen, Item.qlen] <;> omega

theorem phasesOf_cons : ∃ tl, phasesOf seq4 = ("seed", .seed) :: tl := ⟨_, rfl⟩

/-- Every `seq4` phase after the seed has 16-byte items (its shape parameters only). -/
theorem phasesOf_al : ((phasesOf seq4).tail).all (fun p => shAl p.2) = true := by
  rw [seq4_eq]; decide +kernel

/-- **`seq4`'s items**: the seed, then items of a multiple of 16 bytes, each at least 80. -/
theorem itemsOf_seq4_al : ∃ rest, itemsOf seq4 = .seed :: rest ∧ ∀ it ∈ rest, it.slen % 16 = 0 ∧ 80 ≤ it.slen := by
  obtain ⟨tl, htl⟩ := phasesOf_cons
  have hal := phasesOf_al
  rw [htl, List.tail_cons] at hal
  refine ⟨tl.flatMap fun p => p.2.itemsL seq4.lv, ?_, fun it hit => ?_⟩
  · rw [itemsOf, htl, List.flatMap_cons]; rfl
  · obtain ⟨p, hp, hit⟩ := List.mem_flatMap.1 hit
    exact sh_al _ (List.all_eq_true.1 hal p hp) it hit

/-! ## The pins give the stream's constant bytes -/

/-- The offsets the items of `its` start at, from `o`, are `≡ 0` or `1 (mod 16)`. -/
def AlAt : ℕ → List Item → Prop
  | _, [] => True
  | o, it :: its => o % 16 ≤ 1 ∧ AlAt (o + it.slen) its

theorem alAt_of (o : ℕ) (its : List Item) (ho : o % 16 = 0) (h : ∀ it ∈ its, it.slen % 16 = 0) :
    AlAt o its := by
  induction its generalizing o with
  | nil => trivial
  | cons it its ih =>
    refine ⟨by omega, ih _ ?_ fun it' h' => h it' (List.mem_cons_of_mem _ h')⟩
    have := h it List.mem_cons_self
    omega

/-- Bytes `ρ … ρ + 7` of an item's element value are its length word (`ρ = o mod 16 ≤ 1`). -/
theorem winF_word (o : ℕ) (it : Item) (ho : o % 16 ≤ 1) {t : ℕ} (ht : t < 8) :
    (F.toBytes (winF o it))[o % 16 + t]'(by omega) = (enc64 it.qlen).getD t 0 := by
  rw [winF, winFB, F.toBytes_ofBytes, Vector.getElem_ofFn]
  simp only [winB]
  have hl : (enc64 it.qlen).length = 8 := by simp [enc64]
  rcases (by omega : o % 16 = 0 ∨ o % 16 = 1) with h | h
  · rw [h, if_neg (by omega), List.nil_append, Nat.zero_add,
      List.getD_append _ _ _ _ (by omega)]
  · rw [h, if_pos rfl, List.singleton_append, Nat.add_comm,
      List.getD_append _ _ _ _ (by simp only [List.length_cons]; omega), List.getD_cons_succ]

/-- **The pins give the length words.** If every pinned element of `wfData o its` has its value's
bytes in `B`, and the items start at offsets `≡ 0, 1 (mod 16)` inside `B`, the length words are in
place. -/
theorem wfAt_of_pins (B : List UInt8) : ∀ (its : List Item) (o : ℕ), AlAt o its →
    o + slenL its ≤ B.length →
    (∀ p ∈ wfData o its, ∀ r (hr : r < 16), B.getD (16 * p.1 + r) 0 = (F.toBytes p.2)[r]) → WfAt B o its
  | [], _, _, _, _ => trivial
  | it :: its, o, ⟨ho, hal⟩, hl, hp => by
    have hs : slenL (it :: its) = it.slen + slenL its := by simp [slenL]
    have h8 : 8 ≤ it.slen := by simp [Item.slen]
    refine ⟨?_, wfAt_of_pins B its _ hal (by omega) fun p hp' => hp p (List.mem_cons_of_mem _ hp')⟩
    have h0 := hp (o / 16, winF o it) List.mem_cons_self
    refine List.ext_getElem (by simp [enc64]; omega) fun t h₁ h₂ => ?_
    have ht : t < 8 := by simpa [enc64] using h₂
    have := h0 (o % 16 + t) (by omega)
    dsimp only at this
    rw [show 16 * (o / 16) + (o % 16 + t) = o + t by omega, winF_word o it ho ht] at this
    rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0, this,
      List.getD_eq_getElem _ 0 (by simp [enc64]; omega)]

theorem slenL_seq4 : 1 + slenL (itemsOf seq4) = N4c.segB := by
  rw [N4c.segB_eq, streamBytesOf, slenL]; congr 2

theorem wfData_lt80 : ∀ (o : ℕ) (its : List Item), (∀ it ∈ its, 80 ≤ it.slen) →
    ∀ q ∈ wfData o its, 16 * q.1 + 80 ≤ o + slenL its
  | _, [], _ => by simp [wfData]
  | o, it :: its, h80 => by
    intro q hq
    simp only [wfData, List.mem_cons] at hq
    have hs : slenL (it :: its) = it.slen + slenL its := by simp [slenL]
    have := h80 it List.mem_cons_self
    rcases hq with rfl | hq
    · dsimp only; omega
    · have := wfData_lt80 (o + it.slen) its (fun it' h' => h80 it' (List.mem_cons_of_mem _ h')) q hq
      omega

/-- **A pinned element of a segment lies in the segment's main-chain blocks.** -/
theorem wfSeg_lt80 : ∀ p ∈ wfSeg, 16 * p.1 + 80 ≤ N4c.segB := fun p hp => by
  obtain ⟨rest, hr, hal⟩ := itemsOf_seq4_al
  have h80 : ∀ it ∈ itemsOf seq4, 80 ≤ it.slen := by
    rw [hr]; intro it hit
    rcases List.mem_cons.1 hit with rfl | hit
    · decide
    · exact (hal it hit).2
  have := wfData_lt80 1 (itemsOf seq4) h80 p hp
  have := slenL_seq4
  omega

/-- **A stream whose segment-0 pins hold** has its tag and segment 0's length words. -/
theorem wf0_of_pins {κ : NodeKind} {σ k : ℕ} {w : Asg} (hk : N4c.isAgg κ σ = true → 1 ≤ k)
    (hpin : ∀ p ∈ wfSeg, w (sCell (N4c.chBase κ σ) p.1) = p.2) :
    (N4c.chainBytes4 κ σ k w).head? = some tagTrace ∧
      WfAt (N4c.chainBytes4 κ σ k w) 1 (itemsOf seq4) := by
  have hB : ∀ p ∈ wfSeg, ∀ r (hr : r < 16),
      (N4c.chainBytes4 κ σ k w).getD (16 * p.1 + r) 0 = (F.toBytes p.2)[r] := fun p hp r hr => by
    rw [seg0_elem w hk hr (wfSeg_lt80 p hp), hpin p hp]
  have hlen : N4c.segB ≤ (N4c.chainBytes4 κ σ k w).length := by
    rw [N4c.chainBytes4, Stream.streamBytes_length]; exact (stream_ge hk).1
  obtain ⟨rest, hr, hal⟩ := itemsOf_seq4_al
  refine ⟨?_, ?_⟩
  · have h0 := hB (0, winF 1 .seed) (by rw [wfSeg, hr]; exact List.mem_cons_self) 0 (by norm_num)
    dsimp only at h0
    rw [Nat.mul_zero, Nat.add_zero, winF, winFB, F.toBytes_ofBytes, Vector.getElem_ofFn] at h0
    have hpos : 0 < (N4c.chainBytes4 κ σ k w).length := lt_of_lt_of_le (by decide) hlen
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos, ← List.getD_eq_getElem _ 0, h0]
    rfl
  · refine wfAt_of_pins _ (itemsOf seq4) 1 ?_ (by rw [slenL_seq4]; exact hlen) (fun p hp => hB p hp)
    rw [hr]
    exact ⟨by norm_num, alAt_of _ rest (by decide) fun it h => (hal it h).1⟩

/-! ## The kind byte -/

/-- **What `pf` must do with the header** (A.5's `reassemble`: `hdr := payload₀[64…111]`): byte 0
of the proof is byte 71 of the first query (the seed's 7-byte tag, then `vk`, `c`, `hdr`). -/
def PfHdr (pf : Trace → Proof) : Prop := ∀ e tr, byteAt (pf (e :: tr)) 0 = byteAt e.1 71

theorem byteAt_slotPf (pf : Trace → Proof) (κ : NodeKind) (v : ℕ) (w : Asg) :
    byteAt (⟨(slotPf pf κ v w).toArray⟩ : Proof) 0 = byteAt (pf (slotTr4 κ v w)) 0 := by
  rw [byteAt_mk, slotPf, fitL]
  have hn : 0 < piSizeOf seq4 := by rw [piSizeOf_seq4]; norm_num
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hn, List.getElem?_append]
  conv_rhs => rw [show pf (slotTr4 κ v w) = ⟨(pf (slotTr4 κ v w)).data.toList.toArray⟩ from rfl, byteAt_mk]
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD]
  · simp only [not_lt, Nat.le_zero, List.length_eq_zero_iff] at h
    simp [h]

/-- **Byte 0 of a slot's proof read off segment 0** is stream byte 80, element 5's byte 0. -/
theorem kind_byte (pf : Trace → Proof) (hpf : PfHdr pf) {κ : NodeKind} {σ k : ℕ} {w : Asg}
    (hk : N4c.isAgg κ σ = true → 1 ≤ k) :
    byteAt (pf (segTr κ σ k 0 w)) 0 = (F.toBytes (w (sCell (N4c.chBase κ σ) 5)))[0] := by
  obtain ⟨rest, hr, -⟩ := itemsOf_seq4_al
  rw [segTr, hr, Read.readItems, Nat.zero_mul, Nat.add_zero, hpf, ← seg0_elem w hk (by norm_num) (by decide)]
  rw [byteAt_mk]
  show (((N4c.chainBytes4 κ σ k w).drop (1 + 8)).take Item.seed.qlen).getD 71 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by decide), List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]

/-- **The kind row and a selected index give the index's constant.** -/
theorem kindRow_sel {κ : NodeKind} {σ : ℕ} {w : Asg} {G : Grp} {h5 : ℕ} {ι : Kind} (hone : w κ.oneCell = 1)
    (h : (kindRow κ.oneCell h5 (fun ι => κ.oneCell + selR σ ι) G).Holds w)
    (hS : SelOk (slotAsg κ σ w) (protoP (protoOf κ σ)) ι) : w h5 = kConst G ι := by
  have hsel : ∀ ι', w (κ.oneCell + selR σ ι') = if ι' = ι then 1 else 0 := fun ι' => by
    rw [← slotAsg_sel κ σ w ι']; simpa [protoP, Lin.ev_cell] using hS.2 ι'
  rw [kindRow_holds hone h, hsel, hsel, hsel]
  cases ι <;> simp

/-! ## `Gap4` from the pack rows -/

section Gap
variable {impl₀ : OpImpl} {base : NodeKind → OpImpl} (pf : Trace → Proof) {κ : NodeKind}
  {vk c₁ c₂ : Digest} {w : Asg}

/-- **`Gap4` without what the M rows give** (S-E13a): the kind byte of the aggregates' later
sub-slots and the length words of their segments (unaligned: B1), `imp`, `aggChk`; `wots` and
`aggPad` are S-E13b's rows (`wots_aggPad_of_rows`). -/
structure Gap4R (impl₀ : OpImpl) (base : NodeKind → OpImpl) (pf : Trace → Proof) (κ : NodeKind)
    (vk c₁ c₂ : Digest) (w : Asg) : Prop where
  imp : ∀ v, N4c.Active4 (rd4 pf) κ w v →
    SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)
  kindS : ∀ a < N4c.nAgg κ, ∀ i < kAct κ a w, 0 < i → ∀ ι, SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι →
    byteAt ((rd4 pf).slotπ κ (N4c.sub κ a i) w) 0 = (segAt ι).byte
  wf : ∀ σ < 2, ∀ i < nSeg κ σ w, 0 < i →
    WfAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (1 + i * (N4c.segB - 1)) (itemsOf seq4)
  aggChk : ∀ a < N4c.nAgg κ, ∃ vs, (aggSegs (piSizeOf seq4) (N4c.kA (rd4 pf) κ w a)
      ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π).mapM segView = some vs ∧
    aggChecks (N4c.stOf c₁ c₂ (N4c.aggChild κ a)) (rdLE64 ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 8)
      (bytesAt ((rd4 pf).sgn κ (N4c.aggChild κ a) w).π 16 32) vs = true

/-- **S-E13b's node rows give `Gap4.wots` and `Gap4.aggPad`** (`W4.gap4_wots_aggPad`), with the
fold: the node rows are slot 1's link rows when their cell check passes; otherwise slot 1 holds the
rejecting row, which no `StmtN4` witness meets. -/
theorem wots_aggPad_of_rows (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    (∀ σ < 2, SigOk vk (N4c.hDig4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) ((rd4 pf).sgn κ σ w).σ = true) ∧
      ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf) κ w a) w := by
  by_cases h : xOkK κ = true
  · refine W4.gap4_wots_aggPad pf (fun r hr => ?_) hS
    refine List.mem_append_right _ ?_
    rw [extRowsC, if_pos rfl, if_pos h, xRowsK_eq]; exact hr
  · exfalso
    obtain ⟨-, -, -, hE, hP⟩ := hS
    have hone := one_of_pubCells hP
    have h1 : 1 < κ.vslots := by cases κ <;> decide
    have := linkRows_hold (protoFit_of hone hE) h1 hE (rejR κ)
      (List.mem_append_right _ (by rw [extRowsC, if_pos rfl, if_neg h]; simp))
    simp [rejR, Row.Holds, hone] at this

/-- The pack rows of slot `v` hold (they are link rows). -/
theorem packRows_hold {v : ℕ} (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) (hv : v < κ.vslots) :
    ∀ r ∈ packRows4 κ v, r.Holds w := by
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hF := protoFit_of (one_of_pubCells hP) hE
  exact fun r hr => linkRows_hold hF hv hE r (List.mem_append_left _ (List.mem_append_right _ hr))

/-- The pins of a slot whose segment base is `b0`. -/
theorem pins_of {v b0 : ℕ} {G : Grp} (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hv : v < κ.vslots) (hb : packB κ v = some (b0, G)) :
    (∀ p ∈ wfSeg, w (sCell b0 p.1) = p.2) ∧
      (kindRow κ.oneCell (sCell b0 5) (fun ι => κ.oneCell + selR v ι) G).Holds w := by
  have hone := one_of_pubCells hS.2.2.2.2
  have h := packRows_hold hS hv
  refine ⟨fun p hp => pinRow_holds hone (h _ ?_), h _ ?_⟩
  · simp only [packRows4, packWf4, hb, List.mem_append]
    exact Or.inr (List.mem_map.2 ⟨p, hp, rfl⟩)
  · simp [packRows4, packHead4, hb]

theorem packB_prev (hp : κ.hasPrev = true) : packB κ 0 = some (N4c.chBase κ 0, nodeGrp) := by
  simp [packB, isPrevSlot, hp]

theorem packB_sub {a : ℕ} (ha : a < N4c.nAgg κ) (h0 : 0 < κ.maxK) :
    packB κ (N4c.sub κ a 0) = some (N4c.chBase κ (N4c.aggChild κ a), segGrp) := by
  obtain ⟨-, hx, hp, -⟩ := sub_facts κ ha h0
  have hs : aggSlot κ (N4c.sub κ a 0) = a := slotA_sub κ ha h0
  simp only [packB, hp, hx, hs, Bool.false_eq_true, if_false, if_true]

theorem maxK_pos (κ : NodeKind) : 0 < κ.maxK := by cases κ <;> decide

/-- **`gap4_of_rows`**: the node's truths, `PfHdr pf` and `Gap4R` give S-N2's `Gap4`. -/
theorem gap4_of_rows (hpf : PfHdr pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hG : Gap4R impl₀ base pf κ vk c₁ c₂ w) : Gap4 impl₀ base pf κ vk c₁ c₂ w := by
  have hone := one_of_pubCells hS.2.2.2.2
  have hF := protoFit_of hone hS.2.2.2.1
  have hL := hS.2.2.1
  have hlk : ∀ a < N4c.nAgg κ, ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w :=
    fun a ha i hi => linkRows_hold hF (sub_facts κ ha hi).1 hS.2.2.2.1
  have hk1 : ∀ a < N4c.nAgg κ, 1 ≤ kAct κ a w := fun a ha =>
    (actK_kAct hone ha hL (hlk a ha)).1
  -- the stream's segment count
  have hkσ : ∀ σ < 2, N4c.isAgg κ σ = true → 1 ≤ N4c.kOf (rd4 pf) κ w σ := fun σ hσ hA => by
    obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
    rw [N4c.kOf, if_pos hA, kA_rd4 pf κ ha]; exact hk1 _ ha
  -- the pins of signed child `σ`
  have hpinσ : ∀ σ < 2, ∀ p ∈ wfSeg, w (sCell (N4c.chBase κ σ) p.1) = p.2 := fun σ hσ => by
    by_cases hA : N4c.isAgg κ σ = true
    · obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
      have h := (pins_of hS (sub_facts κ ha (maxK_pos κ)).1 (packB_sub ha (maxK_pos κ))).1
      rwa [hc] at h
    · have hp : κ.hasPrev = true ∧ σ = 0 := by cases κ <;> simp_all [N4c.isAgg, NodeKind.hasPrev]
      obtain ⟨hp, rfl⟩ := hp
      exact (pins_of hS (vslots_pos κ) (packB_prev hp)).1
  obtain ⟨hwots, hpad⟩ := wots_aggPad_of_rows pf hS
  refine ⟨hG.imp, ?_, ?_, ?_, hG.aggChk, hpad, hwots⟩
  · -- kindN
    intro hp ι hι
    obtain ⟨-, hrow⟩ := pins_of hS (vslots_pos κ) (packB_prev hp)
    have h5 := kindRow_sel hone hrow (by rw [protoOf_zero hp]; exact hι)
    have hk0 : N4c.isAgg κ 0 = true → 1 ≤ 0 := fun h => by simp [isAgg_zero hp] at h
    show byteAt (sgn4 pf κ 0 w).π 0 = _
    rw [sgn4, if_neg (by simp [isAgg_zero hp]), byteAt_slotPf]
    simp only [slotTr4, isPrevSlot, hp, Bool.true_and, beq_self_eq_true, if_true]
    rw [kind_byte pf hpf hk0, h5]
    exact (kConst_byte ι).1
  · -- kindS
    intro a ha i hi ι hι
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · obtain ⟨-, hrow⟩ := pins_of hS (sub_facts κ ha (maxK_pos κ)).1 (packB_sub ha (maxK_pos κ))
      obtain ⟨-, hx, hpv, -⟩ := sub_facts κ ha (maxK_pos κ)
      have h5 := kindRow_sel hone hrow (by rw [protoOf_seg hpv]; exact hι)
      show byteAt (⟨(slotPf pf κ (N4c.sub κ a 0) w).toArray⟩ : Proof) 0 = _
      rw [byteAt_slotPf]
      simp only [slotTr4, hpv, Bool.false_eq_true, if_false, slotA_sub κ ha (maxK_pos κ), hx]
      rw [kind_byte pf hpf (fun _ => hk1 a ha), h5]
      exact (kConst_byte ι).2
    · exact hG.kindS a ha i hi hi0 ι hι
  · -- wf
    intro σ hσ
    obtain ⟨hh, h0⟩ := wf0_of_pins (k := N4c.kOf (rd4 pf) κ w σ) (hkσ σ hσ) (hpinσ σ hσ)
    refine ⟨hh, fun i hi => ?_⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using h0
    · exact hG.wf σ hσ i hi hi0

/-- (Converse) `Gap4` gives `Gap4R`: nothing beyond `Gap4` is asked. -/
theorem gap4R_of_gap4 (hG : Gap4 impl₀ base pf κ vk c₁ c₂ w) : Gap4R impl₀ base pf κ vk c₁ c₂ w :=
  ⟨hG.imp, fun a ha i hi _ ι hι => hG.kindS a ha i hi ι hι, fun σ hσ i hi _ => (hG.wf σ hσ).2 i hi,
    hG.aggChk⟩

end Gap

/-! ## Controls -/

/-- (+) The kind row holds at a one-hot selection with the element at the selected constant;
(−) with the element at another index's constant it fails (`kConst_ne`). -/
theorem kindRow_ctl (w : Asg) (one h5 : ℕ) (sel : Kind → ℕ) (hone : w one = 1)
    (hs : w (sel .L32) = 0 ∧ w (sel .P30) = 1 ∧ w (sel .N30) = 0) :
    (w h5 = kConst nodeGrp .P30 → (kindRow one h5 sel nodeGrp).Holds w) ∧
      (w h5 = kConst nodeGrp .L32 → ¬ (kindRow one h5 sel nodeGrp).Holds w) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have key : (kindRow one h5 sel nodeGrp).Holds w ↔ w h5 = kConst nodeGrp .P30 := by
    simp only [kindRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, hone, one_mul, Lin.ev_nil, sub_eq_zero]
    simp [Circ.kinds, Lin.ev, h1, h2, h3]
  refine ⟨key.2, fun h hr => kConst_ne.1 (h.symm.trans (key.1 hr))⟩

/-- (+) A proof decoder that takes byte 0 from the seed query's byte 71 meets `PfHdr`; (−) the
empty decoder does not (a seed query with a kind byte at 71). -/
theorem pfHdr_ctl : PfHdr (fun tr => ⟨#[byteAt (tr.headD (ByteArray.empty, default)).1 71]⟩) ∧
    ¬ PfHdr (fun _ => ByteArray.empty) := by
  refine ⟨fun e tr => ?_, fun h => ?_⟩
  · show byteAt ⟨[byteAt e.1 71].toArray⟩ 0 = _
    rw [byteAt_mk]; rfl
  have := h (⟨(List.replicate 72 (0x4e : UInt8)).toArray⟩, default) []
  revert this; decide

end N4s

namespace Snd.P4f
open RecursionFast FR.Rev4 FR.N4s FR.X.X4 FR.Circ

section G
variable (fin : Finals) (lRows : List Row) (κs₀ : F)

/-- **`ks_rev4GH` with the pack rows** (S-E13a): `hGap` is replaced by `PfHdr pf` (A.5's
`reassemble`, S-H4) and `Gap4R`, which no longer asks for the previous node's kind byte, the first
sub-slot's kind byte, the streams' tag or segment 0's length words. -/
theorem ks_rev4GR (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (hO : R4.SegOut4 (VsegC (Impl.implC fin lRows κs₀)) vk) (pf : Trace → Proof) (hpf : PfHdr pf)
    (hGap : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      Gap4R (Impl.implC fin lRows κs₀) (fun _ => Impl.implC fin lRows κs₀) pf κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, X4.GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV :=
  ks_rev4GH fin lRows κs₀ S vk hV hq hE hε hO pf
    (fun κ w c₁ c₂ hS => gap4_of_rows pf hpf hS (hGap κ w c₁ c₂ hS)) D hL

/-- `Resid4GH` with the pack rows: `PfHdr pf` and `Gap4R` in place of `Gap4`. -/
structure Resid4GR (pf : Trace → Proof) (S : Submission) (nd : X.XIR) (D : NodeDec4 nd) (vk : Digest) :
    Prop where
  out : R4.SegOut4 (VsegC (Impl.implC fin lRows κs₀)) vk
  gap : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
    Gap4R (Impl.implC fin lRows κs₀) (fun _ => Impl.implC fin lRows κs₀) pf κ vk c₁ c₂ w
  links : ∀ κ L c π, X4.GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)

/-- **The contract's `Certificate`** with the pack rows (`certificate_rev4GH` at `Gap4R`). -/
theorem certificate_rev4GR (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd)
    (hfuel : S.fuel = X.fuel) (hnd : DecOk4 nd) (D : NodeDec4 nd) (pf : Trace → Proof) (hpf : PfHdr pf)
    (hR : ∀ vk, Resid4GR fin lRows κs₀ pf S nd D vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S :=
  certificate_rev4GH fin lRows κs₀ S hV hq hE hε hext hfuel hnd D pf
    (fun vk => ⟨(hR vk).out, fun κ w c₁ c₂ hS => gap4_of_rows pf hpf hS ((hR vk).gap κ w c₁ c₂ hS),
      (hR vk).links⟩) hC hδ

end G

end Snd.P4f
end FR
