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
  unfold N4c.streamB N4c.streamL
  by_cases h : N4c.isAgg κ σ = true
  · have hk1 := hk h
    rw [if_pos h, if_pos h]
    obtain ⟨h1, h2, -⟩ := N4c.aggB_blocks hk1
    obtain ⟨-, h4, h5⟩ := N4c.strideB_eq
    have : N4c.sBlk ≤ N4c.sBlk * k := Nat.le_mul_of_pos_right _ hk1
    have : N4c.segB ≤ N4c.aggB k := by rw [h1, h2, h5]; omega
    exact ⟨this, by rw [h2]; omega⟩
  · rw [if_neg h, if_neg h]; exact ⟨le_rfl, le_rfl⟩

/-- **An element of the stream's first segment** (`16 e + 80 ≤ segB`) is read off its main-chain
cell. -/
theorem seg0_elem {κ : NodeKind} {σ k : ℕ} (w : Asg) (hk : N4c.isAgg κ σ = true → 1 ≤ k) {e r : ℕ}
    (hr : r < 16) (he : 16 * e + 80 ≤ N4c.segB) :
    (N4c.chainBytes4 κ σ k w).getD (16 * e + r) 0 = (F.toBytes (w (sCell (N4c.chBase κ σ) e)))[r] := by
  obtain ⟨h1, h2⟩ := stream_ge hk
  have hs : N4c.segB = 64 * N4c.cLen := N4c.strideB_eq.2.2
  exact chainBytes4_elem w hr (by omega) (by omega)

/-! ## An aggregate's later segments and its spacers (R-A′) -/

theorem sCell_add (b0 d e : ℕ) : sCell b0 (4 * d + e) = sCell (b0 + d) e := by
  unfold sCell
  rw [show (4 * d + e) / 4 = d + e / 4 by omega, show (4 * d + e) % 4 = e % 4 by omega]
  ring

/-- **An element of an aggregate's stream before its last block** is read off its main-chain cell. -/
theorem agg_elem {κ : NodeKind} {σ k : ℕ} (w : Asg) (hA : N4c.isAgg κ σ = true) (hk : 1 ≤ k) {e r : ℕ}
    (hr : r < 16) (he : e / 4 + 1 < N4c.aggL k) :
    (N4c.chainBytes4 κ σ k w).getD (16 * e + r) 0 = (F.toBytes (w (sCell (N4c.chBase κ σ) e)))[r] := by
  have hB := (N4c.aggB_blocks hk).1
  refine chainBytes4_elem w hr ?_ ?_
  · simp only [N4c.streamB, hA, if_true]; omega
  · simp only [N4c.streamL, hA, if_true]; omega

/-- **Segment `i`'s element `e`** (`i < k`, `16 e + 80 ≤ segB`) of an aggregate's stream: stream
byte `i·strideB + 16 e + r`, read off the cell `sCell (chBase + i·sBlk) e` (R-A′: segment `i` is
segment 0 shifted by `i·sBlk` blocks). -/
theorem segi_elem {κ : NodeKind} {σ k i : ℕ} (w : Asg) (hA : N4c.isAgg κ σ = true) (hi : i < k) {e r : ℕ}
    (hr : r < 16) (he : 16 * e + 80 ≤ N4c.segB) :
    (N4c.chainBytes4 κ σ k w).getD (i * N4c.strideB + 16 * e + r) 0 =
      (F.toBytes (w (sCell (N4c.chBase κ σ + i * N4c.sBlk) e)))[r] := by
  obtain ⟨h1, h2, h3⟩ := N4c.strideB_eq
  have hL := (N4c.aggB_blocks (k := k) (by omega)).2.1
  have hik : i * N4c.sBlk + N4c.sBlk ≤ k * N4c.sBlk := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  have hc : N4c.sBlk * k = k * N4c.sBlk := Nat.mul_comm _ _
  rw [show i * N4c.strideB + 16 * e + r = 16 * (4 * (i * N4c.sBlk) + e) + r by rw [h1]; ring,
    agg_elem w hA (by omega) hr (by omega), sCell_add]

/-- **Spacer `i`'s element `j`** (`1 ≤ i < k`, `j < 8`): stream byte `i·strideB − 128 + 16 j + r`,
read off the cell `sCell (chBase + i·sBlk − 2) j`. -/
theorem spc_elem {κ : NodeKind} {σ k i : ℕ} (w : Asg) (hA : N4c.isAgg κ σ = true) (hi1 : 1 ≤ i) (hi : i < k)
    {j r : ℕ} (hj : j < 8) (hr : r < 16) :
    (N4c.chainBytes4 κ σ k w).getD (i * N4c.strideB - 128 + 16 * j + r) 0 =
      (F.toBytes (w (sCell (N4c.chBase κ σ + i * N4c.sBlk - 2) j)))[r] := by
  obtain ⟨h1, h2, h3⟩ := N4c.strideB_eq
  have hL := (N4c.aggB_blocks (k := k) (by omega)).2.1
  have hik : i * N4c.sBlk + N4c.sBlk ≤ N4c.sBlk * k := by
    rw [Nat.mul_comm N4c.sBlk k, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  have hs : N4c.sBlk ≤ i * N4c.sBlk := Nat.le_mul_of_pos_left _ hi1
  have hsb : 2 ≤ N4c.sBlk := by rw [h2]; decide
  have hm : i * N4c.strideB = 64 * (i * N4c.sBlk) := by rw [h1]; ring
  have hcl : 0 < N4c.cLen := by decide
  rw [hm]
  generalize i * N4c.sBlk = m at *
  generalize N4c.sBlk * k = K at *
  rw [show 64 * m - 128 + 16 * j + r = 16 * (4 * (m - 2) + j) + r by omega,
    agg_elem w hA (by omega) hr (by omega), sCell_add, Nat.add_sub_assoc (by omega)]

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
  have := wfData_lt80 1 (itemsOf seq4) h80 p (List.mem_of_mem_tail hp)
  have := slenL_seq4
  omega

/-- `wfSeg` is the first elements of the items after the seed, from offset 160. -/
theorem wfSeg_eq {rest : List Item} (hr : itemsOf seq4 = .seed :: rest) : wfSeg = wfData 160 rest := by
  rw [wfSeg, hr, wfData, List.tail_cons, show 1 + Item.seed.slen = 160 from rfl]

/-- **Shifting the items by `16 d` bytes shifts their pinned elements by `d`** (the values depend on
the offset modulo 16 only). -/
theorem wfData_shift (d : ℕ) : ∀ (o : ℕ) (its : List Item),
    wfData (o + 16 * d) its = (wfData o its).map fun p => (p.1 + d, p.2)
  | _, [] => rfl
  | o, it :: its => by
    have ih := wfData_shift d (o + it.slen) its
    have h1 : (o + 16 * d) / 16 = o / 16 + d := by omega
    have h2 : winF (o + 16 * d) it = winF o it := by
      simp only [winF, winB, show (o + 16 * d) % 16 = o % 16 by omega]
    simp only [wfData, List.map_cons, h1, h2, show o + 16 * d + it.slen = o + it.slen + 16 * d by omega, ih]

/-! ## The head rows' readings (R-A′) -/

theorem toBytes_add_hi {a b : F} {r : ℕ} (hr : r < 16)
    (hb : ∀ i (hi : i < 8), bitF b ⟨8 * r + i, by omega⟩ = false) :
    (F.toBytes (a + b))[r] = (F.toBytes a)[r] := by
  refine UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi => ?_)
  rw [toBytes_bit _ _ _ hr hi, toBytes_bit _ _ _ hr hi, bitF_add, hb i hi, Bool.xor_false]

theorem packAt_ev_succ (w : Asg) (cell : ℕ → ℕ) (d n : ℕ) :
    (packAt cell d (n + 1)).ev w =
      (packAt cell d n).ev w + bitBasis ⟨(d + n) % 128, Nat.mod_lt _ (by norm_num)⟩ * w (cell n) := by
  simp [packAt, List.range_succ, Lin.ev]

/-- **Packed Boolean cells at bits `d … d + n − 1`** leave every other bit clear. -/
theorem bitF_packAt_out (w : Asg) (cell : ℕ → ℕ) {d n : ℕ} (hn : d + n ≤ 128)
    (hb : ∀ q < n, w (cell q) = 0 ∨ w (cell q) = 1) (j : Fin 128) (hj : j.val < d ∨ d + n ≤ j.val) :
    bitF ((packAt cell d n).ev w) j = false := by
  induction n with
  | zero => simpa [packAt] using bitF_zero j
  | succ n ih =>
    rw [packAt_ev_succ, bitF_add, ih (by omega) (fun q hq => hb q (by omega)) (by omega)]
    rcases hb n (by omega) with h | h
    · rw [h, mul_zero, bitF_zero]; rfl
    · rw [h, mul_one, bitF_bitBasis, Bool.false_xor, decide_eq_false_iff_not, Fin.ext_iff]
      simp only [Fin.val_mk]
      rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem boolRow_val {w : Asg} {one c : ℕ} (hone : w one = 1) (h : (boolRow one c).Holds w) :
    w c = 0 ∨ w c = 1 := by
  simp only [Row.Holds, boolRow, Lin.ev_cell, Lin.ev_sub, Lin.ev_nil, hone, mul_eq_zero] at h
  rcases h with h | h
  · exact .inl h
  · exact .inr (sub_eq_zero.mp h).symm

theorem decRow_val {w : Asg} {one x : ℕ} {c : F} {bits : Lin} (hone : w one = 1)
    (h : (decRow one x c bits).Holds w) : w x = c + bits.ev w := by
  simp only [Row.Holds, decRow, Lin.ev_cell, Lin.ev_sub, Lin.ev_smul, Lin.ev_nil, hone, one_mul,
    mul_one] at h
  linear_combination h

theorem seedW_word {t : ℕ} (ht : t < 8) : (F.toBytes seedW)[1 + t]'(by omega) = (enc64 119).getD t 0 :=
  winF_word 1 .seed (by norm_num) ht

theorem seedW_tag : (F.toBytes seedW)[0] = tagTrace := by
  rw [seedW, winF, winFB, F.toBytes_ofBytes]; rfl

theorem seedM_seedW (r : ℕ) (hr : r < 16) (h1 : 1 ≤ r) : (F.toBytes seedM)[r] = (F.toBytes seedW)[r] := by
  rw [seedM, seedW, winF, winFB, winFB, F.toBytes_ofBytes, F.toBytes_ofBytes, Vector.getElem_ofFn,
    Vector.getElem_ofFn]
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rfl

theorem spBytes_eq : spBytes = enc64 89 ++ spacerQ.data.toList := by
  rw [spacerQ_bytes, spBytes, List.append_assoc]

theorem spPin_byte {j r : ℕ} (hj : j < 6) (hr : r < 16) :
    (F.toBytes (spPin j))[r] = spBytes.getD (16 * j + r) 0 := by
  rw [spPin, winFB, F.toBytes_ofBytes, Vector.getElem_ofFn]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hr]

/-- **What a segment's head rows give** (R-A′), at `one = 1`: bytes 1–15 of its element 0 are the
seed's (`enc64 119 ‖ "FRSEED0"`); for `s = 0` its byte 0 is the tag `0x54`; for `s ≥ 1` the spacer's
elements 0–5 are its constants and byte 0 of its element 6 (its query's last byte) is zero. -/
structure HeadOk (w : Asg) (b0 s : ℕ) : Prop where
  e0 : ∀ r (hr : r < 16), 1 ≤ r → (F.toBytes (w (sCell b0 0)))[r] = (F.toBytes seedW)[r]
  tag : s = 0 → (F.toBytes (w (sCell b0 0)))[0] = tagTrace
  sp : s ≠ 0 → (∀ j < 6, w (sCell (b0 - 2) j) = spPin j) ∧ (F.toBytes (w (sCell (b0 - 2) 6)))[0] = 0

theorem headOk_of {w : Asg} {one b0 s : ℕ} {cell : ℕ → ℕ} (hone : w one = 1)
    (h : ∀ r ∈ headRows one b0 s cell, r.Holds w) : HeadOk w b0 s := by
  unfold headRows at h
  by_cases hs : s = 0
  · rw [if_pos hs] at h
    have h0 := pinRow_holds hone (h _ (List.mem_singleton_self _))
    exact ⟨fun r _ _ => by rw [h0], fun _ => by rw [h0, seedW_tag], fun h' => absurd hs h'⟩
  · rw [if_neg hs] at h
    have hb : ∀ q < 128, w (cell q) = 0 ∨ w (cell q) = 1 := fun q hq =>
      boolRow_val hone (h _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩))))
    have h6 := decRow_val hone (h _ (List.mem_append_right _ (List.mem_cons_self ..)))
    have h8 := decRow_val hone (h _ (List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))
    refine ⟨fun r hr h1 => ?_, fun h' => absurd h' hs, fun _ => ⟨fun j hj => ?_, ?_⟩⟩
    · rw [h8, toBytes_add_hi hr (fun i hi => bitF_packAt_out w _ (by norm_num)
        (fun q hq => hb _ (by omega)) _ (by simp only; omega)), seedM_seedW r hr h1]
    · exact pinRow_holds hone (h _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))))
    · rw [h6, toBytes_add_hi (by norm_num) (fun i hi => bitF_packAt_out w _ (by norm_num)
        (fun q hq => hb _ (by omega)) _ (by simp only; omega))]
      rfl

/-! ## The pins give the segments' and the spacers' constant bytes -/

/-- **A segment's length words from its pins and head facts**: if stream byte `64 d + 16 e + r` is
byte `r` of the cell `sCell b0 e` (`16 e + 80 ≤ segB`), the segment read at `1 + 64 d` has every
item's length word in place. -/
theorem wfSeg_of_pins {B : List UInt8} {w : Asg} {b0 d s : ℕ}
    (hB : ∀ e r (hr : r < 16), 16 * e + 80 ≤ N4c.segB →
      B.getD (64 * d + 16 * e + r) 0 = (F.toBytes (w (sCell b0 e)))[r])
    (hlen : 64 * d + N4c.segB ≤ B.length)
    (hpin : ∀ p ∈ wfSeg, w (sCell b0 p.1) = p.2) (hh : HeadOk w b0 s) :
    WfAt B (1 + 64 * d) (itemsOf seq4) := by
  obtain ⟨rest, hrs, hal⟩ := itemsOf_seq4_al
  have h159 : Item.seed.slen = 159 := rfl
  have hsl : 1 + (159 + slenL rest) = N4c.segB := by
    rw [← slenL_seq4, hrs]; simp [slenL, h159]
  rw [hrs]
  refine ⟨?_, ?_⟩
  · refine List.ext_getElem (by simp [enc64]; omega) fun t h₁ h₂ => ?_
    have ht : t < 8 := by simpa [enc64] using h₂
    have := hB 0 (1 + t) (by omega) (by decide)
    rw [Nat.mul_zero, Nat.add_zero, hh.e0 _ (by omega) (by omega), seedW_word ht] at this
    rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0,
      show 1 + 64 * d + t = 64 * d + (1 + t) by omega, this, List.getD_eq_getElem _ 0 (by simp [enc64]; omega)]
    rfl
  · rw [h159]
    refine wfAt_of_pins B rest _ (alAt_of _ rest (by omega) fun it h => (hal it h).1) (by omega)
      fun p hp r hr => ?_
    rw [show 1 + 64 * d + 159 = 160 + 16 * (4 * d) by omega, wfData_shift, ← wfSeg_eq hrs] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    dsimp only
    rw [show 16 * (q.1 + 4 * d) + r = 64 * d + 16 * q.1 + r by ring, hB _ _ hr (wfSeg_lt80 q hq),
      hpin q hq]

/-- **A spacer's constant bytes from its pins** (R-A′): if stream byte `o + 16 j + r` is byte `r` of
the cell `sCell bb j` (`j < 7`), the pins of elements 0–5 and element 6's zero byte 0 give
`enc64 89 ‖ spacerQ` at `o`. -/
theorem spAt_of_pins {B : List UInt8} {w : Asg} {bb o : ℕ}
    (hB : ∀ j r, j < 7 → ∀ hr : r < 16, B.getD (o + 16 * j + r) 0 = (F.toBytes (w (sCell bb j)))[r])
    (hlen : o + 97 ≤ B.length) (hp : ∀ j < 6, w (sCell bb j) = spPin j)
    (h6 : (F.toBytes (w (sCell bb 6)))[0] = 0) : SpAt B o := by
  unfold SpAt
  rw [← spBytes_eq]
  have hl : spBytes.length = 97 := by simp [spBytes, enc64, tagAbs]
  refine List.ext_getElem (by simp; omega) fun t h₁ h₂ => ?_
  rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
  rw [hl] at h₂
  by_cases ht : t < 96
  · have := hB (t / 16) (t % 16) (by omega) (Nat.mod_lt _ (by norm_num))
    rw [hp _ (by omega), spPin_byte (by omega) (Nat.mod_lt _ (by norm_num))] at this
    rw [show o + t = o + 16 * (t / 16) + t % 16 by omega, this]
    congr 1; omega
  · have := hB 6 0 (by norm_num) (by norm_num)
    rw [h6] at this
    rw [show t = 96 by omega, show o + 96 = o + 16 * 6 + 0 by rfl, this]
    rfl

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

/-- **Byte 0 of a slot's proof read off segment `i`** is the segment's stream byte 80 (its
element 5's byte 0). -/
theorem kind_byte (pf : Trace → Proof) (hpf : PfHdr pf) {κ : NodeKind} {σ k i : ℕ} {w : Asg} {c : UInt8}
    (h5 : (N4c.chainBytes4 κ σ k w).getD (i * N4c.strideB + 16 * 5 + 0) 0 = c) :
    byteAt (pf (segTr κ σ k i w)) 0 = c := by
  obtain ⟨rest, hr, -⟩ := itemsOf_seq4_al
  rw [segTr, hr, Read.readItems, hpf, byteAt_mk]
  show (((N4c.chainBytes4 κ σ k w).drop (1 + i * N4c.strideB + 8)).take Item.seed.qlen).getD 71 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by decide), List.getElem?_drop,
    ← List.getD_eq_getElem?_getD, ← h5]
  congr 1; omega

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

/-- **`Gap4` without what the M rows give** (S-E13a; revision 4.4.1, R-A′): the slots' imports
`imp` and `V_A`'s checks `aggChk`. The kind bytes and the streams' constant bytes (`kindN`, `kindS`,
`wf`) are given by the pack rows at every slot (`gap4_of_rows`); `wots` and `aggPad` by S-E13b's
rows (`wots_aggPad_of_rows`). -/
structure Gap4R (impl₀ : OpImpl) (base : NodeKind → OpImpl) (pf : Trace → Proof) (κ : NodeKind)
    (vk c₁ c₂ : Digest) (w : Asg) : Prop where
  imp : ∀ v, N4c.Active4 (rd4 pf) κ w v →
    SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)
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
    rw [extRowsC, if_pos rfl, if_pos h, xRowsK_eq]; exact List.mem_append_left _ hr
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

/-- The pins, the kind tie and the head facts of a slot whose segment base is `b0`. -/
theorem pins_of {v b0 : ℕ} {G : Grp} (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hv : v < κ.vslots) (hb : packB κ v = some (b0, G)) :
    (∀ p ∈ wfSeg, w (sCell b0 p.1) = p.2) ∧
      (kindRow κ.oneCell (sCell b0 5) (fun ι => κ.oneCell + selR v ι) G).Holds w ∧
      HeadOk w b0 (segIx κ v) := by
  have hone := one_of_pubCells hS.2.2.2.2
  have h := packRows_hold hS hv
  refine ⟨fun p hp => pinRow_holds hone (h _ ?_), h _ ?_,
    headOk_of (cell := spC κ (N4c.aggChild κ (aggSlot κ v)) (segIx κ v)) hone fun r hr => h r ?_⟩
  · simp only [packRows4, packWf4, hb, List.mem_append]
    exact Or.inr (List.mem_map.2 ⟨p, hp, rfl⟩)
  · simp [packRows4, packHead4, hb]
  · simp only [packRows4, packHead4, hb, List.mem_append, List.mem_cons]
    exact Or.inl (Or.inr hr)

theorem packB_prev (hp : κ.hasPrev = true) : packB κ 0 = some (N4c.chBase κ 0, nodeGrp) := by
  simp [packB, isPrevSlot, hp]

theorem packB_sub {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) :
    packB κ (N4c.sub κ a i) = some (N4c.chBase κ (N4c.aggChild κ a) + i * N4c.sBlk, segGrp) := by
  obtain ⟨-, hx, hp, -⟩ := sub_facts κ ha hi
  have hs : aggSlot κ (N4c.sub κ a i) = a := slotA_sub κ ha hi
  simp only [packB, hp, hx, hs, Bool.false_eq_true, if_false]

theorem segIx_sub {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) : segIx κ (N4c.sub κ a i) = i := by
  obtain ⟨-, hx, hp, -⟩ := sub_facts κ ha hi
  simp only [segIx, hp, hx, Bool.false_eq_true, if_false]

theorem segIx_prev (hp : κ.hasPrev = true) : segIx κ 0 = 0 := by simp [segIx, isPrevSlot, hp]

theorem maxK_pos (κ : NodeKind) : 0 < κ.maxK := by cases κ <;> decide

/-- **Signed child `σ`'s stream from the pack rows** (R-A′): its tag, every segment's length words
and every spacer's constant bytes. -/
theorem wf_of_rows (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) {σ : ℕ} (hσ : σ < 2) :
    (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w).head? = some tagTrace ∧
      ∀ i < nSeg κ σ w, WfAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (1 + i * N4c.strideB)
        (itemsOf seq4) ∧
      (0 < i → SpAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (i * N4c.strideB - 128)) := by
  have hone := one_of_pubCells hS.2.2.2.2
  have hF := protoFit_of hone hS.2.2.2.1
  have hst := N4c.strideB_eq
  have hlen : ∀ k, (N4c.chainBytes4 κ σ k w).length = N4c.streamB κ σ k := fun k =>
    Stream.streamBytes_length _ _
  by_cases hA : N4c.isAgg κ σ = true
  · obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
    have hlk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ (N4c.aggOf κ σ) i), r.Holds w :=
      fun i hi => linkRows_hold hF (sub_facts κ ha hi).1 hS.2.2.2.1
    have hk1 : 1 ≤ kAct κ (N4c.aggOf κ σ) w := (actK_kAct hone ha hS.2.2.1 hlk).1
    have hkm := kAct_le κ (N4c.aggOf κ σ) w
    have hk : N4c.kOf (rd4 pf) κ w σ = kAct κ (N4c.aggOf κ σ) w := by
      rw [N4c.kOf, if_pos hA, kA_rd4 pf κ ha]
    have hn : nSeg κ σ w = kAct κ (N4c.aggOf κ σ) w := by rw [nSeg, if_pos hA]
    rw [hk, hn]
    set k := kAct κ (N4c.aggOf κ σ) w
    have hB : (N4c.chainBytes4 κ σ k w).length = N4c.aggB k := by rw [hlen, N4c.streamB, if_pos hA]
    have hBk := N4c.aggB_blocks hk1
    -- sub-slot `i`'s pins
    have hpin : ∀ i < k, (∀ p ∈ wfSeg, w (sCell (N4c.chBase κ σ + i * N4c.sBlk) p.1) = p.2) ∧
        HeadOk w (N4c.chBase κ σ + i * N4c.sBlk) i := fun i hi => by
      have hi' : i < κ.maxK := by omega
      have h := pins_of hS (sub_facts κ ha (i := i) hi').1 (packB_sub (i := i) ha hi')
      simp only [hc, segIx_sub ha hi'] at h
      exact ⟨h.1, h.2.2⟩
    have hseg : ∀ i < k, WfAt (N4c.chainBytes4 κ σ k w) (1 + i * N4c.strideB) (itemsOf seq4) := fun i hi => by
      obtain ⟨hp, hh⟩ := hpin i hi
      have h64 : i * N4c.strideB = 64 * (i * N4c.sBlk) := by rw [hst.1]; ring
      rw [h64]
      refine wfSeg_of_pins (fun e r hr he => ?_) ?_ hp hh
      · rw [← h64]; exact segi_elem w hA hi hr he
      · have : (i + 1) * N4c.strideB ≤ k * N4c.strideB := Nat.mul_le_mul_right _ (by omega)
        rw [hB, ← h64, hBk.2.2, Nat.add_one_mul] at *
        have : N4c.segB + 128 = N4c.strideB := by simp [N4c.strideB, N4c.spacerB, N4c.segB]
        omega
    refine ⟨?_, fun i hi => ⟨hseg i hi, fun hi0 => ?_⟩⟩
    · -- the tag
      have h0 := (hpin 0 (by omega)).2.tag rfl
      have he := segi_elem w hA (k := k) (i := 0) (by omega) (e := 0) (r := 0) (by norm_num) (by decide)
      simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_zero] at he h0
      have h0lt : 0 < N4c.aggB k := by
        have := Nat.le_mul_of_pos_right N4c.sBlk hk1
        rw [hBk.1, hBk.2.1]; simp only [N4c.sBlk] at *; omega
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [hB]; exact h0lt), ← List.getD_eq_getElem _ 0,
        he, h0]
    · -- spacer `i`
      obtain ⟨hpj, h6⟩ := (hpin i hi).2.sp (by omega)
      refine spAt_of_pins (bb := N4c.chBase κ σ + i * N4c.sBlk - 2) (fun j r hj hr => spc_elem w hA hi0 hi
        (by omega) hr) ?_ hpj h6
      have : (i + 1) * N4c.strideB ≤ k * N4c.strideB := Nat.mul_le_mul_right _ (by omega)
      have : 128 ≤ i * N4c.strideB := le_trans (by rw [hst.1, hst.2.1]; decide)
        (Nat.le_mul_of_pos_left _ hi0)
      rw [hB, hBk.2.2, Nat.add_one_mul] at *
      omega
  · have hp : κ.hasPrev = true ∧ σ = 0 := by
      cases κ <;> simp_all [N4c.isAgg, NodeKind.hasPrev]
    obtain ⟨hp, rfl⟩ := hp
    have hk : N4c.kOf (rd4 pf) κ w 0 = 0 := by rw [N4c.kOf, if_neg hA]
    have hn : nSeg κ 0 w = 1 := by rw [nSeg, if_neg hA]
    rw [hk, hn]
    have hk0 : N4c.isAgg κ 0 = true → 1 ≤ 0 := fun h => absurd h hA
    have h := pins_of hS (vslots_pos κ) (packB_prev hp)
    rw [segIx_prev hp] at h
    obtain ⟨hpin, -, hh⟩ := h
    have hB : (N4c.chainBytes4 κ 0 0 w).length = N4c.segB := by rw [hlen, N4c.streamB, if_neg hA]
    refine ⟨?_, fun i hi => ?_⟩
    · have he := seg0_elem w hk0 (e := 0) (r := 0) (by norm_num) (by decide)
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [hB]; decide), ← List.getD_eq_getElem _ 0]
      simpa [hh.tag rfl] using he
    · obtain rfl : i = 0 := by omega
      refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
      have := wfSeg_of_pins (d := 0) (fun e r hr he => by simpa using seg0_elem w hk0 hr he)
        (by rw [hB]; omega) hpin hh
      simpa using this

/-- **`Gap4.kindS` from the pack rows** (every sub-slot; R-A′): an active sub-slot's proof has the
selected segment kind's byte. -/
theorem kindS_of_rows (hpf : PfHdr pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ a < N4c.nAgg κ, ∀ i < kAct κ a w, ∀ ι, SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP 1) ι →
      byteAt ((rd4 pf).slotπ κ (N4c.sub κ a i) w) 0 = (segAt ι).byte := by
  have hone := one_of_pubCells hS.2.2.2.2
  intro a ha i hi ι hι
  have hkm := kAct_le κ a w
  have hi' : i < κ.maxK := by omega
  obtain ⟨-, hx, hpv, -⟩ := sub_facts κ ha hi'
  obtain ⟨-, hrow, -⟩ := pins_of hS (sub_facts κ ha (i := i) hi').1 (packB_sub (i := i) ha hi')
  have h5 := kindRow_sel hone hrow (by rw [protoOf_seg hpv]; exact hι)
  show byteAt (⟨(slotPf pf κ (N4c.sub κ a i) w).toArray⟩ : Proof) 0 = _
  rw [byteAt_slotPf]
  simp only [slotTr4, hpv, Bool.false_eq_true, if_false, slotA_sub κ ha (by omega : i < κ.maxK), hx]
  rw [kind_byte pf hpf (segi_elem w (N4c.isAgg_aggChild κ a) hi (by norm_num) (by decide)), h5]
  exact (kConst_byte ι).2

/-- **`gap4_of_rows`**: the node's truths, `PfHdr pf` and `Gap4R` give S-N2's `Gap4`. -/
theorem gap4_of_rows (hpf : PfHdr pf) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hG : Gap4R impl₀ base pf κ vk c₁ c₂ w) : Gap4 impl₀ base pf κ vk c₁ c₂ w := by
  have hone := one_of_pubCells hS.2.2.2.2
  have hF := protoFit_of hone hS.2.2.2.1
  have hL := hS.2.2.1
  have hlk : ∀ a < N4c.nAgg κ, ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w :=
    fun a ha i hi => linkRows_hold hF (sub_facts κ ha hi).1 hS.2.2.2.1
  obtain ⟨hwots, hpad⟩ := wots_aggPad_of_rows pf hS
  refine ⟨hG.imp, ?_, ?_, fun σ hσ => wf_of_rows pf hS hσ, hG.aggChk, hpad, hwots⟩
  · -- kindN
    intro hp ι hι
    obtain ⟨-, hrow, -⟩ := pins_of hS (vslots_pos κ) (packB_prev hp)
    have h5 := kindRow_sel hone hrow (by rw [protoOf_zero hp]; exact hι)
    have hk0 : N4c.isAgg κ 0 = true → 1 ≤ 0 := fun h => by simp [isAgg_zero hp] at h
    show byteAt (sgn4 pf κ 0 w).π 0 = _
    rw [sgn4, if_neg (by simp [isAgg_zero hp]), byteAt_slotPf]
    simp only [slotTr4, isPrevSlot, hp, Bool.true_and, beq_self_eq_true, if_true]
    rw [kind_byte pf hpf (i := 0) (by simpa using seg0_elem w hk0 (e := 5) (r := 0) (by norm_num) (by decide)),
      h5]
    exact (kConst_byte ι).1
  · -- kindS, every sub-slot
    exact kindS_of_rows pf hpf hS

/-- (Converse) `Gap4` gives `Gap4R`: nothing beyond `Gap4` is asked. -/
theorem gap4R_of_gap4 (hG : Gap4 impl₀ base pf κ vk c₁ c₂ w) : Gap4R impl₀ base pf κ vk c₁ c₂ w :=
  ⟨hG.imp, hG.aggChk⟩

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

/-- (+/−) **`SpAt`** (R-A′): the spacer's encoding `enc64 89 ‖ spacerQ ‖ a` meets it (any answer
`a`); 129 zero bytes do not, nor does the spacer with its last query byte set. -/
theorem spAt_ctl : SpAt (enc64 89 ++ spacerQ.data.toList ++ List.replicate 32 7) 0 ∧
    ¬ SpAt (List.replicate 129 0) 0 ∧
    ¬ SpAt (enc64 89 ++ (spacerQ.data.toList.take 88 ++ [1]) ++ List.replicate 32 7) 0 := by
  unfold SpAt; decide

/-- (+) **The masked element 0** (R-A′): an element whose bytes 1–15 are the seed's and whose byte
0 is any `b` is `seedM` plus `b`'s bits at positions 0–7: the decomposition row holds with the bits
of `b = 1`. (−) An element differing from `seedM` in bit 8 (byte 1) fails the row for every Boolean
choice of the 8 bit cells. -/
theorem decRow_ctl :
    (decRow 0 1 seedM (packAt (fun q => 2 + q) 0 8)).Holds
      (fun c => if c = 0 then 1 else if c = 1 then seedM + bitBasis 0 else if c = 2 then 1 else 0) ∧
    ∀ w : Asg, w 0 = 1 → w 1 = seedM + bitBasis 8 → (∀ q < 8, w (2 + q) = 0 ∨ w (2 + q) = 1) →
      ¬ (decRow 0 1 seedM (packAt (fun q => 2 + q) 0 8)).Holds w := by
  refine ⟨?_, fun w h0 h1 hb h => ?_⟩
  · simp only [Row.Holds, decRow, Lin.ev_cell, Lin.ev_sub, Lin.ev_smul, Lin.ev_nil]
    simp [packAt, Lin.ev, List.range_succ]
  · have hv := decRow_val h0 h
    rw [h1] at hv
    have := congrArg (fun x => bitF x ⟨8, by norm_num⟩) hv
    simp only [bitF_add] at this
    rw [bitF_packAt_out w _ (by norm_num) (fun q hq => hb q hq) _ (by simp)] at this
    rw [bitF_bitBasis] at this
    simp at this

/-- (+/−) **Every slot is packed** (R-A′): `N8`'s slot 5 (aggregate 1's sub-slot 1) reads its segment
at the aggregate's first block plus `sBlk`, `N4`'s slot 2 (sub-slot 1) at its aggregate's plus
`sBlk`, not at sub-slot 0's. -/
theorem packB_ctl : (packB .N8 5).map Prod.fst = some (N4c.chBase .N8 1 + N4c.sBlk) ∧
    (packB .N4 2).map Prod.fst = some (N4c.chBase .N4 1 + N4c.sBlk) ∧
    (packB .N4 2).map Prod.fst ≠ (packB .N4 1).map Prod.fst := by
  refine ⟨rfl, rfl, by decide⟩

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
