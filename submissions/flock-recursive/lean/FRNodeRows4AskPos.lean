-- New for `flock-recursive` (PACK-4.4.1 §4.2–§5.2; IMP-RESULT §5.2; track ASK-P): the reader's
-- positional spec and the element alignment of every item, at revision 4.4.1's format.
import FRNodeRows4AskPosF

/-!
# Where each trace entry sits: the reader's positional spec and the element alignment

A slot's trace (`slotTr4`, the reader `rd4`) is `seq4`'s items read off its signed child's stream
(`chainBytes4`) from the slot's segment start `1 + i·strideB` (`segIx`, R-A′'s spacers). Here:

* **`slotTr4_getElem?`** (the reader's positional spec): entry `k` is item `k` read at the stream
  offset `1 + i·strideB + itOff k`, `itOff k` the prefix sum of the items' stream lengths
  (`readItems_getElem?` for any item list).
* **`entryAt_qbyte`**, **`entryAt_abyte`**: an entry's query byte `j` and answer byte `j` are stream
  bytes `o + 8 + j` and `o + 8 + qlen + j`.
* **`slot_byte`** (the H bridge at an active slot): stream byte `i·strideB + x` of the slot's segment
  is byte `x mod 16` of the H cell `sCell (slotB0 κ v) (x / 16)` (outside the segment's last block).
* **The alignment** (`itOff_al`, `ans_al`, `itOff_le`): item `k ≥ 1` starts on an element boundary
  (`1 + itOff k ≡ 0 mod 16`), every answer is two whole elements (`1 + itOff k + 8 + qlen ≡ 0`), and
  items end inside the segment. **`itE k`**/**`ansE k`**: item `k`'s first element and its answer's.
* **`slot_ans`** / **`slot_ansA`**: entry `k`'s answer halves are the H cells (and the arena₁ cells in
  the prototype frame) of elements `ansE k`, `ansE k + 1`; **`slot_qbyte`** / **`slot_qelem`**: its query
  bytes are those cells' bytes, a whole 16-byte query window an element (`F.ofBytes`).

Only the last item's answer lies in the segment's last block (`last_item`), which may be an
aggregate's candidate final block: the statements exclude it by `1 + itOff k + slen + 64 ≤ segB`.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## The reader's positional spec -/

/-- **Entry `k` of `readItems`** is item `k` read at the prefix sum of the items' stream lengths. -/
theorem readItems_getElem? (B : List UInt8) : ∀ (its : List Item) (o k : ℕ),
    (Read.readItems B o its)[k]? = (its[k]?).map (Read.entryAt B (o + ((its.take k).map Item.slen).sum))
  | [], _, _ => rfl
  | it :: its, o, 0 => by simp [Read.readItems]
  | it :: its, o, k + 1 => by
    rw [Read.readItems, List.getElem?_cons_succ, readItems_getElem? B its, List.getElem?_cons_succ,
      List.take_succ_cons, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **Item `k`'s offset in a segment's trace** (bytes after the trace's first byte): the prefix sum of
`seq4`'s items' stream lengths. -/
def itOff (k : ℕ) : ℕ := (((itemsOf seq4).take k).map Item.slen).sum

/-- Item `k` of `seq4` (the seed past the end). -/
def itAt (k : ℕ) : Item := (itemsOf seq4).getD k .seed

/-- Slot `v`'s signed child (whose stream it reads). -/
def slotSg (κ : NodeKind) (v : ℕ) : ℕ := if isPrevSlot κ v then 0 else N4c.aggChild κ (slotA κ v)

/-- Slot `v`'s stream's segment count (the reader's). -/
noncomputable def slotK (κ : NodeKind) (v : ℕ) (w : Asg) : ℕ := if isPrevSlot κ v then 0 else kAct κ (slotA κ v) w

/-- **Slot `v`'s stream** (`chainBytes4` of its signed child). -/
noncomputable def slotStr (κ : NodeKind) (v : ℕ) (w : Asg) : List UInt8 :=
  N4c.chainBytes4 κ (slotSg κ v) (slotK κ v w) w

theorem slotTr4_seg (κ : NodeKind) (v : ℕ) (w : Asg) :
    slotTr4 κ v w = segTr κ (slotSg κ v) (slotK κ v w) (segIx κ v) w := by
  unfold slotTr4 slotSg slotK segIx; split_ifs <;> rfl

/-- **The reader's positional spec**: slot `v`'s entry `k` is item `k` read off the slot's stream at
`1 + i·strideB + itOff k` (`i = segIx κ v`). -/
theorem slotTr4_getElem? (κ : NodeKind) (v : ℕ) (w : Asg) (k : ℕ) :
    (slotTr4 κ v w)[k]? =
      ((itemsOf seq4)[k]?).map (Read.entryAt (slotStr κ v w) (1 + segIx κ v * N4c.strideB + itOff k)) := by
  rw [slotTr4_seg, segTr, readItems_getElem?]; rfl

/-! ## An entry's bytes -/

/-- **An entry's query byte `j`** is stream byte `o + 8 + j` (inside the stream). -/
theorem entryAt_qbyte (B : List UInt8) (o : ℕ) (it : Item) {j : ℕ} (hj : j < it.qlen)
    (hB : o + 8 + it.qlen ≤ B.length) : byteAt (Read.entryAt B o it).1 j = B.getD (o + 8 + j) 0 := by
  have hs : ((B.drop (o + 8)).take it.qlen).length = it.qlen := by simp; omega
  rw [Read.entryAt]
  dsimp only
  rw [byteAt_mk, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]

/-- **An entry's answer byte `j`** is stream byte `o + 8 + qlen + j`. -/
theorem entryAt_abyte (B : List UInt8) (o : ℕ) (it : Item) (j : ℕ) (hj : j < 32) :
    (Read.entryAt B o it).2[j] = B.getD (o + 8 + it.qlen + j) 0 := by
  simp [Read.entryAt]

/-! ## The stream's bytes are H cells (an active slot) -/

/-- **An active slot is the previous node's or an active sub-slot** (the reader's `k`). -/
theorem active_cases {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v) :
    (κ.hasPrev = true ∧ v = 0) ∨ ∃ a < N4c.nAgg κ, ∃ i < kAct κ a w, v = N4c.sub κ a i := by
  rcases hv with h | ⟨a, ha, i, hi, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, ha, i, by rwa [kA_rd4 pf κ ha] at hi, rfl⟩

theorem isAgg_aggChild (κ : NodeKind) (a : ℕ) : N4c.isAgg κ (N4c.aggChild κ a) = true := by
  cases κ <;> simp [N4c.isAgg, N4c.aggChild, NodeKind.hasPrev]

/-- **Stream byte `i·strideB + x` of an active slot's segment** (outside the segment's last block,
`16·⌊x/16⌋ + 80 ≤ segB`) is byte `x mod 16` of the H cell of element `⌊x/16⌋` (`sCell (slotB0 κ v) ·`). -/
theorem slot_byte {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    {x : ℕ} (hx : 16 * (x / 16) + 80 ≤ N4c.segB) :
    (slotStr κ v w).getD (segIx κ v * N4c.strideB + x) 0 =
      (F.toBytes (w (sCell (slotB0 κ v) (x / 16))))[x % 16]'(Nat.mod_lt _ (by norm_num)) := by
  have hx' : x = 16 * (x / 16) + x % 16 := (Nat.div_add_mod x 16).symm
  rcases active_cases hv with ⟨hp, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · have h0 : isPrevSlot κ 0 = true := by simp [isPrevSlot, hp]
    simp only [slotStr, slotSg, slotK, segIx, slotB0, h0, if_true, Nat.zero_mul, Nat.zero_add]
    conv_lhs => rw [hx']
    exact seg0_elem w (fun h => by simp [N4c.isAgg, hp] at h) (Nat.mod_lt _ (by norm_num)) hx
  · have hk := kAct_le κ a w
    obtain ⟨-, hsi, hps, -⟩ := sub_facts κ ha (lt_of_lt_of_le hi hk)
    have hsa := slotA_sub κ ha (lt_of_lt_of_le hi hk)
    have hag : aggSlot κ (N4c.sub κ a i) = slotA κ (N4c.sub κ a i) := by
      unfold aggSlot slotA; rfl
    simp only [slotStr, slotSg, slotK, segIx, slotB0, hps, if_false, Bool.false_eq_true, hsi, hsa, hag]
    rw [show i * N4c.strideB + x = i * N4c.strideB + 16 * (x / 16) + x % 16 by omega]
    exact segi_elem w (isAgg_aggChild κ a) hi (Nat.mod_lt _ (by norm_num)) hx

/-! ## The alignment -/

theorem sum_mod16 : ∀ l : List ℕ, (∀ x ∈ l, x % 16 = 0) → l.sum % 16 = 0
  | [], _ => rfl
  | x :: l, h => by
    rw [List.sum_cons, Nat.add_mod, h x List.mem_cons_self,
      sum_mod16 l fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **Every item after the seed starts on an element boundary** (`1 + itOff k ≡ 0 mod 16`). -/
theorem itOff_al {k : ℕ} (hk : 1 ≤ k) : (1 + itOff k) % 16 = 0 := by
  obtain ⟨rest, hr, hal⟩ := itemsOf_seq4_al
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hs := sum_mod16 ((rest.take j).map Item.slen) fun x hx => by
    obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hx
    exact (hal it (List.mem_of_mem_take hit)).1
  rw [itOff, hr, List.take_succ_cons, List.map_cons, List.sum_cons]
  have : Item.slen .seed = 159 := rfl
  omega

/-- **Every answer is two whole elements**: `1 + itOff k + 8 + qlen ≡ 0 (mod 16)`. -/
theorem ans_al {k : ℕ} (hk : k < (itemsOf seq4).length) : (1 + itOff k + 8 + (itAt k).qlen) % 16 = 0 := by
  obtain ⟨rest, hr, hal⟩ := itemsOf_seq4_al
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp only [itOff, itAt, hr, List.take_zero, List.map_nil, List.sum_nil, List.getD_cons_zero]; rfl
  · have h1 := itOff_al hk1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : j < rest.length := by rw [hr] at hk; simpa using hk
    have hit : itAt (j + 1) = rest[j] := by simp [itAt, hr, List.getD_eq_getElem?_getD, hj]
    have := (hal rest[j] (List.getElem_mem hj)).1
    rw [hit]; unfold Item.slen at this; omega

/-- **Every item ends inside the segment**: `1 + itOff k + slen ≤ segB`. -/
theorem itOff_le {k : ℕ} (hk : k < (itemsOf seq4).length) : 1 + itOff k + (itAt k).slen ≤ N4c.segB := by
  have h := slenL_seq4
  have hk' : itAt k = (itemsOf seq4)[k] := by simp [itAt, List.getD_eq_getElem?_getD, hk]
  have e : itOff k + (itAt k).slen = (((itemsOf seq4).take (k + 1)).map Item.slen).sum := by
    rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append, List.sum_append,
      hk']; simp [itOff]
  have le : (((itemsOf seq4).take (k + 1)).map Item.slen).sum ≤ slenL (itemsOf seq4) := by
    rw [slenL]
    conv_rhs => rw [← List.take_append_drop (k + 1) (itemsOf seq4)]
    rw [List.map_append, List.sum_append]; omega
  omega

/-- **Item `k`'s first element** in its segment (for `k ≥ 1` exactly: `itOff_al`). -/
def itE (k : ℕ) : ℕ := (1 + itOff k) / 16

/-- **Item `k`'s answer's first element** (the answer is elements `ansE k`, `ansE k + 1`: `ans_al`). -/
def ansE (k : ℕ) : ℕ := (1 + itOff k + 8 + (itAt k).qlen) / 16

/-! ## The composites: an entry's answer and query at an active slot -/

theorem itAt_eq {k : ℕ} (hk : k < (itemsOf seq4).length) : (itemsOf seq4)[k]? = some (itAt k) := by
  simp [itAt, List.getD_eq_getElem?_getD, hk]

theorem slotStr_len {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v) :
    segIx κ v * N4c.strideB + N4c.segB ≤ (slotStr κ v w).length := by
  have hL : ∀ σ k, (N4c.chainBytes4 κ σ k w).length = N4c.streamB κ σ k := fun σ k => by
    simp [N4c.chainBytes4, Stream.streamBytes]
  obtain ⟨h1, h2, h3⟩ := N4c.strideB_eq
  rcases active_cases hv with ⟨hp, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · have h0 : isPrevSlot κ 0 = true := by simp [isPrevSlot, hp]
    simp only [slotStr, slotSg, slotK, segIx, h0, if_true, Nat.zero_mul, Nat.zero_add, hL]
    exact (stream_ge (fun h => by simp [N4c.isAgg, hp] at h)).1
  · have hk := kAct_le κ a w
    obtain ⟨-, hsi, hps, -⟩ := sub_facts κ ha (lt_of_lt_of_le hi hk)
    have hsa := slotA_sub κ ha (lt_of_lt_of_le hi hk)
    simp only [slotStr, slotSg, slotK, segIx, hps, if_false, Bool.false_eq_true, hsi, hsa, hL, N4c.streamB,
      isAgg_aggChild, if_true]
    obtain ⟨-, -, h6⟩ := N4c.aggB_blocks (k := kAct κ a w) (by omega)
    have : i * N4c.strideB + N4c.strideB ≤ kAct κ a w * N4c.strideB := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    omega

/-- **Entry `k`'s answer at an active slot** (not the last block's item): its halves are the H cells of
elements `ansE k`, `ansE k + 1` of the slot's segment. -/
theorem slot_ans {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    (hb : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB) :
    dlo e.2 = w (sCell (slotB0 κ v) (ansE k)) ∧ dhi e.2 = w (sCell (slotB0 κ v) (ansE k + 1)) := by
  rw [slotTr4_getElem?, itAt_eq hk, Option.map_some, Option.some.injEq] at he
  subst he
  have hal := ans_al hk
  have hsl : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl
  have key : ∀ (h : ℕ) (r : Fin 16) (_hh : h < 2),
      (Read.entryAt (slotStr κ v w) (1 + segIx κ v * N4c.strideB + itOff k) (itAt k)).2[16 * h + r.1]'(by omega) =
        (F.toBytes (w (sCell (slotB0 κ v) (ansE k + h))))[r.1] := fun h r hh => by
    rw [entryAt_abyte _ _ _ (16 * h + r.1) (by omega)]
    rw [show 1 + segIx κ v * N4c.strideB + itOff k + 8 + (itAt k).qlen + (16 * h + r.1) =
        segIx κ v * N4c.strideB + (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) by omega,
      slot_byte hv (by have := r.2; unfold ansE at *; omega)]
    have e1 : (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) / 16 = ansE k + h := by unfold ansE; omega
    have e2 : (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) % 16 = r.1 := by omega
    simp only [e1, e2]
  constructor
  · rw [dlo, ← F.ofBytes_toBytes (w (sCell (slotB0 κ v) (ansE k)))]
    refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
    rw [Vector.getElem_ofFn]
    have := key 0 ⟨r, hr⟩ (by norm_num)
    simpa using this
  · rw [dhi, ← F.ofBytes_toBytes (w (sCell (slotB0 κ v) (ansE k + 1)))]
    refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
    rw [Vector.getElem_ofFn]
    exact key 1 ⟨r, hr⟩ (by norm_num)

/-- **Entry `k`'s query byte `j`** at an active slot (not the last block's item): byte `(o + j) mod 16`
of the H cell of element `⌊(o + j)/16⌋`, `o = 1 + itOff k + 8`. -/
theorem slot_qbyte {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    (hb : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB) {j : ℕ} (hj : j < (itAt k).qlen) :
    byteAt e.1 j = (F.toBytes (w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j) / 16))))[(1 + itOff k + 8 + j) % 16]'(
      Nat.mod_lt _ (by norm_num)) := by
  rw [slotTr4_getElem?, itAt_eq hk, Option.map_some, Option.some.injEq] at he
  subst he
  have hsl : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl
  have hL := slotStr_len hv
  rw [entryAt_qbyte _ _ _ hj (by omega),
    show 1 + segIx κ v * N4c.strideB + itOff k + 8 + j = segIx κ v * N4c.strideB + (1 + itOff k + 8 + j) by omega,
    slot_byte hv (by omega)]

/-- **A whole 16-byte query window is an element**: if `1 + itOff k + 8 + j ≡ 0 (mod 16)` and the window
lies in the query, the window's `F` value is the H cell. -/
theorem slot_qelem {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    (hb : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB) {j : ℕ} (hj : j + 16 ≤ (itAt k).qlen)
    (hal : (1 + itOff k + 8 + j) % 16 = 0) :
    F.ofBytes (Vector.ofFn fun r : Fin 16 => byteAt e.1 (j + r)) = w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j) / 16)) := by
  rw [← F.ofBytes_toBytes (w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j) / 16)))]
  refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
  rw [Vector.getElem_ofFn, slot_qbyte hv hk he hb (by omega)]
  have e1 : (1 + itOff k + 8 + (j + r)) / 16 = (1 + itOff k + 8 + j) / 16 := by omega
  have e2 : (1 + itOff k + 8 + (j + r)) % 16 = r := by omega
  simp only [e1, e2]

/-! ## In the prototype frame: the arena₁ cells -/

/-- An item's elements lie in arena₁ (`arN = 4·cLen` elements: the segment's). -/
theorem elem_arN {x : ℕ} (hx : 16 * x + 16 ≤ N4c.segB) : x < arN := by
  have := (arConsts).2.2.2.2.2
  have h3 := N4c.strideB_eq.2.2
  omega

/-- **Entry `k`'s answer in the prototype frame**: its halves are arena₁'s cells
`π·2^20 + arA1 + ansE k (+ 1)` at the slot's assignment (`π = protoOf κ v`). -/
theorem slot_ansA {pf : Trace → Proof} {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v) (hvs : v < κ.vslots)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    (hb : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB) :
    dlo e.2 = slotAsg κ v w (protoOf κ v * slotM4 + arA1 + ansE k) ∧
      dhi e.2 = slotAsg κ v w (protoOf κ v * slotM4 + arA1 + (ansE k + 1)) := by
  obtain ⟨h1, h2⟩ := slot_ans hv hk he hb
  have hal := ans_al hk
  have hsl : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl
  rw [a1_slot hone hE hvs (elem_arN (x := ansE k) (by unfold ansE; omega)),
    a1_slot hone hE hvs (elem_arN (x := ansE k + 1) (by unfold ansE; omega))]
  exact ⟨h1, h2⟩

/-- **A query element in the prototype frame**: arena₁'s cell `π·2^20 + arA1 + ⌊(o + j)/16⌋`. -/
theorem slot_qelemA {pf : Trace → Proof} {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v) (hvs : v < κ.vslots)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    (hb : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB) {j : ℕ} (hj : j + 16 ≤ (itAt k).qlen)
    (hal : (1 + itOff k + 8 + j) % 16 = 0) :
    F.ofBytes (Vector.ofFn fun r : Fin 16 => byteAt e.1 (j + r)) =
      slotAsg κ v w (protoOf κ v * slotM4 + arA1 + (1 + itOff k + 8 + j) / 16) := by
  have hsl : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl
  rw [slot_qelem hv hk he hb hj hal, a1_slot hone hE hvs (elem_arN (by omega))]

/-! ## Controls -/

/-- (+) The reader's spec on a toy stream: entry `1` of two `squeeze` items read from offset `1` is read
at `1 + 80` (one `squeeze` is 80 bytes), (−) not at `1`. -/
theorem readItems_ctl :
    ((Read.readItems (List.replicate 200 7) 1 [.squeeze, .squeeze])[1]?).isSome ∧
      ([Item.squeeze, .squeeze].take 1).map Item.slen = [80] ∧ ([Item.squeeze].map Item.slen).sum ≠ 0 := by
  decide

/-- (+) The seed's answer is element-aligned (`1 + 8 + 119 = 128`); (−) its query is not (`1 + 8 ≢ 0`). -/
theorem seed_al_ctl : (1 + 0 + 8 + Item.qlen .seed) % 16 = 0 ∧ (1 + 0 + 8) % 16 ≠ 0 := by decide

end N4s
end FR
