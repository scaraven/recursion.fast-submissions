/- `LvmXOutSegOff` (GOLF2 off-path move, group 25 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmXLayout, LvmXOut, LvmXOutSeg,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmXLayout
import LvmXOut
import LvmXOutSeg

-- ===== from `LvmXLayout` =====

section
namespace Lvm.X
open RecursionFast Lvm

/-- Every chain message is lane-aligned and inside π. -/
def msgOk (p : Params) (m : ℕ × ℕ) : Bool := m.1 % 8 == 0 && m.2 % 8 == 0 && m.1 + m.2 ≤ piSize p

theorem fsMsgs_ok : ((fsMsgs pX).take (nChain pX)).all (msgOk pX) = true := by decide +kernel

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- `leafLens` is the set of `pX`'s row lengths. -/
theorem leafLens_rows :
    leafLens.all (fun l => ((pX.mainLevels ++ pX.recLevels).map Level.row).contains l) = true ∧
      ((pX.mainLevels ++ pX.recLevels).map Level.row).all (fun l => leafLens.contains l) = true := by
  decide +kernel

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- The trace's lanes: `q₀`'s entry ends at lane 6 (with the tag byte), then the blocks fill the
stream exactly (`T = 238,827`); the reassembled proof is `piSize` bytes (header bytes 0–7 are the
constant `'S' ‖ 0⁷`). -/
theorem blocks_sizes : 6 + ((blocks pX).map Blk.lanes).sum = streamLanes pX ∧
    8 + ((blocks pX).map Blk.pBytes).sum = piSize pX ∧
    (blocks pX).all (fun b => match b with
      | .one _ len => len % 8 == 0 && 32 ≤ len | .opn _ row _ => row % 8 == 0) = true :=
  layout_all_P20.2.2.1

end Lvm.X
end

-- ===== from `LvmXOut` =====

section
namespace Lvm.X
open RecursionFast Lvm

theorem wordsBytes_flatMap {α : Type} (l : List α) (g : α → List Word) :
    wordsBytes (l.flatMap g) = l.flatMap fun x => wordsBytes (g x) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, wordsBytes_append, ih, List.flatMap_cons]

/-- Packing bytes that start with whole words. -/
theorem packBytes_wordsBytes_append (a : List Word) (b : List UInt8) :
    packBytes (wordsBytes a ++ b) = a ++ packBytes b := by
  induction a with
  | nil => rfl
  | cons w a ih =>
    rw [show wordsBytes (w :: a) = wordBytes w ++ wordsBytes a from rfl, List.append_assoc,
      packBytes_append8 _ (wordBytes_length w), ih, ofLE_wordBytes]
    simp [toWord]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **The trace's output words**: the count, `q₀`'s entry, the entries' lanes. -/
def trWords (W : ℕ → Word) : List Word :=
  toWord (qS pX) :: (toWord 7 :: (W 1 >>> 8) :: wsAt W 2 4) ++ entL.flatMap fun x => entW W x.1 x.2

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **The trace's output words** are `trWords`. -/
theorem logWords_readTraceL (W : ℕ → Word) : logWords (readTraceL W) = trWords W := by
  have hal : ∀ x ∈ entL, x.2 % 8 = 0 := by
    have h := List.all_eq_true.mp lensL_facts.2
    intro x hx
    unfold entL at hx
    suffices ∀ (u : ℕ) (l : List ℕ), (∀ y ∈ l, (y % 8 == 0 && 32 ≤ y) = true) → x ∈ walk u l →
        x.2 % 8 = 0 from this 6 lensL h hx
    intro u l
    induction l generalizing u with
    | nil => intro _ h; cases h
    | cons y r ih =>
      intro hy hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have := hy y List.mem_cons_self
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
        exact this.1
      · exact ih _ (fun z hz => hy z (List.mem_cons_of_mem _ hz)) hx
  rw [logWords, length_readTraceL, readTraceL, trWords]
  generalize entL = E at hal ⊢
  rw [List.flatMap_cons, entryWords_q0, List.flatMap_map,
    List.flatMap_congr fun x hx => entryWords_entAt W x.1 x.2 (hal x hx)]
  rfl

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- An entry's contribution in lanes. -/
def pieceW (W : ℕ → Word) (u len : ℕ) : List Word :=
  if len = 64 then sibWs W u
  else if len ∈ leafLens then wsAt W (u + 1) (len / 8)
  else wsAt W (u + 5) ((len - 32) / 8)

/-- **The proof's output words** (without the length word). -/
def pWords (W : ℕ → Word) : List Word := toWord 0x53 :: entL.flatMap fun x => pieceW W x.1 x.2

theorem piece_entAt (W : ℕ → Word) {u len : ℕ} (h8 : len % 8 = 0) (h32 : 32 ≤ len) :
    piece (digW (wsAt W (u - 4) 4)) (entAt W u len) = wordsBytes (pieceW W u len) := by
  have hl : (entAt W u len).1.data.toList.length = len := by
    simp only [entAt, bArr_data, wordsBytes_length, length_wsAt]; (clear * - h8; omega)
  have hq : (entAt W u len).1.data.toList = wordsBytes (wsAt W (u + 1) (len / 8)) := rfl
  unfold piece pieceW
  rw [hl, if_neg (by (clear * - h8 h32; omega))]
  by_cases h64 : len = 64
  · subst h64
    have t1 : (wordsBytes (wsAt W (u + 1) (64 / 8))).take 32 = wordsBytes (wsAt W (u + 1) 4) := by
      rw [show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_take, wsAt_take _ _ _ _ (by norm_num)]
    have t2 : (wordsBytes (wsAt W (u + 1) (64 / 8))).drop 32 = wordsBytes (wsAt W (u + 5) 4) := by
      rw [show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_drop, wsAt_drop]
    rw [if_pos rfl, if_pos rfl, hq, t1, t2, digW_toList (length_wsAt _ _ _)]
    unfold sibWs
    by_cases he : wsAt W (u + 1) 4 = wsAt W (u - 4) 4
    · rw [if_pos (by rw [he]), if_pos he]
    · rw [if_neg (fun h => he (wordsBytes_inj h)), if_neg he]
  · rw [if_neg h64, if_neg h64]
    by_cases hr : len ∈ leafLens
    · rw [if_pos hr, if_pos hr, hq]
    · have t3 : (wordsBytes (wsAt W (u + 1) (len / 8))).drop 32 =
          wordsBytes (wsAt W (u + 5) ((len - 32) / 8)) := by
        rw [show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_drop, wsAt_drop]
        congr 2 <;> (clear * - h8 h32; omega)
      rw [if_neg hr, if_neg hr, hq, t3]

theorem pieces_walk (W : ℕ → Word) : ∀ (l : List ℕ) (u : ℕ), 4 ≤ u →
    (∀ y ∈ l, (y % 8 == 0 && 32 ≤ y) = true) →
    pieces (digW (wsAt W (u - 4) 4)) ((walk u l).map fun x => entAt W x.1 x.2) =
      wordsBytes ((walk u l).flatMap fun x => pieceW W x.1 x.2)
  | [], _, _, _ => rfl
  | len :: r, u, hu, hy => by
    have h0 := hy len List.mem_cons_self
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h0
    simp only [walk, List.map_cons, pieces, List.flatMap_cons, wordsBytes_append]
    rw [piece_entAt W h0.1 h0.2]
    congr 1
    have e : (entAt W u len).2 = digW (wsAt W (u + 5 + len / 8 - 4) 4) := by
      rw [entAt, show u + 5 + len / 8 - 4 = u + 1 + len / 8 by (clear * - hu h0; omega)]
    rw [e]
    exact pieces_walk W r _ (by (clear * - hu h0; omega)) fun y hy' => hy y (List.mem_cons_of_mem _ hy')

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **The proof's bytes** are `pWords`' bytes. -/
theorem reassembleL_data (W : ℕ → Word) :
    (reassembleL (readTraceL W)).data.toList = wordsBytes (pWords W) := by
  have hq0 : piece (Vector.replicate 32 0) (q0Ent W) = [] := by
    unfold piece
    rw [if_pos (by simp [q0Ent, wordBytes_length])]
  have hp := pieces_walk W lensL 6 (by norm_num) (List.all_eq_true.mp lensL_facts.2)
  rw [reassembleL, bArr_data, readTraceL, pieces, hq0, List.nil_append,
    show (q0Ent W).2 = digW (wsAt W (6 - 4) 4) from rfl]
  unfold entL at hp ⊢
  rw [hp, header0_eq]
  rfl

/-- **The proof's packed words** are `pWords`. -/
theorem packBytes_reassembleL (W : ℕ → Word) :
    packBytes (reassembleL (readTraceL W)).data.toList = pWords W := by
  rw [reassembleL_data, packBytes_wordsBytes]

theorem length_pieceW (W : ℕ → Word) (u len : ℕ) : (pieceW W u len).length = pieceLen len := by
  unfold pieceW pieceLen sibWs
  split_ifs <;> simp

theorem sum_walk (f : ℕ → ℕ) : ∀ (u : ℕ) (l : List ℕ),
    ((walk u l).map fun x => f x.2).sum = (l.map f).sum
  | _, [] => rfl
  | u, len :: r => by simp [walk, sum_walk f _ r]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **The reassembled proof has `piSize` bytes.** -/
theorem size_reassembleL (W : ℕ → Word) : (reassembleL (readTraceL W)).size = piSize pX := by
  have : ((entL.map fun x => (pieceW W x.1 x.2).length)).sum = (lensL.map pieceLen).sum := by
    simp only [length_pieceW]
    exact sum_walk pieceLen 6 lensL
  have e : (reassembleL (readTraceL W)).size = 8 + 8 * (lensL.map pieceLen).sum := by
    rw [ByteArray.size, ← Array.length_toList, reassembleL_data, wordsBytes_length, pWords,
      List.length_cons, List.length_flatMap, this]
    generalize (lensL.map pieceLen).sum = n
    (clear * -; omega)
  exact e.trans lensL_pieces

end Lvm.X
end

-- ===== from `LvmXOutSeg` =====

section
section
namespace Lvm.X
open RecursionFast

/-- A list of segments in turn. -/
def catL : List Seg → Seg
  | [] => .nil
  | x :: xs => .cat x (catL xs)

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast

theorem segOut_catL (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ l : List Seg,
    segOut W κ b (catL l) = l.flatMap (segOut W κ b)
  | [] => rfl
  | x :: xs => by rw [catL, segOut, segOut_catL W κ b xs, List.flatMap_cons]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM runPrims

/-- **A segment keeps every register below `200`** but `cTmp`. -/
theorem noW_lo (ap : AP) (sg : Seg) (d : ℕ) {r : ℕ} (hr : r < 200) (hc : r ≠ cTmp) : ¬ Writes (segIR ap d sg) r :=
  fun h => by
    rcases ow_segIR ap sg d r h with h1 | ⟨e, -, h2⟩
    · rcases h1 with h1 | h1
      · exact hc h1
      · (clear * - hr h1; omega)
    · (clear * - hr h2; omega)

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM runPrims

/-- `sibc` takes the right half when the left half is the previous answer, else the left half. -/
theorem segOut_sibc_ctl :
    segOut (fun u => toWord (u % 5)) false 0 (.sibc 4) = [toWord 4, 0, toWord 1, toWord 2] ∧
    segOut (fun u => toWord u) false 0 (.sibc 4) = [toWord 5, toWord 6, toWord 7, toWord 8] := by
  decide

end Lvm.X
end
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem lensL_eq : lensL = (blocks pX).flatMap lensB := rfl

/-- **The trace's segment denotes the trace's words.** -/
theorem segOut_trSegL (W : ℕ → Word) (κ : Bool) : segOut W κ 0 trSegL = trWords W := by
  simp only [trSegL, segOut, segOut_blkTSegs, trWords, entL, lensL_eq, wsAt, Nat.zero_add,
    List.singleton_append, List.cons_append, List.nil_append]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem segOut_blkPSeg (W : ℕ → Word) (κ : Bool) (b u : ℕ) (blk : Blk) (hb : blkOk blk = true) :
    segOut W κ b (blkPSeg u blk) = (walk (b + u) (lensB blk)).flatMap fun x => pieceW W x.1 x.2 := by
  cases blk with
  | one c len =>
    have key : len ≠ 64 ∧ len ∉ leafLens → segOut W κ b (.cp (u + 5) ((len - 32) / 8)) =
        (walk (b + u) [len]).flatMap fun x => pieceW W x.1 x.2 := fun ⟨h1, hr⟩ => by
      simp only [segOut, walk, List.flatMap_cons, List.flatMap_nil, List.append_nil, pieceW,
        if_neg h1, if_neg hr, wsAt]
      all_goals exact List.map_congr_left fun j _ => by congr 1 <;> omega
    cases c <;> simp only [blkOk, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at hb
    · exact absurd hb (by decide)
    · exact key hb
    · exact key hb
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
  | opn t row path =>
    simp only [blkOk, decide_eq_true_eq] at hb
    have hr : row ≠ 64 := ne64_of_leaf hb
    rw [lensB_opn, walk_reps, List.flatMap_assoc]
    simp only [blkPSeg, segOut]
    refine List.flatMap_congr fun j _ => ?_
    rw [walk, walk_rep64, List.flatMap_cons, List.flatMap_map]
    generalize opS row path * j = A
    rw [pieceW, if_neg hr, if_pos (by omega)]
    simp only [wsAt]
    congr 1
    · exact List.map_congr_left fun k _ => by congr 1 <;> (clear * -; omega)
    · refine List.flatMap_congr fun h _ => ?_
      rw [pieceW, if_pos rfl, sibWs]
      simp only [wsAt]
      have e1 : ∀ k, b + A + 13 * h + (u + 5 + row / 8) + 1 + k = b + u + A + 5 + row / 8 + 13 * h + 1 + k :=
        fun k => by (clear * -; omega)
      have e2 : ∀ k, b + A + 13 * h + (u + 5 + row / 8) - 4 + k = b + u + A + 5 + row / 8 + 13 * h - 4 + k :=
        fun k => by (clear * -; omega)
      have e3 : ∀ k, b + A + 13 * h + (u + 5 + row / 8) + 5 + k = b + u + A + 5 + row / 8 + 13 * h + 5 + k :=
        fun k => by (clear * -; omega)
      simp only [e1, e2, e3]
      exact if_congr Iff.rfl rfl rfl

theorem segOut_blkPSegs (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ (u : ℕ) (bs : List Blk),
    bs.all blkOk = true → segOut W κ b (blkPSegs u bs) =
      (walk (b + u) (bs.flatMap lensB)).flatMap fun x => pieceW W x.1 x.2
  | _, [], _ => rfl
  | u, blk :: bs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [blkPSegs, segOut, segOut_blkPSeg W κ b u blk h.1, segOut_blkPSegs W κ b _ bs h.2,
      List.flatMap_cons, walk_append, List.flatMap_append, lanes_eq, Nat.add_assoc]

/-- **The proof's segment denotes the reassembled proof's words.** -/
theorem segOut_pSegL (W : ℕ → Word) (κ : Bool) : segOut W κ 0 pSegL = pWords W := by
  show [toWord 0x53] ++ segOut W κ 0 (blkPSegs 6 (blocks pX)) = _
  rw [segOut_blkPSegs W κ 0 6 _ blocks_ok, Nat.zero_add, pWords, entL, lensL_eq,
    List.singleton_append]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

private theorem lanesOf_flatMap : ∀ bs : List Blk, lanesOf (bs.flatMap lensB) = (bs.map Blk.lanes).sum
  | [] => rfl
  | b :: bs => by
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← lanesOf_flatMap bs, lanes_eq]
    simp only [lanesOf, List.map_append, List.sum_append]

theorem lanes_T : 6 + lanesOf lensL = streamLanes pX := by
  rw [lensL_eq, lanesOf_flatMap]
  exact blocks_sizes.1

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **The trace reads lanes below `T` only.** -/
theorem readTraceL_congr {W W' : ℕ → Word} (h : ∀ v < streamLanes pX, W v = W' v) :
    readTraceL W = readTraceL W' := by
  have hT := lanes_T
  have h6 : ∀ v < 6, W v = W' v := fun v hv => h v (by (clear * - hT hv; omega))
  have hq : q0Ent W = q0Ent W' := by
    have e : wsAt W 2 4 = wsAt W' 2 4 := List.map_congr_left fun j hj => h6 _ (by simp at hj; (clear * - hj; omega))
    simp only [q0Ent, e, h6 1 (by norm_num)]
  unfold readTraceL
  rw [hq]
  refine congrArg _ (List.map_congr_left fun x hx => entAt_congr fun v hv => h v ?_)
  have := walk_lt 6 lensL x hx
  (clear * - hT hv this; omega)

end Lvm.X
end
