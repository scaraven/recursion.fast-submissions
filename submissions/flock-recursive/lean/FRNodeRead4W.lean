-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.5, A.7; stage S-N2): when the reader's traces
-- are the hashed stream. The 3.x analogue is `FRNodeRead.readTrace_of_stream` (the converse).
import FRNodeRead4

/-!
# A well-formed stream is the encoding of the trace the reader reads off it

The reader `rd4` reads signed child `σ`'s trace off its stream `B = chainBytes4 κ σ k w` at fixed
offsets (`segTr`). The query and answer bytes are whatever `B` holds; the stream is the trace's
encoding `0x54 ‖ traceBytes tr` iff its **constant bytes** are right: the tag `0x54` at byte 0 and,
at each item's offset, the 8-byte length word `enc64 |q|` (`WfAt`). **`chainMsg_of_wf`**: on such a
stream, `NodeResid4.chainMsg` holds for the reader. This reduces S-E12a's `chainMsg` to facts at
public positions of H.
-/

namespace FR
namespace N4s
open RecursionFast Rev4

/-- **The length words of `its` from offset `o`** (each item's 8 bytes are `enc64` of its query
length). -/
def WfAt (B : List UInt8) : ℕ → List Item → Prop
  | _, [] => True
  | o, it :: its => (B.drop o).take 8 = enc64 it.qlen ∧ WfAt B (o + it.slen) its

/-- The bytes `its` take. -/
def slenS (its : List Item) : ℕ := (its.map Item.slen).sum

theorem entry_bytes {B : List UInt8} {o : ℕ} {it : Item} (hl : o + it.slen ≤ B.length)
    (hw : (B.drop o).take 8 = enc64 it.qlen) :
    (B.drop o).take it.slen = enc64 (Read.entryAt B o it).1.size ++ (Read.entryAt B o it).1.data.toList ++
      (Read.entryAt B o it).2.toList := by
  have hs : it.slen = 8 + it.qlen + 32 := rfl
  have hq : (Read.entryAt B o it).1.size = it.qlen := by
    show ((B.drop (o + 8)).take it.qlen).toArray.size = _
    rw [List.size_toArray, List.length_take, List.length_drop]; omega
  have h1 : (Read.entryAt B o it).1.data.toList = ((B.drop o).drop 8).take it.qlen := by
    show ((B.drop (o + 8)).take it.qlen).toArray.toList = _
    rw [List.toList_toArray, List.drop_drop]
  have h2 : (Read.entryAt B o it).2.toList = ((B.drop o).drop (8 + it.qlen)).take 32 := by
    simp only [Read.entryAt, Vector.toList_ofFn]
    refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take, List.length_drop]; omega)
      fun i h₁ h₂ => ?_
    simp only [List.length_ofFn] at h₁
    rw [List.getElem_ofFn]
    simp only [Fin.val_mk]
    rw [List.getElem_take, List.getElem_drop, List.getElem_drop, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1; omega
  rw [hq, hs, List.take_add, List.take_add, hw, h1, h2, List.drop_drop]

/-- **On well-formed bytes, the items' span is the encoding of what `readItems` reads.** -/
theorem take_readItems (B : List UInt8) : ∀ (its : List Item) (o : ℕ), WfAt B o its →
    o + slenS its ≤ B.length → (B.drop o).take (slenS its) = traceBytes (Read.readItems B o its)
  | [], _, _, _ => by simp [slenS, Read.readItems, traceBytes]
  | it :: its, o, ⟨hw, hr⟩, hl => by
    have hs : slenS (it :: its) = it.slen + slenS its := by simp [slenS]
    rw [hs] at hl ⊢
    rw [List.take_add, entry_bytes (by omega) hw, List.drop_drop, take_readItems B its _ hr (by omega),
      Read.readItems, Read.traceBytes_cons']

theorem traceBytes_flatten (trs : List Trace) : traceBytes trs.flatten = (trs.map traceBytes).flatten := by
  induction trs with
  | nil => rfl
  | cons t ts ih => simp only [List.flatten_cons, traceBytes, List.flatMap_append, List.map_cons] at ih ⊢; rw [ih]

theorem take_mul_flatten (B : List UInt8) (o S : ℕ) : ∀ n : ℕ,
    (B.drop o).take (n * S) = ((List.range n).map fun i => (B.drop (o + i * S)).take S).flatten
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, List.take_add, take_mul_flatten B o S n, List.range_succ, List.map_append,
      List.flatten_append, List.drop_drop]
    simp

/-- `seq4`'s items take `segB − 1` bytes. -/
theorem slenS_seq4 : slenS (itemsOf seq4) = N4c.segB - 1 := by
  rw [N4c.segB_eq, streamBytesOf, slenS, Nat.add_sub_cancel_left]
  rfl

/-- **A well-formed stream of `n` segments is `0x54 ‖` the segments' traces.** -/
theorem stream_of_wf {B : List UInt8} {n : ℕ} (hl : B.length = 1 + n * (N4c.segB - 1))
    (h0 : B.head? = some tagTrace)
    (hw : ∀ i < n, WfAt B (1 + i * (N4c.segB - 1)) (itemsOf seq4)) :
    B = tagTrace :: traceBytes ((List.range n).map fun i =>
      Read.readItems B (1 + i * (N4c.segB - 1)) (itemsOf seq4)).flatten := by
  obtain ⟨b, B', rfl⟩ : ∃ b B', B = b :: B' := by
    cases B with
    | nil => simp at h0
    | cons b B' => exact ⟨b, B', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at h0
  subst h0
  congr 1
  have hB : B' = ((tagTrace :: B').drop 1).take (n * (N4c.segB - 1)) := by
    simp only [List.drop_one, List.tail_cons]
    rw [List.take_of_length_le]; simp at hl; omega
  refine hB.trans ?_
  rw [take_mul_flatten, traceBytes_flatten, List.map_map]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [Function.comp_apply, ← slenS_seq4, take_readItems _ _ _ (slenS_seq4 ▸ hw i hi')]
  rw [slenS_seq4, hl]
  have : (i + 1) * (N4c.segB - 1) ≤ n * (N4c.segB - 1) := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_one_mul] at this
  omega

end N4s
end FR
