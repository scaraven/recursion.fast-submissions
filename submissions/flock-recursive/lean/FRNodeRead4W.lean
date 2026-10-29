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

/-! ## The spacers (R-A′) -/

/-- **The spacer's constant bytes** at stream offset `o`: its length word and its query,
`enc64 89 ‖ spacerQ` (97 bytes; its answer, the 32 bytes after, is free). -/
def SpAt (B : List UInt8) (o : ℕ) : Prop := (B.drop o).take 97 = enc64 89 ++ spacerQ.data.toList

theorem spItem_slen : spItem.slen = 129 := rfl

/-- **On its constant bytes, a spacer's 129 bytes are the spacer entry** with the answer read off the
stream (`spAnsB`). -/
theorem spacer_bytes {B : List UInt8} {o : ℕ} (hl : o + 129 ≤ B.length) (hs : SpAt B o) :
    (B.drop o).take 129 = traceBytes [spEntry (spAnsB B o)] := by
  have hq97 : (enc64 89 ++ spacerQ.data.toList).length = 97 := by
    rw [List.length_append, enc64_length, Array.length_toList]; exact congrArg (8 + ·) spacerQ_size
  have hw : (B.drop o).take 8 = enc64 spItem.qlen := by
    have : ((B.drop o).take 97).take 8 = (B.drop o).take 8 := by rw [List.take_take]; rfl
    rw [← this, hs, List.take_left' (enc64_length _)]; rfl
  have hq : (Read.entryAt B o spItem).1 = spacerQ := by
    have h2 : ((B.drop o).take 97).drop 8 = (B.drop (o + 8)).take 89 := by
      rw [List.drop_take, List.drop_drop, Nat.add_comm]
    have h3 : (B.drop (o + 8)).take 89 = spacerQ.data.toList := by
      rw [← h2, hs, List.drop_left' (enc64_length _)]
    show (⟨((B.drop (o + 8)).take spItem.qlen).toArray⟩ : ByteArray) = spacerQ
    rw [show spItem.qlen = 89 from rfl, h3]
  rw [← spItem_slen, entry_bytes (by rw [spItem_slen]; exact hl) hw, hq, traceBytes, List.flatMap_singleton]
  rfl

theorem traceBytes_append (a b : Trace) : traceBytes (a ++ b) = traceBytes a ++ traceBytes b := by
  simp [traceBytes]

/-- **A well-formed aggregate stream of `n` segments is `0x54 ‖ V_A`'s trace** (R-A′): the
segments' traces read at `1 + i·strideB`, the spacer entry before segment `i ≥ 1` (its constant bytes
at `i·strideB − 128`, its answer read off the stream). For `n = 1` (a single proof's stream) there is
no spacer. -/
theorem stream_of_wf {B : List UInt8} {n : ℕ} (hl : B.length = N4c.aggB n)
    (h0 : B.head? = some tagTrace)
    (hw : ∀ i < n, WfAt B (1 + i * N4c.strideB) (itemsOf seq4))
    (hs : ∀ i < n, 0 < i → SpAt B (i * N4c.strideB - 128)) :
    B = tagTrace :: traceBytes (aggTrace (fun i => spAnsB B (i * N4c.strideB - 128))
      ((List.range n).map fun i => Read.readItems B (1 + i * N4c.strideB) (itemsOf seq4))) := by
  rw [aggTrace_range]
  set g : ℕ → Trace := fun i => (if i = 0 then [] else [spEntry (spAnsB B (i * N4c.strideB - 128))]) ++
    Read.readItems B (1 + i * N4c.strideB) (itemsOf seq4) with hg
  have hmono : ∀ m m', m ≤ m' → N4c.aggB m ≤ N4c.aggB m' := fun m m' h => by
    simp only [N4c.aggB]
    have := Nat.mul_le_mul_right (N4c.segB - 1) h
    have := Nat.mul_le_mul_right N4c.spacerB (Nat.sub_le_sub_right h 1)
    omega
  have key : ∀ m ≤ n, B.take (N4c.aggB m) = tagTrace :: traceBytes ((List.range m).map g).flatten := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨b, B', rfl⟩ : ∃ b B', B = b :: B' := by
        cases B with
        | nil => simp at h0
        | cons b B' => exact ⟨b, B', rfl⟩
      simp only [List.head?_cons, Option.some.injEq] at h0
      subst h0
      simp [N4c.aggB, traceBytes]
    | succ m ih =>
      intro hm
      have hle := hmono (m + 1) n hm
      rw [List.range_succ, List.map_append, List.flatten_append, traceBytes_append, ← List.cons_append,
        ← ih (by omega), List.map_singleton, List.flatten_singleton]
      have hsplit : N4c.aggB (m + 1) = N4c.aggB m + (N4c.aggB (m + 1) - N4c.aggB m) := by
        have := hmono m (m + 1) (by omega); omega
      rw [hsplit, List.take_add]
      congr 1
      have hT : slenS (itemsOf seq4) = N4c.segB - 1 := slenS_seq4
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · -- segment 0, no spacer
        have hd : N4c.aggB 1 - N4c.aggB 0 = slenS (itemsOf seq4) := by
          rw [hT]; simp [N4c.aggB]
        rw [hd, hg]
        simp only [Nat.zero_mul, Nat.add_zero]
        rw [show N4c.aggB 0 = 1 by simp [N4c.aggB]]
        refine take_readItems B _ 1 (by simpa using hw 0 (by omega)) ?_
        rw [hl, hT]
        have := hmono 1 n (by omega)
        simp only [N4c.aggB] at this ⊢; omega
      · -- spacer `m`, then segment `m`
        obtain ⟨hB, -, hB'⟩ := N4c.aggB_blocks (k := m) (by omega)
        have hs1 := N4c.aggB_succ m (by omega)
        have hd : N4c.aggB (m + 1) - N4c.aggB m = 129 + slenS (itemsOf seq4) := by
          rw [hs1, hT]; simp only [N4c.spacerB]; omega
        have hst : N4c.strideB = N4c.segB - 1 + 129 := rfl
        have ho : m * N4c.strideB - 128 = N4c.aggB m := by rw [hB']
        have hsp : SpAt B (N4c.aggB m) := by rw [← ho]; exact hs m (by omega) hm0
        have hl' : N4c.aggB m + 129 ≤ B.length := by rw [hl]; omega
        rw [hd, List.take_add, hg]
        simp only [if_neg (Nat.pos_iff_ne_zero.1 hm0)]
        rw [traceBytes_append, ho, spacer_bytes hl' hsp, List.drop_drop]
        refine congrArg (traceBytes [spEntry (spAnsB B (N4c.aggB m))] ++ ·) ?_
        have hoff : N4c.aggB m + 129 = 1 + m * N4c.strideB := by
          have : 128 ≤ m * N4c.strideB := by
            have : N4c.strideB ≤ m * N4c.strideB := Nat.le_mul_of_pos_left _ hm0
            simp only [N4c.strideB, N4c.segB, N4c.spacerB] at this ⊢; omega
          omega
        rw [hoff]
        refine take_readItems B _ _ (hw m (by omega)) ?_
        rw [hl]; omega
  have := key n le_rfl
  rwa [List.take_of_length_le (by rw [hl])] at this

end N4s
end FR
