-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2, A.2, A.7; stage S-E13a, track L-circ):
-- the first rows of the pack map (S-N2's `Gap4`: the kind tie and `wf`).
import FRNodeKinds4
import FRVIR4Mux

/-!
# The pack rows' data: stream elements, the kind tie, the stream's constant elements

A child's trace is hashed by H as the stream `0x54 ‖ traceBytes tr` (`FRBlockStream`). Stream
element `e` (bytes `16e … 16e + 15`) is the H cell `sCell b0 e` of a stream whose first block is
`b0` (A.7, `elem_slot`). A linear row over cells can pin or equate **whole elements** only. Within
one trace starting at stream offset 1 the fields the rows need are whole elements:

* **element 0** is `0x54 ‖ enc64 119 ‖ "FRSEED0"`: the tag, the seed's length word, its query tag;
* every later item starts 16-aligned (`items_aligned`), so its first element is
  `enc64 |q| ‖ tag(q)` (`winB`): the length word and the query's 8-byte tag;
* **element 5** is `hdr[0…16)` (the seed query's bytes 71–86): `kind ‖ m ‖ 0¹⁴`, the constant the
  slot's program asserts (`seedOpsG`'s `const`).

This module has the data: `sCell`, the per-item element values (`winF`, `wfData`, the closed
`wfSeg`), the pin row `pinRow`, the stream rows `wfRows`, the kind constants `kConst` and the kind
tie `kindRow`. `FRNodeRows4` places them in the slots' link regions (`packRows4`);
`FRNodeRows4PackSound` proves what they give.
-/

namespace FR
namespace Rev4
open RecursionFast Circ

/-! ## Stream elements -/

/-- **The H cell of stream element `e`** of a stream whose first block is `b0`: message slot
`4 + e mod 4` of block `b0 + ⌊e/4⌋` (A.7). -/
def sCell (b0 e : ℕ) : ℕ := (b0 + e / 4) * 128 + 4 + e % 4

/-- An item's query tag (A.2): the seed's 7 bytes, every other query's 8. -/
def itemTag : Item → List UInt8
  | .seed => tagSeed
  | .absorb _ => tagAbs
  | .squeeze => tagSqz
  | .col i => tagCol i
  | .node i _ => tagNode i

/-- **The element where an item starts**, at stream offset `o`: the stream's tag if `o ≡ 1`
(the first item), the length word `enc64 |q|`, the query's tag. -/
def winB (o : ℕ) (it : Item) : List UInt8 :=
  (if o % 16 = 1 then [tagTrace] else []) ++ enc64 it.qlen ++ itemTag it

/-- The element whose bytes are `b` (zero-padded to 16). -/
def winFB (b : List UInt8) : F := F.ofBytes (Vector.ofFn fun r : Fin 16 => b.getD r 0)

/-- Its value (the byte list built once: `wfSeg` is a closed constant built at process start). -/
def winF (o : ℕ) (it : Item) : F := winFB (winB o it)

/-- **The pinned elements** of the items `its` from stream offset `o`: (element, value). -/
def wfData : ℕ → List Item → List (ℕ × F)
  | _, [] => []
  | o, it :: its => (o / 16, winF o it) :: wfData (o + it.slen) its

/-- **One trace's pinned elements** (`seq4`'s 8,783 items from offset 1; a closed constant). -/
def wfSeg : List (ℕ × F) := wfData 1 (itemsOf seq4)

/-! ## The rows -/

/-- **`one · (x − c · one) = 0`**: at `one = 1`, cell `x` holds `c`. -/
def pinRow (one x : ℕ) (c : F) : Row := ⟨Lin.cell one, (Lin.cell x).sub ((Lin.cell one).smul c), []⟩

/-- **The `wf` rows of a stream at block `b0`**: each item's first element pinned. -/
def wfRows (one b0 : ℕ) : List Row := wfSeg.map fun p => pinRow one (sCell b0 p.1) p.2

/-- **The kind constant** of index `ι` of group `G`: `hdr[0…16)` of a `G ι` proof, as the slot
program's seed check has it (`FRVIR4Mux.seedOpsG`). -/
def kConst (G : Grp) (ι : Kind) : F :=
  F.ofBytes (bytesAt (bytesOf ([(G ι).byte, (G ι).d.m.toUInt8] ++ List.replicate 46 0)) 0 16)

/-- **The kind tie**: stream element `h5` (`hdr[0…16)`) is `Σ_ι K_ι · s′_ι` over the slot's
selector copies `sel ι`. -/
def kindRow (one h5 : ℕ) (sel : Kind → ℕ) (G : Grp) : Row :=
  ⟨Lin.cell one, (Lin.cell h5).sub (Circ.kinds.map fun ι => (sel ι, kConst G ι)), []⟩

/-! ## Facts -/

theorem pinRow_holds {w : Asg} {one x : ℕ} {c : F} (hone : w one = 1) (h : (pinRow one x c).Holds w) :
    w x = c := by
  simp only [pinRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_smul, hone, one_mul, mul_one,
    Lin.ev_nil] at h
  exact sub_eq_zero.1 h

theorem pinRow_ctl (w : Asg) (one x : ℕ) (c : F) (hone : w one = 1) :
    (pinRow one x c).Holds w ↔ w x = c :=
  ⟨pinRow_holds hone, fun h => by
    simp only [pinRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_smul, hone, h, one_mul, mul_one,
      sub_self, Lin.ev_nil]⟩

theorem kindRow_holds {w : Asg} {one h5 : ℕ} {sel : Kind → ℕ} {G : Grp} (hone : w one = 1)
    (h : (kindRow one h5 sel G).Holds w) :
    w h5 = kConst G .L32 * w (sel .L32) + kConst G .P30 * w (sel .P30) + kConst G .N30 * w (sel .N30) := by
  simp only [kindRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, hone, one_mul, Lin.ev_nil] at h
  have h' := sub_eq_zero.1 h
  rw [h']
  simp [Circ.kinds, Lin.ev]
  ring

theorem wfData_length : ∀ (o : ℕ) (its : List Item), (wfData o its).length = its.length
  | _, [] => rfl
  | o, _ :: its => by simp [wfData, wfData_length _ its]

theorem wfSeg_length : wfSeg.length = 8783 := by
  rw [wfSeg, wfData_length, itemsOf_seq4_length]

/-- The bytes an item's stream occupies. -/
def slenL (its : List Item) : ℕ := (its.map Item.slen).sum

/-- **Every pinned element lies inside the items' bytes.** -/
theorem wfData_lt : ∀ (o : ℕ) (its : List Item), ∀ q ∈ wfData o its, 16 * q.1 < o + slenL its := by
  intro o its
  induction its generalizing o with
  | nil => simp [wfData]
  | cons it its ih =>
    intro q hq
    simp only [wfData, List.mem_cons] at hq
    have hs : slenL (it :: its) = it.slen + slenL its := by simp [slenL]
    have : 0 < it.slen := by simp [Item.slen]
    rcases hq with rfl | hq
    · dsimp only; omega
    · have := ih (o + it.slen) q hq; omega

/-- (+) A pinned element of a segment lies below the segment's `segB` bytes. -/
theorem wfSeg_lt : ∀ p ∈ wfSeg, 16 * p.1 < N4c.segB := fun p hp => by
  have hb : 1 + slenL (itemsOf seq4) = N4c.segB := by
    rw [N4c.segB_eq, streamBytesOf, slenL]
    congr 2
  have := wfData_lt 1 (itemsOf seq4) p hp
  omega

/-- (+) The kind constants' first byte is the kind byte (node group, segment group). -/
theorem kConst_byte (ι : Kind) :
    (F.toBytes (kConst nodeGrp ι))[0] = (nodeAt ι).byte ∧ (F.toBytes (kConst segGrp ι))[0] = (segAt ι).byte := by
  simp only [kConst, F.toBytes_ofBytes]
  cases ι <;> decide

/-- (−) The three node constants are distinct (so the tie fixes the index, not only the group). -/
theorem kConst_ne : kConst nodeGrp .L32 ≠ kConst nodeGrp .P30 ∧ kConst nodeGrp .P30 ≠ kConst nodeGrp .N30 ∧
    kConst segGrp .L32 ≠ kConst segGrp .N30 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  · have := congrArg (fun a => (F.toBytes a)[0]) h
    simp only [kConst, F.toBytes_ofBytes] at this
    revert this; decide

/-- (+) The first element of a trace's stream: `0x54 ‖ enc64 119 ‖ "FRSEED0"`; (−) a later
absorb's element has no `0x54`. -/
theorem winB_ctl : winB 1 .seed = [0x54] ++ enc64 119 ++ tagSeed ∧ (winB 1 .seed).length = 16 ∧
    (winB 160 (.absorb 128)).length = 16 ∧ (winB 160 (.absorb 128)).head? ≠ some 0x54 := by
  refine ⟨rfl, by decide, by decide, by decide⟩

end Rev4
end FR
