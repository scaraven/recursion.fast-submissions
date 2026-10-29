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

**R-A′ (revision 4.4.1).** An aggregate's stream is `0x54 ‖ tr₁ ‖ sp ‖ tr₂ ‖ … ‖ sp ‖ tr_k` with
the 129-byte spacer entry `sp` (`FRAgg.spacerQ`), so segment `s` starts at `1 + s·strideB` with
`strideB = 64 · 24,238`: its elements are segment 0's shifted by `s·sBlk` blocks. Two elements per
spacer are not whole constants, because an entry ends with its (random) answer:
* the segment's **element 0** is the spacer answer's last byte, then `enc64 119 ‖ "FRSEED0"`: it is
  `seedM` plus 8 Boolean cells at bits 0–7 (`decRow`), so bytes 1–15 are pinned;
* the spacer's **element 6** is its query's last byte (`0`), then 15 answer bytes: it is 120
  Boolean cells at bits 8–127, so byte 0 is zero.
The spacer's elements 0–5 (`enc64 89 ‖ "FRABS000"`, the zero state, the message's first 48 zero
bytes) are whole constants (`spPin`). `headRows` are these rows; a stream's segment 0 has instead
its element 0 pinned whole (`seedW`).

This module has the data: `sCell`, the per-item element values (`winF`, `wfData`, the closed
`wfSeg`: every item's first element but the seed's), the pin row `pinRow`, the stream rows
`wfRows`, the head rows `headRows`, the kind constants `kConst` and the kind tie `kindRow`.
`FRNodeRows4` places them in the slots' link regions (`packRows4`); `FRNodeRows4PackSound` proves
what they give.
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

/-- **One trace's pinned elements past element 0** (`seq4`'s items from offset 1 but the seed's
element 0, which `headRows` binds: 8,782; a closed constant). -/
def wfSeg : List (ℕ × F) := (wfData 1 (itemsOf seq4)).tail

/-! ## The rows -/

/-- **`one · (x − c · one) = 0`**: at `one = 1`, cell `x` holds `c`. -/
def pinRow (one x : ℕ) (c : F) : Row := ⟨Lin.cell one, (Lin.cell x).sub ((Lin.cell one).smul c), []⟩

/-- **The `wf` rows of a stream at block `b0`**: each item's first element pinned. -/
def wfRows (one b0 : ℕ) : List Row := wfSeg.map fun p => pinRow one (sCell b0 p.1) p.2

/-! ## A segment's element 0 and the spacer (R-A′) -/

/-- **Element 0 of a stream's segment 0**: `0x54 ‖ enc64 119 ‖ "FRSEED0"`. -/
def seedW : F := winF 1 .seed

/-- Element 0 of a later segment with its byte 0 (the spacer answer's last byte) zero. -/
def seedM : F := winFB ([0] ++ enc64 119 ++ tagSeed)

/-- **The spacer entry's constant bytes**: `enc64 89 ‖ "FRABS000" ‖ 0^81` (`enc64 |q| ‖ q`,
`q = FRAgg.spacerQ`; `FRNodeRows4PackSound.spBytes_eq`). -/
def spBytes : List UInt8 := enc64 89 ++ tagAbs ++ List.replicate 81 0

/-- The spacer's whole constant element `j < 6`. -/
def spPin (j : ℕ) : F := winFB ((spBytes.drop (16 * j)).take 16)

/-- `c` is a bit: `c · (one − c) = 0`. -/
def boolRow (one c : ℕ) : Row := ⟨Lin.cell c, (Lin.cell one).sub (Lin.cell c), []⟩

/-- The bits `cell q` (`q < n`) at the element's bit positions `d + q`: `Σ_q x^(d+q) · cell q`. -/
def packAt (cell : ℕ → ℕ) (d n : ℕ) : Lin :=
  (List.range n).map fun q => (cell q, bitBasis ⟨(d + q) % 128, Nat.mod_lt _ (by norm_num)⟩)

/-- **`one · (x − c · one − bits) = 0`**: cell `x` is the constant `c` plus the packed bits. -/
def decRow (one x : ℕ) (c : F) (bits : Lin) : Row :=
  ⟨Lin.cell one, ((Lin.cell x).sub ((Lin.cell one).smul c)).sub bits, []⟩

/-- **The head rows of segment `s` of a stream, at block `b0`** (R-A′): for `s = 0` its element 0
pinned (`seedW`); for `s ≥ 1` the spacer before it (blocks `b0 − 2`, `b0 − 1`): elements 0–5
pinned, element 6 as 120 bits at positions 8–127 (`cell 0 … 119`), and the segment's element 0 as
`seedM` plus 8 bits at positions 0–7 (`cell 120 … 127`); 136 rows. -/
def headRows (one b0 s : ℕ) (cell : ℕ → ℕ) : List Row :=
  if s = 0 then [pinRow one (sCell b0 0) seedW]
  else (List.range 6).map (fun j => pinRow one (sCell (b0 - 2) j) (spPin j)) ++
    (List.range 128).map (fun q => boolRow one (cell q)) ++
    [decRow one (sCell (b0 - 2) 6) 0 (packAt cell 8 120),
     decRow one (sCell b0 0) seedM (packAt (fun q => cell (120 + q)) 0 8)]

/-- **Spacer `s`'s 128 bit cells** of signed child `σ` (`s ≥ 1`): L elements `11,264 + 128 (s − 1) + q`
of `σ`'s stride (S-E13b's `padRows` decomposition cells, which R-A′'s whole blocks free). -/
def spC (κ : NodeKind) (σ s q : ℕ) : ℕ := κ.lBase * 128 + σ * 2 ^ 14 + 11264 + 128 * (s - 1) + q

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

theorem wfSeg_length : wfSeg.length = 8782 := by
  rw [wfSeg, List.length_tail, wfData_length, itemsOf_seq4_length]

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
  have := wfData_lt 1 (itemsOf seq4) p (List.mem_of_mem_tail hp)
  omega

theorem headRows_length (one b0 s : ℕ) (cell : ℕ → ℕ) :
    (headRows one b0 s cell).length = if s = 0 then 1 else 136 := by
  unfold headRows; split_ifs <;> simp

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
