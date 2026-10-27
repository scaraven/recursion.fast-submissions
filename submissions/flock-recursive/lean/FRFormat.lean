-- New for `flock-recursive` (BLUEPRINT §7, stage S-0; §1, Appendix A.3, A.5).
import FRTranscriptDefs
import Mathlib.Data.List.Basic

/-!
# The proof format: fields, `piSize`, `parse`, `serialise`, `reassemble`

BLUEPRINT §1.1, A.3, A.5.

* `fieldSize f`: the bytes of field `f` (A.3's row `f`), **computed from the phase table**
  (`FRTranscriptDefs.phases`): an absorb puts its message in its field, the seed's `hdr` is field 0,
  the queries of level `i` put `tᵢ` columns in field 14 and `tᵢ · sibᵢ` siblings in field 15
  (revision 3.1's numbering).
  `fieldSizes_eq` is A.3's column; **`piSize_eq : piSize = 755680`** (the checked sum).
* `kindOf π`: `W` unless byte 0 is a kind byte; a kind byte with `|π| ≠ piSize` is `bad`.
* `serialise` concatenates the fields, `parse` cuts a proof of `piSize` bytes at the offsets;
  **`parse_serialise`**: `parse (serialise fs) = some fs` when the sizes are A.3's.
* `reassemble tr` (A.5): the proof a trace of the item sequence determines: `hdr` from the seed's
  bytes `64 … 111` (after the tag), every absorbed message into its field, columns, and per
  Merkle-node query the half that is not on the path (bit `h` of the position), dummies as zeros.
-/

namespace FR
open RecursionFast

/-! ## Field sizes (A.3) -/

/-- The bytes of field `f` that a phase contributes. -/
def Shape.bytesTo (f : ℕ) : Shape → ℕ
  | .seed => if f = fHdr then 48 else 0
  | .absorb g len => if f = g then len else 0
  | .squeezes _ _ => 0
  | .uni g => if f = g then uniBytes else 0
  | .rounds g n _ inK _ => if f = g then n * roundBytes inK else 0
  | .queries i =>
    if f = fCols then (lvlStar i).t * (lvlStar i).rows * 16
    else if f = fSibs then (lvlStar i).t * (lvlStar i).sib * 32 else 0

/-- **The size of field `f`**: the sum over the phase table. -/
def fieldSize (f : ℕ) : ℕ := (phases.map fun p => p.shape.bytesTo f).sum

/-- The field sizes in order. -/
def fieldSizes : List ℕ := (List.range nFields).map fieldSize

/-- **`piSize`**: the sum of the field sizes. -/
def piSize : ℕ := fieldSizes.sum

/-- A.3's column. -/
theorem fieldSizes_eq : fieldSizes = [48, 128, 2048, 1248, 32, 800, 1344, 1440, 48, 8192, 1008, 48,
    2112, 672, 45056, 4096, 445696, 241664] := by decide +kernel

/-- **`piSize = 755,680`** (A.3, revision 3.8.2: `48 + 128 + 18,992 + 45,056 + 4,096 + 445,696 +
241,664`). -/
theorem piSize_eq : piSize = 755680 := by rw [piSize, fieldSizes_eq]; rfl

theorem piSize_le_proofCap : piSize ≤ proofCap := by rw [piSize_eq]; decide

/-- The offset of field `f`. -/
def fieldOff (f : ℕ) : ℕ := (fieldSizes.take f).sum

/-- The offset, inside its field, of the first byte phase number `n` contributes to field `f`. -/
def phaseOff (n f : ℕ) : ℕ := ((phases.take n).map fun p => p.shape.bytesTo f).sum

/-! ## `hdr` and `stmt` (§1.1) -/

/-- `hdr = kindByte ‖ m ‖ zero(14) ‖ pub(32)` (`pub` is the chain start `s` of a leaf kind). -/
def hdrBytes (k : Kind) (pub : Digest) : List UInt8 :=
  [k.byte, k.m.toUInt8] ++ List.replicate 14 0 ++ pub.toList

/-- A leaf kind's `stmt` (revision 3.3): the padded message blocks of `leafStmt h n`,
`tagLeaf ‖ h ‖ enc64 n ‖ 0^23 ‖ 0^64` (128 bytes). -/
def stmtLeafBytes (n : ℕ) (h : Digest) : List UInt8 :=
  tagLeaf :: h.toList ++ enc64 n ++ List.replicate (23 + 64) 0

/-- A node's `stmt`: the padded message blocks of `nodeStmt c₁ c₂`, `tagNode ‖ c₁ ‖ c₂ ‖ 0^63`. -/
def stmtNodeBytes (c₁ c₂ : Digest) : List UInt8 := RecursionFast.tagNode :: c₁.toList ++ c₂.toList ++ List.replicate 63 0

/-- A leaf kind's chain length: `n = 2^(m − 14)`. -/
def leafN (k : Kind) : ℕ := 2 ^ (k.m - 14)

theorem hdrBytes_length (k : Kind) (pub : Digest) : (hdrBytes k pub).length = 48 := by
  simp [hdrBytes]

theorem stmtLeafBytes_length (n : ℕ) (h : Digest) : (stmtLeafBytes n h).length = 128 := by
  simp [stmtLeafBytes, enc64]

theorem stmtNodeBytes_length (c₁ c₂ : Digest) : (stmtNodeBytes c₁ c₂).length = 128 := by
  simp [stmtNodeBytes]

/-! ## The kind of a proof -/

/-- What `V` does with a proof: decide the witness-sending relation (`W`), reject (`bad`), or run
the program of a SNARK kind. -/
inductive PKind where
  | W | bad
  | snark (k : Kind)
  deriving DecidableEq, Repr

/-- **The kind of a proof**: byte 0 a kind byte and `|π| = piSize`, or `bad` for a kind byte with
another size, or `W` otherwise (S-0-m5: decided on the first **byte**, not §1.1's tag word; a
witness-sending proof's first word is `0` or `1`, so its first byte is `0x00`/`0x01`, never a
kind byte; the empty proof and any other first byte are `W` too, whose branch decides `Rel` and
rejects every non-canonical encoding). -/
def kindOf (π : Proof) : PKind :=
  match (byteAt? π 0).bind Kind.ofByte? with
  | none => .W
  | some k => if π.size = piSize then .snark k else .bad

/-! ## `serialise`, `parse` -/

/-- The proof whose fields are `fs`, in order. -/
def serialise (fs : List ByteArray) : Proof := ⟨(fs.flatMap fun b => b.data.toList).toArray⟩

/-- Field `f` of a proof: bytes `[fieldOff f, fieldOff f + fieldSize f)`. -/
def field (π : Proof) (f : ℕ) : ByteArray := π.extract (fieldOff f) (fieldOff f + fieldSize f)

/-- **The fields of a proof of `piSize` bytes.** -/
def parse (π : Proof) : Option (List ByteArray) :=
  if π.size = piSize then some ((List.range nFields).map (field π)) else none

theorem fieldSizes_length : fieldSizes.length = nFields := by simp [fieldSizes]

theorem toList_extract (a : ByteArray) (i j : ℕ) :
    (a.extract i j).data.toList = (a.data.toList.drop i).take (j - i) := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract]

/-- **`parse ∘ serialise = some`** on fields of A.3's sizes. -/
theorem parse_serialise (fs : List ByteArray) (h : fs.map ByteArray.size = fieldSizes) :
    parse (serialise fs) = some fs := by
  set L := fs.map fun b => b.data.toList
  have hL : L.map List.length = fieldSizes := by
    rw [← h, List.map_map]; rfl
  have hdata : (serialise fs).data.toList = L.flatten := rfl
  have hsize : (serialise fs).size = piSize := by
    rw [ByteArray.size, ← Array.length_toList, hdata, List.length_flatten, hL, piSize]
  have hlen : fs.length = nFields := by rw [← fieldSizes_length, ← h, List.length_map]
  simp only [parse, hsize, ite_true, Option.some.injEq]
  refine List.ext_getElem (by simp [hlen]) fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range]
  apply ByteArray.ext; apply Array.ext'
  have hi : i < L.length := by simp [L]; exact h₂
  have hsz : fieldSize i = (L[i]).length := by
    rw [← List.getElem_map List.length (h := by simpa using hi)]
    simp only [hL, fieldSizes, List.getElem_map, List.getElem_range]
  rw [field, toList_extract, hdata, Nat.add_sub_cancel_left, fieldOff, ← hL, List.drop_sum_flatten,
    hsz, List.drop_eq_getElem_cons hi, List.flatten_cons, List.take_left' rfl]
  simp [L]

/-- A proof of another size does not parse (the negative control of `parse_serialise`). -/
theorem parse_size {π : Proof} (h : π.size ≠ piSize) : parse π = none := by simp [parse, h]

/-! ## `reassemble` (A.5) -/

/-- An array of `n` zero bytes. -/
def zeros (n : ℕ) : ByteArray := ⟨Array.replicate n 0⟩

/-- Bytes `[a, a + n)` of the query of entry `j` of the trace. -/
def qBytes (tr : Array (ByteArray × Digest)) (j a n : ℕ) : ByteArray :=
  ((tr.getD j (ByteArray.empty, 0)).1).extract a (a + n)

/-- The kind a trace's seed declares (byte `64` of its payload, after the 7-byte tag). -/
def traceKind (tr : Array (ByteArray × Digest)) : Kind :=
  ((((tr.getD 0 (ByteArray.empty, 0)).1).data[71]?).bind Kind.ofByte?).getD .L32

/-- The walk's state: the fields so far, the item index, the last position answers. -/
structure RSt where
  out : Array ByteArray
  ix : ℕ
  ans : List Digest

/-- Append `b` to field `f`. -/
def RSt.put (s : RSt) (f : ℕ) (b : ByteArray) : RSt := { s with out := s.out.modify f (· ++ b) }

/-- The sibling half of a Merkle-node query: `right` if bit `h` of the position is `0`, else
`left`; zeros for a dummy (`h ≥ sib` of the kind). -/
def sibling (k : Kind) (i h j : ℕ) (q : ByteArray) : ByteArray :=
  if h < (lvl k i).sib then
    if j / 2 ^ h % 2 = 0 then q.extract 40 72 else q.extract 8 40
  else zeros 32

/-- One phase of `reassemble`. -/
def rsPhase (k : Kind) (tr : Array (ByteArray × Digest)) (s : RSt) : Shape → RSt
  | .seed => { s.put fHdr (qBytes tr s.ix 71 48) with ix := s.ix + 1 }
  | .absorb f len => { s.put f (qBytes tr s.ix 40 len) with ix := s.ix + 1 }
  | .squeezes n ch =>
    let s' := { s with ix := s.ix + n }
    match ch with
    | .pos _ => { s' with ans := (List.range n).map fun j => (tr.getD (s.ix + j) (ByteArray.empty, 0)).2 }
    | _ => s'
  | .uni f => { s.put f (qBytes tr s.ix 40 uniBytes) with ix := s.ix + 2 }
  | .rounds f n _ inK _ =>
    (List.range n).foldl (fun s j => s.put f (qBytes tr (s.ix + 2 * j) 40 (roundBytes inK)))
      s |> fun s' => { s' with ix := s.ix + 2 * n }
  | .queries i =>
    let L := lvlStar i
    let per := 1 + L.sib
    let s' := (List.range L.t).foldl (fun s p =>
      let base := s.ix + per * p
      let j := posOf k i s.ans p
      let s := s.put fCols (qBytes tr base 8 (L.rows * 16))
      (List.range L.sib).foldl (fun s h =>
        s.put fSibs (sibling k i h j ((tr.getD (base + 1 + h) (ByteArray.empty, 0)).1))) s) s
    { s' with ix := s.ix + per * L.t }

/-- **`reassemble tr`** (A.5): the proof a trace of the item sequence carries. -/
def reassemble (tr : Trace) : Proof :=
  let a := tr.toArray
  let k := traceKind a
  let s := phases.foldl (fun s p => rsPhase k a s p.shape)
    ⟨Array.replicate nFields ByteArray.empty, 0, []⟩
  serialise s.out.toList


/-! ## Controls -/

theorem kindOf_snark {π : Proof} {k : Kind} (h0 : π.data[0]? = some k.byte) (hs : π.size = piSize) :
    kindOf π = .snark k := by simp [kindOf, byteAt?_eq, h0, Kind.ofByte?_byte, hs]

/-- Negative: a kind byte with another size is rejected (`bad`), not run. -/
theorem kindOf_bad {π : Proof} {k : Kind} (h0 : π.data[0]? = some k.byte) (hs : π.size ≠ piSize) :
    kindOf π = .bad := by simp [kindOf, byteAt?_eq, h0, Kind.ofByte?_byte, hs]

/-- A witness-sending proof (first word `0` or `1`) is the `W` kind. -/
theorem kindOf_W {π : Proof} {b : UInt8} (h0 : π.data[0]? = some b) (hb : b = 0 ∨ b = 1) :
    kindOf π = .W := by
  rcases hb with rfl | rfl <;> simp [kindOf, byteAt?_eq, h0, Kind.ofByte?]

theorem kindOf_small : kindOf ⟨#[0x4E]⟩ = .bad ∧ kindOf ⟨#[1, 0]⟩ = .W ∧ kindOf ByteArray.empty = .W := by
  refine ⟨kindOf_bad (k := .N30) rfl (by rw [piSize_eq]; decide), kindOf_W rfl (by decide), rfl⟩

end FR
