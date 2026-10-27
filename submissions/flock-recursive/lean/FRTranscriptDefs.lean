-- New for `flock-recursive` (BLUEPRINT §7, stage S-0; Appendix A.1, A.2, A.4; revision 3.1).
import FRField256
import FRMerkle
import RecursionFast.Contract.Oracle
import RecursionFast.Contract.Signature

/-!
# The transcript's definitions: kinds, tags, ladders, challenge maps, **the item sequence**

BLUEPRINT §1.2, §2.2, A.1, A.2, A.4. Everything that revision 3.1 may change (round counts, squeeze
counts, the final message's size, the ladders) is a constant of **one table**, `phases`; the item
sequence `items` (A.4), the proof's fields (`FRFormat`, A.3) and the verifier program (`FRVIR.gen`)
are all computed from it, so the three cannot drift apart.

* `Kind`: `L32` (`'L'`, the tree leaf, `m = 32`), `P30` (`'P'`, the stream leaf, `m = 30`), `N30`
  (`'N'`, a node, `m = 30`). One item sequence for all three (B-2): every phase is sized for
  `m* = 32` and a kind's unused items are dummy queries (`Shape.rounds`'s `real`, the ladders'
  sibling counts).
* Tags (A.2): seed `"FRSEED0"` (7 bytes), absorb `"FRABS000"`, squeeze `"FRSQZ000"`, Merkle node
  `"FRMNOD" ‖ i ‖ 0`, column `"FRMCOL" ‖ i ‖ 0`.
* Challenge maps (A.2): `chF a c` is bytes `16c … 16c + 15` of an answer as an F element; `chK a` all
  32 bytes as a K element; `idxOf b a i` bits `[ib, (i+1)b)` of `natLE a`.
* `items_length : items.length = 8874` (`decide`, a closed form of the table), `fsItems_length`
  (431), `streamBytes_eq` (the hashed stream `0x54 ‖ traceBytes`), `chainLen_eq` (compressions).
-/

namespace FR
open RecursionFast

/-! ## Kinds -/

/-- The three proof kinds of the SNARK path (the `W` kind is `FRFormat`'s). -/
inductive Kind where
  | L32 | P30 | N30
  deriving DecidableEq, Repr, Inhabited

namespace Kind

/-- The kind byte of `hdr` (A.3): `'L'`, `'P'`, `'N'`. -/
def byte : Kind → UInt8
  | L32 => 0x4C | P30 => 0x50 | N30 => 0x4E

/-- The kind's `m` (`log₂` of the witness length in bits). -/
def m : Kind → ℕ
  | L32 => 32 | _ => 30

/-- The kind of a kind byte. -/
def ofByte? (b : UInt8) : Option Kind :=
  if b = 0x4C then some L32 else if b = 0x50 then some P30 else if b = 0x4E then some N30
  else none

theorem ofByte?_byte (k : Kind) : ofByte? k.byte = some k := by cases k <;> decide

/-- Is the kind a node? (The node-only phases Lr and E are real only for `'N'`.) -/
def isNode : Kind → Bool
  | N30 => true | _ => false

end Kind

/-- `m* = 32`: the item sequence is sized for the larger kind. -/
def mStar : ℕ := 32

/-! ## The ladder (§2.2) -/

/-- One level of the Ligerito ladder. -/
structure Level where
  /-- Fold rounds `ℓ`: the committed matrix has `2^ℓ` rows. -/
  ell : ℕ
  /-- `log₂ n`: the bits of a position. -/
  logN : ℕ
  /-- Queried positions (every index is opened, duplicates included). -/
  t : ℕ
  /-- Cap depth: the cap holds `2^cap` digests. -/
  cap : ℕ
  deriving Repr

namespace Level
/-- Rows of the committed matrix: `2^ℓ`. -/
def rows (l : Level) : ℕ := 2 ^ l.ell
/-- Positions per squeeze answer: `⌊256 / log₂ n⌋`. -/
def per (l : Level) : ℕ := 256 / l.logN
/-- Squeezes for the positions: `⌈t / per⌉`. -/
def sq (l : Level) : ℕ := (l.t + l.per - 1) / l.per
/-- Merkle-node queries per position (siblings): `log₂ n − cap`. -/
def sib (l : Level) : ℕ := l.logN - l.cap
end Level

/-- The `m = 32` ladder (rates `1/2 … 1/32`). -/
def ladder32 : List Level :=
  [⟨6, 20, 290, 9⟩, ⟨4, 18, 178, 8⟩, ⟨4, 16, 145, 8⟩, ⟨4, 14, 132, 8⟩, ⟨4, 12, 126, 7⟩]

/-- The `m = 30` ladder. -/
def ladder30 : List Level :=
  [⟨6, 18, 290, 9⟩, ⟨4, 16, 178, 8⟩, ⟨4, 14, 145, 8⟩, ⟨4, 12, 132, 8⟩, ⟨4, 10, 126, 7⟩]

/-- A kind's ladder. -/
def ladder : Kind → List Level
  | .L32 => ladder32 | _ => ladder30

/-- Level `i` of a kind's ladder. -/
def lvl (k : Kind) (i : ℕ) : Level := (ladder k).getD i ⟨0, 1, 0, 0⟩

/-- The level of the item sequence (`m* = 32`). -/
def lvlStar (i : ℕ) : Level := lvl .L32 i

/-- Levels. -/
def nLevels : ℕ := 5

/-- The final message: the level-4 fold, `2^7` K elements (`P30`: `2^5` then zeros; P1-D7). -/
def finalElems : ℕ := 2 ^ 7

/-- The final message's real K elements per kind. -/
def finalReal : Kind → ℕ
  | .L32 => 2 ^ 7 | _ => 2 ^ 5

theorem ladder_sq : (ladder32.map Level.sq, ladder30.map Level.sq) =
    ([25, 13, 10, 8, 6], [21, 12, 9, 7, 6]) := by decide
theorem ladder_sib : (ladder32.map Level.sib, ladder30.map Level.sib) =
    ([11, 10, 8, 6, 5], [9, 8, 6, 4, 3]) := by decide

/-! ## The proof's fields (A.3; sizes computed in `FRFormat`) -/

/-- A.3 row numbers (revision 3.1). -/
def fHdr : ℕ := 0
def fStmt : ℕ := 1
def fZ2 : ℕ := 2
def fZ3 : ℕ := 3
def fZend : ℕ := 4
def fL2 : ℕ := 5
def fS2 : ℕ := 6
def fLr : ℕ := 7
/-- A.3 row 7′ (revision 3.7): Lr end, `â_L ‖ b̂_L ‖ ĉ_L`. -/
def fLrEnd : ℕ := 8
def fRS0 : ℕ := 9
def fE : ℕ := 10
/-- A.3 row 9′ (revision 3.7): E end, `â_M ‖ b̂_M ‖ ĉ_M`. -/
def fEEnd : ℕ := 11
def fP1 : ℕ := 12
def fPf : ℕ := 13
def fCaps : ℕ := 14
def fFinal : ℕ := 15
def fCols : ℕ := 16
def fSibs : ℕ := 17
/-- Number of fields. -/
def nFields : ℕ := 18

/-! ## The phase table (A.4): the one place the counts live -/

/-- What a phase's squeezes yield. -/
inductive Chal where
  /-- F coordinates, two per answer (bytes `0…15`, `16…31`); `n κ` of them are real for kind `κ`. -/
  | coords (n : Kind → ℕ)
  /-- One F challenge (bytes `0…15`), real for the kinds where `act` holds. -/
  | one (act : Kind → Bool)
  /-- The positions of level `i` (`idxOf`). -/
  | pos (i : ℕ)

/-- A phase's items. -/
inductive Shape where
  /-- The seed query `"FRSEED0" ‖ vk ‖ c ‖ hdr`. -/
  | seed
  /-- One absorb of `len` bytes of field `fld` (stmt, caps, `s_v`, the final message). -/
  | absorb (fld len : ℕ)
  /-- `n` squeezes. -/
  | squeezes (n : ℕ) (ch : Chal)
  /-- A univariate round: absorb 2,048 bytes of field `fld`, squeeze `λ`. -/
  | uni (fld : ℕ)
  /-- `n` sumcheck rounds `(absorb, squeeze)` of degree `deg` (`inK`: K coefficients, 96 bytes;
  else F, 48 bytes) from field `fld`; the first `real κ` are real, the rest dummies (zero). -/
  | rounds (fld n deg : ℕ) (inK : Bool) (real : Kind → ℕ)
  /-- The queries of level `i`: per position, the column then the Merkle-node queries. -/
  | queries (i : ℕ)

/-- A phase: a name (A.4's) and a shape. -/
structure Phase where
  name : String
  shape : Shape

/-- `m* − d` for kind `κ`: the count for `m = κ.m`. -/
def mm (d : ℕ) (k : Kind) : ℕ := k.m - d

/-- Real only for nodes. -/
def nodeOnly (n : ℕ) (k : Kind) : ℕ := if k.isNode then n else 0

/-- The Fiat–Shamir phases before the PCS (A.4 rows 0–21, revision 3.4: L3 added, E4 removed). -/
def piopPhases : List Phase :=
  [⟨"seed", .seed⟩, ⟨"stmt", .absorb fStmt 128⟩, ⟨"cap0", .absorb fCaps (2 ^ 9 * 32)⟩,
   ⟨"Z1", .squeezes 10 (.coords (mm 13))⟩, ⟨"Z2", .uni fZ2⟩,
   ⟨"Z3", .rounds fZ3 26 3 false (mm 6)⟩, ⟨"Zend", .absorb fZend 32⟩,
   ⟨"L1", .squeezes 1 (.one fun _ => true)⟩, ⟨"L2", .rounds fL2 14 2 false fun _ => 14⟩,
   ⟨"L3", .absorb fL2 (8 * 16)⟩, ⟨"L3β", .squeezes 1 (.one fun _ => true)⟩,
   ⟨"S1", .squeezes 15 (.coords fun _ => 29)⟩, ⟨"S2", .rounds fS2 28 2 false (mm 4)⟩,
   ⟨"Lr1", .squeezes 8 (.coords (nodeOnly 15))⟩, ⟨"Lr2", .rounds fLr 15 3 false (nodeOnly 15)⟩,
   ⟨"Lrend", .absorb fLrEnd 48⟩,
   ⟨"Lr3", .squeezes 1 (.one Kind.isNode)⟩, ⟨"Lr4", .rounds fLr 15 2 false (nodeOnly 15)⟩,
   ⟨"RS0", .absorb fRS0 (4 * 128 * 16)⟩, ⟨"RS1", .squeezes 4 (.coords fun _ => 8)⟩,
   ⟨"E1", .squeezes 11 (.coords (nodeOnly 21))⟩, ⟨"E2", .rounds fE 21 3 false (nodeOnly 21)⟩,
   ⟨"Eend", .absorb fEEnd 48⟩,
   ⟨"E3", .squeezes 1 (.one Kind.isNode)⟩,
   ⟨"B'", .squeezes 1 (.one fun _ => true)⟩]

/-- The bytes absorbed after level `i`'s fold rounds: `cap_{i+1}`, or the final message. -/
def capBytes (i : ℕ) : ℕ := if i + 1 < nLevels then 2 ^ (lvlStar (i + 1)).cap * 32 else finalElems * 32

/-- The field of what level `i` absorbs after its fold rounds. -/
def capField (i : ℕ) : ℕ := if i + 1 < nLevels then fCaps else fFinal

/-- The five phases of level `i` (A.4 rows `22 + 5i … 26 + 5i`). -/
def levelPhases (i : ℕ) : List Phase :=
  [⟨"P1", .rounds fP1 (lvlStar i).ell 2 true fun k => (lvl k i).ell⟩,
   ⟨"C", .absorb (capField i) (capBytes i)⟩,
   ⟨"P2", .squeezes (lvlStar i).sq (.pos i)⟩,
   ⟨"Q", .queries i⟩,
   ⟨"P3", .squeezes 5 (.coords fun _ => 9)⟩]

/-- The final rounds `Pf` (A.4 row 47): `log₂ finalElems` K rounds. -/
def finalPhase : Phase := ⟨"Pf", .rounds fPf 7 2 true fun _ => 7⟩

/-- **The phase table** (A.4). -/
def phases : List Phase := piopPhases ++ (List.range nLevels).flatMap levelPhases ++ [finalPhase]

/-! ## Items -/

/-- One query of the item sequence, by shape. -/
inductive Item where
  | seed
  /-- An absorb of a message of `len` bytes. -/
  | absorb (len : ℕ)
  | squeeze
  /-- The column query of level `i`. -/
  | col (i : ℕ)
  /-- The Merkle-node query of level `i` at depth `h` (leaf level `0`). -/
  | node (i h : ℕ)
  deriving DecidableEq, Repr

/-- The bytes of a sumcheck round's message. -/
def roundBytes (inK : Bool) : ℕ := if inK then 96 else 48

/-- A univariate round's message: 127 F values padded to 2,048 bytes. -/
def uniBytes : ℕ := 2048

/-- The queries of one position of level `i`: the column, then `sib` Merkle-node queries. -/
def posItems (i : ℕ) : List Item := .col i :: (List.range (lvlStar i).sib).map (.node i)

/-- A phase's items. -/
def Shape.items : Shape → List Item
  | .seed => [.seed]
  | .absorb _ len => [.absorb len]
  | .squeezes n _ => List.replicate n .squeeze
  | .uni _ => [.absorb uniBytes, .squeeze]
  | .rounds _ n _ inK _ => (List.replicate n [.absorb (roundBytes inK), .squeeze]).flatten
  | .queries i => (List.replicate (lvlStar i).t (posItems i)).flatten

/-- **The item sequence** (A.4). -/
def items : List Item := phases.flatMap fun p => p.shape.items

/-- The Fiat–Shamir items (all but the column and Merkle-node queries). -/
def Item.isFS : Item → Bool
  | .col _ | .node _ _ => false
  | _ => true

/-- **`items_length`** (A.4; `qV = 10,240`). -/
theorem items_length : items.length = 8874 := by decide +kernel

theorem fsItems_length : (items.filter Item.isFS).length = 451 := by decide +kernel

/-! ## Tags and queries (A.2) -/

/-- `"FRSEED0"`. -/
def tagSeed : List UInt8 := [0x46, 0x52, 0x53, 0x45, 0x45, 0x44, 0x30]
/-- `"FRABS000"`. -/
def tagAbs : List UInt8 := [0x46, 0x52, 0x41, 0x42, 0x53, 0x30, 0x30, 0x30]
/-- `"FRSQZ000"`. -/
def tagSqz : List UInt8 := [0x46, 0x52, 0x53, 0x51, 0x5A, 0x30, 0x30, 0x30]
/-- `"FRMNOD" ‖ i ‖ 0`. -/
def tagNode (i : ℕ) : List UInt8 := [0x46, 0x52, 0x4D, 0x4E, 0x4F, 0x44, i.toUInt8, 0]
/-- `"FRMCOL" ‖ i ‖ 0`. -/
def tagCol (i : ℕ) : List UInt8 := [0x46, 0x52, 0x4D, 0x43, 0x4F, 0x4C, i.toUInt8, 0]

/-- The tag lists are pairwise distinct at the first byte where they differ (controls). -/
theorem tags_distinct : tagSeed ≠ tagAbs.take 7 ∧ tagAbs ≠ tagSqz ∧ tagAbs ≠ tagNode 0 ∧
    tagNode 0 ≠ tagCol 0 := by decide

/-- A byte list as a byte array. -/
def bytesOf (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- The seed query `"FRSEED0" ‖ vk ‖ c ‖ hdr`. -/
def seedQ (vk c : Digest) (hdr : ByteArray) : ByteArray :=
  bytesOf (tagSeed ++ vk.toList ++ c.toList) ++ hdr

/-- The absorb query `"FRABS000" ‖ st ‖ msg`. -/
def absorbQ (st : Digest) (msg : ByteArray) : ByteArray := bytesOf (tagAbs ++ st.toList) ++ msg

/-- The squeeze query `"FRSQZ000" ‖ st`. -/
def squeezeQ (st : Digest) : ByteArray := bytesOf (tagSqz ++ st.toList)

/-- The Merkle-node query of level `i`: `"FRMNOD" ‖ i ‖ 0 ‖ left ‖ right`. -/
def nodeQ (i : ℕ) (l r : Digest) : ByteArray := bytesOf (tagNode i ++ l.toList ++ r.toList)

/-- The column query of level `i`: `"FRMCOL" ‖ i ‖ 0 ‖ column`. -/
def colQ (i : ℕ) (col : ByteArray) : ByteArray := bytesOf (tagCol i) ++ col

/-- `n` bytes of `q` at `o` (zero past the end). -/
def bytesAt (q : ByteArray) (o n : ℕ) : Vector UInt8 n := Vector.ofFn fun i => q.data.getD (o + i) 0

/-! ### The Merkle encodings (`FRMerkle.MerkleEnc`, per level) -/

/-- Parse a Merkle-node query of level `i`: 72 bytes, the tag, the two children. -/
def parseNode (i : ℕ) (q : ByteArray) : Option (Digest × Digest) :=
  if q.data.toList.take 8 = tagNode i ∧ q.size = 72 then some (bytesAt q 8 32, bytesAt q 40 32)
  else none

/-- Parse a column query of level `i`: the tag (with the level byte), then the column's bytes. The
width is **not** checked (S-0-m4): a wrong-width first preimage under a cap entry is a collision,
charged by `Bad`; `FRMerkle.MerkleEnc`'s "and check its width" is therefore not required. -/
def parseCol (i : ℕ) (q : ByteArray) : Option ByteArray :=
  if q.data.toList.take 8 = tagCol i then some (q.extract 8 q.size) else none

/-- The 32-byte windows of a query at offsets `o₀ + 16k`. -/
def windowsFrom (o₀ : ℕ) (q : ByteArray) : List Digest :=
  (List.range ((q.size - o₀) / 16)).filterMap fun k =>
    if o₀ + 16 * k + 32 ≤ q.size then some (bytesAt q (o₀ + 16 * k) 32) else none

/-- The windows of a non-seed query: offsets `8 + 16k`, which are the 16-aligned stream offsets
(`streamOff_aligned`: the item starts at `≡ 0`, its `enc64 |q|` takes 8 bytes). -/
def windows (q : ByteArray) : List Digest := windowsFrom 8 q

/-- `"FRMNOD"`, the node tag without the level byte. -/
def tagNode6 : List UInt8 := [0x46, 0x52, 0x4D, 0x4E, 0x4F, 0x44]

/-- **The digests a query carries** (`FRMerkle.MerkleEnc.carried`, revision 3.3): a node query its
two children, an absorb its state and the 32-byte elements of its message (a cap's entries), a
seed `vk` and `c`, a squeeze its state; nothing else. -/
def carried (q : ByteArray) : List Digest :=
  let t := q.data.toList
  if t.take 8 = tagAbs then
    bytesAt q 8 32 :: (List.range ((q.size - 40) / 32)).map fun k => bytesAt q (40 + 32 * k) 32
  else if t.take 8 = tagSqz then [bytesAt q 8 32]
  else if t.take 7 = tagSeed then [bytesAt q 7 32, bytesAt q 39 32]
  else if t.take 6 = tagNode6 then [bytesAt q 8 32, bytesAt q 40 32]
  else []

theorem nodeQ_data (i : ℕ) (l r : Digest) :
    (nodeQ i l r).data.toList = tagNode i ++ l.toList ++ r.toList := rfl

theorem tagNode_length (i : ℕ) : (tagNode i).length = 8 := rfl

theorem nodeQ_size (i : ℕ) (l r : Digest) : (nodeQ i l r).size = 72 := by
  rw [ByteArray.size, ← Array.length_toList, nodeQ_data]; simp [tagNode_length]

theorem getElem_bytesAt (q : ByteArray) (o n k : ℕ) (hk : k < n) :
    (bytesAt q o n)[k] = q.data.toList.getD (o + k) 0 := by
  rw [bytesAt, Vector.getElem_ofFn, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

theorem bytesAt_nodeQ_l (i : ℕ) (l r : Digest) : bytesAt (nodeQ i l r) 8 32 = l := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, nodeQ_data, List.append_assoc,
    List.getD_append_right _ _ _ _ (by rw [tagNode_length]; omega), tagNode_length,
    Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by simpa using hk)]
  simp [List.getD_eq_getElem?_getD, hk]

theorem bytesAt_nodeQ_r (i : ℕ) (l r : Digest) : bytesAt (nodeQ i l r) 40 32 = r := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, nodeQ_data,
    List.getD_append_right _ _ _ _ (by simp [tagNode_length])]
  simp [tagNode_length, List.getD_eq_getElem?_getD, hk, show 40 + k - (8 + 32) = k by omega]

/-- A 72-byte query is its first 8 bytes and its two 32-byte halves. -/
theorem split72 (q : ByteArray) (hs : q.size = 72) :
    q.data.toList = q.data.toList.take 8 ++ (bytesAt q 8 32).toList ++ (bytesAt q 40 32).toList := by
  have hl : q.data.toList.length = 72 := by rw [Array.length_toList]; exact hs
  have ht : (q.data.toList.take 8).length = 8 := by rw [List.length_take, hl]; rfl
  refine List.ext_getElem (by rw [List.length_append, List.length_append, ht, hl]; simp)
    fun k h₁ h₂ => ?_
  by_cases k8 : k < 8
  · rw [List.getElem_append_left (by rw [List.length_append, ht]; omega),
      List.getElem_append_left (by rw [ht]; omega), List.getElem_take]
  · by_cases k40 : k < 40
    · rw [List.getElem_append_left (by rw [List.length_append, ht]; simp; omega),
        List.getElem_append_right (by rw [ht]; omega), Vector.getElem_toList, getElem_bytesAt,
        List.getD_eq_getElem _ _ (by omega)]
      congr 1; rw [ht]; omega
    · rw [List.getElem_append_right (by rw [List.length_append, ht]; simp; omega)]
      simp only [List.length_append, ht, Vector.length_toList]
      rw [Vector.getElem_toList, getElem_bytesAt, List.getD_eq_getElem _ _ (by omega)]
      congr 1; omega

theorem parseNode_nodeQ (i : ℕ) (l r : Digest) : parseNode i (nodeQ i l r) = some (l, r) := by
  have ht : (nodeQ i l r).data.toList.take 8 = tagNode i := by
    rw [nodeQ_data, List.append_assoc, List.take_left' (tagNode_length i)]
  simp only [parseNode, ht, nodeQ_size, and_self, ite_true, bytesAt_nodeQ_l, bytesAt_nodeQ_r]

theorem nodeQ_of_parseNode (i : ℕ) (q : ByteArray) (l r : Digest) (h : parseNode i q = some (l, r)) :
    q = nodeQ i l r := by
  unfold parseNode at h
  split_ifs at h with hq
  obtain ⟨ht, hs⟩ := hq
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  apply ByteArray.ext; apply Array.ext'
  rw [nodeQ_data, ← ht]; exact split72 q hs

theorem parseCol_colQ (i : ℕ) (c : ByteArray) : parseCol i (colQ i c) = some c := by
  have hd : (colQ i c).data.toList = tagCol i ++ c.data.toList := by
    simp [colQ, bytesOf, ByteArray.data_append]
  have h8 : (tagCol i).length = 8 := rfl
  have hs : (colQ i c).size = 8 + c.data.toList.length := by
    rw [ByteArray.size, ← Array.length_toList, hd, List.length_append, h8]
  rw [parseCol, if_pos (by rw [hd, List.take_left' h8] : (colQ i c).data.toList.take 8 = tagCol i)]
  congr 1
  apply ByteArray.ext; apply Array.ext'
  rw [ByteArray.data_extract, Array.toList_extract, List.extract, hd, List.drop_left' h8, hs,
    Nat.add_sub_cancel_left]
  exact List.take_of_length_le (le_refl _)

theorem carried_nodeQ (i : ℕ) (l r : Digest) :
    l ∈ carried (nodeQ i l r) ∧ r ∈ carried (nodeQ i l r) := by
  have h8 : (nodeQ i l r).data.toList.take 8 = tagNode i := by
    rw [nodeQ_data, List.append_assoc, List.take_left' (tagNode_length i)]
  have h7 : (nodeQ i l r).data.toList.take 7 = (tagNode i).take 7 := by
    rw [← h8, List.take_take]; rfl
  have h6 : (nodeQ i l r).data.toList.take 6 = tagNode6 := by
    rw [show (6 : ℕ) = min 6 8 from rfl, ← List.take_take, h8]; rfl
  have hc : carried (nodeQ i l r) = [l, r] := by
    simp only [carried, h8, h7, h6, bytesAt_nodeQ_l, bytesAt_nodeQ_r]
    simp [tagNode, tagAbs, tagSqz, tagSeed]
  simp [hc]

theorem absorbQ_data (st : Digest) (msg : ByteArray) :
    (absorbQ st msg).data.toList = tagAbs ++ st.toList ++ msg.data.toList := by
  simp [absorbQ, bytesOf, ByteArray.data_append]

theorem absorbQ_size (st : Digest) (msg : ByteArray) : (absorbQ st msg).size = 40 + msg.size := by
  rw [ByteArray.size, ← Array.length_toList, absorbQ_data, List.length_append, List.length_append,
    Vector.length_toList, Array.length_toList]; rfl

/-- **`carried_absorb`** (S-D-M1): an absorb query carries its state and every 32-byte element of
its message (a cap's entries). -/
theorem carried_absorb (st : Digest) (msg : ByteArray) (k : ℕ) (hk : 32 * (k + 1) ≤ msg.size) :
    st ∈ carried (absorbQ st msg) ∧ bytesAt msg (32 * k) 32 ∈ carried (absorbQ st msg) := by
  have hs := absorbQ_size st msg
  have h8 : (tagAbs ++ st.toList).length = 40 := by rw [List.length_append, Vector.length_toList]; rfl
  have ht : (absorbQ st msg).data.toList.take 8 = tagAbs := by
    rw [absorbQ_data, List.append_assoc, List.take_left' (show tagAbs.length = 8 from rfl)]
  have hst : bytesAt (absorbQ st msg) 8 32 = st := by
    ext j hj
    rw [getElem_bytesAt _ _ _ _ hj, absorbQ_data, List.append_assoc,
      List.getD_append_right _ _ _ _ (by rw [show tagAbs.length = 8 from rfl]; omega),
      show tagAbs.length = 8 from rfl, Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ (by simpa using hj)]
    simp [List.getD_eq_getElem?_getD, hj]
  simp only [carried, ht, ite_true, hst, List.mem_cons, true_or, List.mem_map, List.mem_range,
    true_and]
  refine Or.inr ⟨k, by rw [hs]; omega, ?_⟩
  ext j hj
  rw [getElem_bytesAt _ _ _ _ hj, getElem_bytesAt _ _ _ _ hj, absorbQ_data,
    List.getD_append_right _ _ _ _ (by rw [h8]; omega), h8]
  rw [show 40 + 32 * k + j - 40 = 32 * k + j by omega]

/-- **The in-play windows of a log** (S-D-M1; revision 3.5, S-0-m1: by **stream offset**, `≡ 0 mod 16`
in `0x54 ‖ traceBytes`): the first entry is the seed (stream offset 1, its query at 9), so its
windows are at query offsets `7 + 16k` (`vk`, `c`, `hdr`); every later query's at `8 + 16k`; and
every answer. -/
def inPlay : Trace → List Digest
  | [] => []
  | e :: L => windowsFrom 7 e.1 ++ [e.2] ++ L.flatMap fun e => windows e.1 ++ [e.2]

/-- **The protocol's `MerkleEnc`** of level `i` (S-D's fix pass; `FRMerkle`). -/
def frEnc (i : ℕ) : Merkle.MerkleEnc where
  nodeQ := nodeQ i
  colQ := colQ i
  parseNode := parseNode i
  parseCol := parseCol i
  carried := carried
  parseNode_nodeQ := parseNode_nodeQ i
  nodeQ_of_parseNode := nodeQ_of_parseNode i
  parseCol_colQ := parseCol_colQ i
  carried_nodeQ := carried_nodeQ i

/-- The query length of an item. -/
def Item.qlen : Item → ℕ
  | .seed => 7 + 32 + 32 + 48
  | .absorb len => 8 + 32 + len
  | .squeeze => 8 + 32
  | .col i => 8 + (lvlStar i).rows * 16
  | .node _ _ => 8 + 64

/-- The hashed stream `0x54 ‖ traceBytes tr` of a trace of the item sequence: `enc64 |q| ‖ q ‖ a`
per item. -/
def streamBytes : ℕ := 1 + (items.map fun it => 8 + it.qlen + 32).sum

theorem streamBytes_eq : streamBytes = 1437760 := by decide +kernel

/-- An item's bytes in the stream: `enc64 |q| ‖ q ‖ a`. -/
def Item.slen (it : Item) : ℕ := 8 + it.qlen + 32

/-- **Query sizes** (S-E1's `item_aligned`): the first query has `|q| = 119 ≡ 7 (mod 16)`, every
other query `|q| ≡ 8 (mod 16)`. -/
theorem qlen_mod : items.head? = some .seed ∧ Item.seed.qlen % 16 = 7 ∧
    ∀ it ∈ items.tail, it.qlen % 16 = 8 := by
  refine ⟨by decide +kernel, by decide, ?_⟩
  have : items.tail.all (fun it => it.qlen % 16 == 8) = true := by decide +kernel
  intro it h
  simpa using List.all_eq_true.1 this it h

/-- **Alignment** (BLUEPRINT §1.2, S-D's window question): the stream `0x54 ‖ …` starts with the
seed (`1 + 159 = 160` bytes) and every later item's length is a multiple of 16, so every later item
starts at a 16-aligned stream offset `s`; its 8-byte tag ends at `s + 16`, so its payload (query
offsets `8 + 16k`: a node query's children, an absorb's state and message, hence every cap entry)
and its answer (`s + 16 + |payload|`, `|payload| ≡ 0 mod 16`) are 16-aligned windows. -/
theorem items_aligned : items.head? = some .seed ∧ (1 + Item.seed.slen) % 16 = 0 ∧
    ∀ it ∈ items.tail, it.slen % 16 = 0 ∧ (it.qlen - 8) % 16 = 0 := by
  obtain ⟨h0, -, h⟩ := qlen_mod
  refine ⟨h0, by decide, fun it hit => ?_⟩
  have := h it hit
  simp only [Item.slen]; omega

/-- The stream offset of item `k`: `1 + Σ_{j<k} slen`. -/
def streamOff (k : ℕ) : ℕ := 1 + ((items.take k).map Item.slen).sum

theorem streamOff_aligned (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ items.length) : streamOff k % 16 = 0 := by
  obtain ⟨h0, h1, h2⟩ := items_aligned
  induction k, hk using Nat.le_induction with
  | base =>
    obtain ⟨x, xs, hx⟩ : ∃ x xs, items = x :: xs := List.exists_cons_of_ne_nil (by
      intro h; simp [h] at h0)
    rw [hx] at h0; simp only [List.head?_cons, Option.some.injEq] at h0
    simpa [streamOff, hx, h0] using h1
  | succ k hk ih =>
    have hlt : k < items.length := by omega
    have := ih (by omega)
    rw [streamOff, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      List.map_append, List.sum_append, ← Nat.add_assoc]
    have hmem : items[k] ∈ items.tail := by
      obtain ⟨x, xs, hx⟩ : ∃ x xs, items = x :: xs := List.exists_cons_of_ne_nil (by
        intro h; simp [h] at hlt)
      simp only [hx, List.tail_cons, List.getElem_cons, show k ≠ 0 by omega, ↓reduceDIte]
      exact List.getElem_mem _
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have := (h2 _ hmem).1
    unfold streamOff at *
    omega

/-- **The digest chain's length** (compressions per slot, §4.2): `⌈|B| / 64⌉`. -/
def chainLen : ℕ := (streamBytes + 63) / 64

theorem chainLen_eq : chainLen = 22465 := by rw [chainLen, streamBytes_eq]

/-! ## Challenge maps (A.2) -/

/-- Bytes `o … o + n − 1` of a digest (zero past the end). -/
def digestBytes (a : Digest) (o n : ℕ) : Vector UInt8 n := Vector.ofFn fun i => a.toArray.getD (o + i) 0

/-- **The F challenge** of an answer: coordinate `c` is bytes `16c … 16c + 15`. -/
def chF (a : Digest) (c : ℕ) : F := F.ofBytes (digestBytes a (16 * c) 16)

/-- **The K challenge** of an answer: all 32 bytes. -/
def chK (a : Digest) : K := K.ofBytes a

/-- The little-endian integer of an answer. -/
def natLE (a : Digest) : ℕ := ∑ i : Fin 32, a[i.1].toNat * 256 ^ i.1

/-- **Index `i` of `b` bits** of the answer `a`: bits `[i b, (i + 1) b)` of `natLE a`. -/
def idxOf (b : ℕ) (a : Digest) (i : ℕ) : ℕ := natLE a / 2 ^ (i * b) % 2 ^ b

/-- Position `p` of level `i` of kind `κ`: index `p mod per` of answer `p / per`. -/
def posOf (k : Kind) (i : ℕ) (ans : List Digest) (p : ℕ) : ℕ :=
  let l := lvl k i
  idxOf l.logN (ans.getD (p / l.per) 0) (p % l.per)

/-! ## Variable order and the `(0,0)`-row sets (normative) -/

/-- **Variable order** (S-D-m4). An index `x < 2^ℓ` is read little-endian: coordinate `v` is bit `v`
of `x`, so `eq(r, x) = Π_v (x_v r_v + (1 − x_v)(1 − r_v))` (`FRVIR.eqTab`, `FRRS.eqBits`,
`FRMLE.eq` on `cube`); **sumcheck round `t` binds coordinate `t`** (bit `t`, low bits first), in
particular **fold round `t` of a level binds bit `t` of the row index**, and the Ligerito point and
`tensorW`'s operand `r` list the fold challenges in round order (`r[v]` ↔ bit `v`). The bridge
`FRRS.eqBits r ℓ x = FRMLE.eq (r ∘ ·) (cube x)` is the identity; the lemma `eqBits_eq_eq` lives
with its consumer (S-0-m6, moved out so `FRRS` leaves the serial path; text in S-0-RESULT). -/
def bitOrderLE : Bool := true

/-- **The evaluation domain's size bound** `n ≤ 2^20` (S-D-m2): `D[j]`, `j < 2^domBits`; the same
constant as `FRRS.logNMax` (not imported here, S-0-m6: `domBits = FRRS.logNMax` is `rfl` where both
are in scope). -/
def domBits : ℕ := 20

theorem ladder_logN_le : (ladder32 ++ ladder30).all (fun l => l.logN ≤ domBits) = true := by
  decide

/-- The block kinds of the circuits (A.6, revision 3.3, normative). -/
inductive BlockKind where
  /-- The leaf's chain blocks. -/
  | chain
  /-- Digest-chain blocks `1 … N−1`; key-leaf blocks `1 … 65`. -/
  | stream
  /-- Block 0 of each digest chain. -/
  | streamStart
  /-- The key leaf's last block (41-byte tail). -/
  | streamEnd41
  /-- `hashStmt` A (`leafStmt`, 41 bytes). -/
  | hashA
  /-- `hashStmt` B1; key-leaf block 0; path blocks 1. -/
  | hashB1
  /-- `hashStmt` B2; path blocks 2. -/
  | hashB2
  /-- WOTS chain steps (43 bytes). -/
  | w43
  /-- The non-hash blocks (M, L, `WM`, spares; revision 3.8/3.8.1): rows `(var k, var k)`, `E = 0`,
  nothing pinned (`Sel ≡ 1`). -/
  | free
  deriving DecidableEq, Repr

/-- The kinds, in A.6's order (`kindInd`'s array order). -/
def blockKinds : List BlockKind :=
  [.chain, .stream, .streamStart, .streamEnd41, .hashA, .hashB1, .hashB2, .w43, .free]

/-- **The pinned positions** (`(0,0)` rows) of a kind (A.6, normative), as bit intervals `[lo, hi]`;
a pinned position's value is its bit in the public target `E` (the `E` values are A.6's table,
`FRPubTarget`). The walk ops take row weights masked by these sets (`FRVIR.maskRows`). -/
def zeroRows : BlockKind → List (ℕ × ℕ)
  | .chain => [(0, 255), (512, 519), (776, 1023), (1024, 1152)]
  | .stream => [(1024, 1152)]
  | .streamStart => [(0, 255), (1024, 1152)]
  | .streamEnd41 => [(840, 1023), (1024, 1152)]
  | .hashA => [(0, 255), (512, 519), (840, 1023), (1024, 1152)]
  | .hashB1 => [(0, 255), (512, 519), (1024, 1152)]
  | .hashB2 => [(520, 1023), (1024, 1152)]
  | .w43 => [(0, 255), (512, 519), (584, 599), (856, 1023), (1024, 1152)]
  | .free => []

/-- Is row `x` a `(0,0)` row of the block kind? -/
def isZeroRow (bk : BlockKind) (x : ℕ) : Bool := (zeroRows bk).any fun p => p.1 ≤ x && x ≤ p.2

/-! ## Constants of the circuit and the claim (A.1, B-10) -/

/-- `N_M`, `N_L`: M and L rows. -/
def NM : ℕ := 2 ^ 21
def NL : ℕ := 2 ^ 15
/-- The verifier's query bound. -/
def qVBound : ℕ := 10240

theorem items_le_qV : items.length ≤ qVBound := by rw [items_length]; decide

end FR
