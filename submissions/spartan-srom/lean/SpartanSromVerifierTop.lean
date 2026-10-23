-- Ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to the v4 contract.
/-
# The leaf branch of `V` (BLUEPRINT §1.1, §2 branch `L`; v3 BLUEPRINT-R1 §1.1–§1.3)

This module is the part of the verifier that does not depend on the SNARK and is not the node
side. The leaf verifier is a parameter (`LeafVerifier`): the exact leaf size `leafSize n` (§7),
the SNARK verifier `prog s n h π_S` (a query program, §1.3 step 3) and, new in v4, its per-leaf
query bound `qb n`, which the bundle branch sums before any query. `Verifier.lean` instantiates
them. v3's node branch, `check` and `vb` (the verifier instantiated with v3's contract oracle)
are gone: v4's verifier (`SpartanSromNode`) takes the public key and has the branches `L`, `C`,
`N`, `B`.

* **Format (§1.1).** Word 0 of a proof (bytes 0–7) is the tag: `0` a leaf, `1` a node. A SNARK
  leaf proof (`L`) is `enc64 0 ‖ s ‖ enc64 n ‖ h ‖ π_S`, of exactly `leafSize n` bytes. Its first
  48 bytes are `encode (.leaf s n)`, so the library's `decode` reads it as `.leaf s n`
  (`decode_leaf`, re-proved for v4's strict `decodeWit`), and the library's extractor program and
  `computes` apply unchanged.
* **The leaf branch** is `leafProg` (§1.3, unchanged from v3). It parses the header and checks,
  with no oracle query: `n ≤ chainCap`, `π.size = leafSize n` and `c = leafStmt h n`. Then it
  accepts iff `h = s` when `n = 0`, and otherwise runs the SNARK verifier.

Proved here, for every `LeafVerifier`: the header lemmas, the extractor's view of a leaf
(`decode_leaf`), statement binding of the leaf branch (`leafProg_stmt`), the byte facts of the
canaries (`parse48_congr`, `take_push`, `take_dropLast`), the leaf branch's queries
(`leafProg_queries`) and what an accepted leaf branch gives `final` (`leafProg_final`).
-/
import SpartanSromDecode
import SpartanSromOracle

namespace SpartanSrom
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode size_encode size_eq_length)

/-! ## The leaf verifier, as a parameter -/

/-- The SNARK side of a leaf (§1.3 step 3, §7), supplied by `Verifier.lean`. -/
structure LeafVerifier where
  /-- `leafSize n`: the exact byte length of a leaf proof of a chain of `n` steps. -/
  size : ℕ → ℕ
  /-- A leaf proof holds at least its 80-byte header. -/
  size_ge : ∀ n, 80 ≤ size n
  /-- The SNARK verifier on `π_S` with public input `(s, n, h)`, run when `n ≥ 1`. -/
  prog : (s : Digest) → (n : ℕ) → (h : Digest) → (snark : ByteArray) → OProg Bool
  /-- The bound on the SNARK verifier's queries for a chain of `n` steps (v4: the bundle branch
  sums it before any query). -/
  qb : ℕ → ℕ

variable (LV : LeafVerifier)

/-! ## Parsing (§1.1) -/

/-- Byte `j` of a proof, `0` past its end. (v4: read in place; v3's `digestFrom` read
`π.data.getD`, and compiled code materialises `π.data` as a copy of the whole proof on every
access, 32 per digest.) -/
def byteAt (π : Proof) (j : ℕ) : UInt8 := if h : j < π.size then π[j] else 0

/-- Word 0 of a proof, bytes 0–7 little-endian: the tag. -/
def tagWord (π : Proof) : ℕ := ofLE (π.data.extract 0 8).toList

/-- The 32 bytes of `π` from byte `k` on, as a digest (`0` past the end). -/
def digestFrom (π : Proof) (k : ℕ) : Digest :=
  Vector.ofFn fun i : Fin 32 => byteAt π (k + i.val)

/-- The chain start of a leaf proof, bytes 8–39. -/
def leafS (π : Proof) : Digest := digestFrom π 8

/-- The chain length of a leaf proof, bytes 40–47 little-endian. -/
def leafN (π : Proof) : ℕ := ofLE (π.data.extract 40 48).toList

/-- The claimed chain end of a leaf proof, bytes 48–79. -/
def leafH (π : Proof) : Digest := digestFrom π 48

/-- The SNARK of a leaf proof, bytes 80 to the end. -/
def leafSnark (π : Proof) : ByteArray := π.extract 80 π.size

/-- The leaf header test (§1.3 step 1), no oracle: the length within `chainCap`, the exact size,
and the statement `leafStmt h n`. -/
def leafHeaderOK (c : Digest) (π : Proof) : Bool :=
  decide (leafN π ≤ chainCap) && decide (π.size = LV.size (leafN π)) &&
    decide (c = leafStmt (leafH π) (leafN π))

/-- **The leaf branch** (§1.3), the only query program. -/
def leafProg (c : Digest) (π : Proof) : OProg Bool :=
  if leafHeaderOK LV c π then
    if leafN π = 0 then .ret (decide (leafH π = leafS π))
    else LV.prog (leafS π) (leafN π) (leafH π) (leafSnark π)
  else .ret false


theorem take8_encode (w : Wit) : (encode w).data.toList.take 8 =
    wordBytes (toWord (match w with | .leaf .. => 0 | .node .. => 1)) := by
  rw [WitnessSending.encode_data]
  cases w <;> simp [witWords, wordsBytes, List.flatMap_cons, wordBytes]

theorem proof_extract_toList (π : Proof) (i j : ℕ) :
    (π.data.extract i j).toList = (π.data.toList.drop i).take (j - i) := by
  simp [Array.toList_extract, List.extract]

theorem tagWord_eq (π : Proof) : tagWord π = ofLE (π.data.toList.take 8) := by
  rw [tagWord, proof_extract_toList]; rfl


theorem tagWord_encode_node (c₁ c₂ : Digest) (p₁ p₂ : Signed) :
    tagWord (encode (.node c₁ c₂ p₁ p₂)) = 1 := by
  rw [tagWord_eq, take8_encode, ofLE_wordBytes]; rfl

theorem tagWord_encode_leaf (s : Digest) (n : ℕ) : tagWord (encode (.leaf s n)) = 0 := by
  rw [tagWord_eq, take8_encode, ofLE_wordBytes]; rfl

theorem size_encode_node (c₁ c₂ : Digest) (p₁ p₂ : Signed) :
    8 ≤ (encode (.node c₁ c₂ p₁ p₂)).size := by
  rw [size_encode]
  simp only [witWords, List.length_cons, List.length_append]
  omega

/-! ## Leaves: the header, the extractor's view, the zero-step leaf -/

theorem leafProg_header {c : Digest} {π : Proof} {L : Log} {b : Bool}
    (h : (leafProg LV c π).runLog L = some b) (hb : b = true) : leafHeaderOK LV c π = true := by
  subst hb
  by_contra hn
  rw [leafProg, ite_eq_right hn] at h
  cases h

theorem leafProg_header_run {c : Digest} {π : Proof} {H : ByteArray → Digest}
    (h : (leafProg LV c π).run H = true) : leafHeaderOK LV c π = true := by
  by_contra hn
  rw [leafProg, ite_eq_right hn] at h
  cases h

theorem leafHeaderOK_iff {c : Digest} {π : Proof} : leafHeaderOK LV c π = true ↔
    leafN π ≤ chainCap ∧ π.size = LV.size (leafN π) ∧ c = leafStmt (leafH π) (leafN π) := by
  simp [leafHeaderOK, and_assoc]

theorem proof_getD_eq (π : Proof) (i : ℕ) : π.data.getD i 0 = π.data.toList.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  unfold Array.getD
  split
  · rename_i h; rw [Array.getElem?_eq_getElem h]; rfl
  · simp_all

theorem byteAt_eq (π : Proof) (j : ℕ) : byteAt π j = π.data.getD j 0 := rfl

theorem wordsBytes_packBytes_digest (d : Digest) : wordsBytes (packBytes d.toList) = d.toList := by
  have h := unpack_packBytes d.toList
  rwa [List.take_of_length_le (by rw [wordsBytes_length, packBytes_length]; simp)] at h

/-- The first 48 bytes of a proof with tag word `0` are the encoding of the leaf witness its
header names. -/
theorem take48_leaf {π : Proof} (hs : 48 ≤ π.size) (ht : tagWord π = 0) :
    π.data.toList.take 48 = wordsBytes (witWords (.leaf (leafS π) (leafN π))) := by
  set l := π.data.toList with hl
  have hlen : l.length = π.size := (size_eq_length π).symm
  rw [tagWord_eq] at ht
  have hA : l.take 8 = wordBytes (toWord 0) := by
    rw [← wordBytes_ofLE8 (p := l.take 8) (by simp; omega), hl, ht]
  have hB : (l.drop 8).take 32 = (leafS π).toList := by
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [leafS, digestFrom, Vector.toList_ofFn, List.getElem_ofFn, byteAt_eq, proof_getD_eq,
      ← hl, List.getElem_take, List.getElem_drop]
    rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]
  have hC : (l.drop 40).take 8 = wordBytes (toWord (leafN π)) := by
    rw [leafN, proof_extract_toList, ← hl]
    exact (wordBytes_ofLE8 (by simp; omega)).symm
  have e1 : l.take 48 = l.take 8 ++ (l.drop 8).take 32 ++ (l.drop 40).take 8 := by
    rw [List.append_assoc, show (40 : ℕ) = 8 + 32 by rfl, ← List.drop_drop, ← List.take_add,
      ← List.take_add]
  rw [e1, hA, hB, hC]
  simp only [witWords, List.cons_append, wordsBytes, List.flatMap_cons, List.flatMap_append,
    List.flatMap_nil, List.append_nil]
  rw [← wordsBytes, wordsBytes_packBytes_digest, List.append_assoc]

/-- **The extractor's view of a leaf proof**: the library's `decode` reads the start and the
length of the header, whatever follows byte 48. -/
theorem decode_leaf {π : Proof} (hs : 48 ≤ π.size) (ht : tagWord π = 0) :
    decode π = some (.leaf (leafS π) (leafN π)) := by
  have hlen : π.data.toList.length = π.size := (size_eq_length π).symm
  have hfit : (Wit.leaf (leafS π) (leafN π)).Fits := by
    show leafN π < 2 ^ 64
    have h8 : (π.data.extract 40 48).toList.length ≤ 8 := by simp
    exact (ofLE_lt _).trans_le ((Nat.pow_le_pow_right (by norm_num) h8).trans (by norm_num))
  have hw : (wordsBytes (witWords (.leaf (leafS π) (leafN π)))).length = 8 * 6 := by
    rw [wordsBytes_length]; simp [witWords, packBytes_digest_length]
  rw [decode, ← List.take_append_drop 48 π.data.toList, take48_leaf hs ht,
    packBytes_append_mul8 6 _ _ hw, packBytes_wordsBytes]
  have := readWit_witWords _ hfit (packBytes (π.data.toList.drop 48))
  simp only [decodeWit, StateT.run', StateT.run] at this ⊢
  rw [this]; rfl

/-! ## Statement binding -/

/-- An accepted leaf proof binds the statement `leafStmt h n` of its header, for every oracle. -/
theorem leafProg_stmt {c : Digest} {π : Proof} {H : ByteArray → Digest}
    (h : (leafProg LV c π).run H = true) : c = leafStmt (leafH π) (leafN π) :=
  ((leafHeaderOK_iff LV).mp (leafProg_header_run LV h)).2.2

/-! ## The canaries (DESIGN-v3 §6.3 step 7): one byte appended, the last byte removed -/

/-- `π` without its last byte. -/
def dropLast (π : Proof) : Proof := ⟨π.data.pop⟩

private theorem take_drop_of_take {l l' : List UInt8} {m : ℕ} (h : l.take m = l'.take m)
    {k j : ℕ} (hkj : k + j ≤ m) : (l.drop k).take j = (l'.drop k).take j := by
  have e : ∀ x : List UInt8, (x.drop k).take j = ((x.take m).drop k).take j := fun x => by
    rw [List.drop_take, List.take_take]; congr 1; omega
  rw [e l, e l', h]

private theorem getD_of_take {l l' : List UInt8} {m : ℕ} (h : l.take m = l'.take m) {j : ℕ}
    (hj : j < m) : l.getD j 0 = l'.getD j 0 := by
  have e : ∀ x : List UInt8, x.getD j 0 = (x.take m).getD j 0 := fun x => by
    simp [List.getD_eq_getElem?_getD, hj]
  rw [e l, e l', h]

/-- The tag, the start and the length read only the first 48 bytes. -/
theorem parse48_congr {π π' : Proof} (h : π.data.toList.take 48 = π'.data.toList.take 48) :
    tagWord π = tagWord π' ∧ leafN π = leafN π' ∧ leafS π = leafS π' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tagWord_eq, tagWord_eq, ← List.drop_zero (l := π.data.toList),
      ← List.drop_zero (l := π'.data.toList), take_drop_of_take h (by omega : 0 + 8 ≤ 48)]
  · rw [leafN, leafN, proof_extract_toList, proof_extract_toList,
      take_drop_of_take h (by omega : 40 + 8 ≤ 48)]
  · ext i hi
    simp only [leafS, digestFrom, Vector.getElem_ofFn, byteAt_eq, proof_getD_eq]
    exact congrArg _ (getD_of_take h (by omega : 8 + i < 48))

/-- The parse reads only the first 80 bytes. -/
theorem parse_congr {π π' : Proof} (h : π.data.toList.take 80 = π'.data.toList.take 80) :
    tagWord π = tagWord π' ∧ leafN π = leafN π' ∧ leafS π = leafS π' ∧ leafH π = leafH π' := by
  have ht : ∀ k j, k + j ≤ 80 → (π.data.toList.drop k).take j = (π'.data.toList.drop k).take j :=
    fun _ _ hkj => take_drop_of_take h hkj
  have hg : ∀ j, j < 80 → π.data.getD j 0 = π'.data.getD j 0 := fun j hj => by
    rw [proof_getD_eq, proof_getD_eq]; exact getD_of_take h hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tagWord_eq, tagWord_eq, ← List.drop_zero (l := π.data.toList),
      ← List.drop_zero (l := π'.data.toList), ht 0 8 (by omega)]
  · rw [leafN, leafN, proof_extract_toList, proof_extract_toList, ht 40 8 (by omega)]
  · ext i hi
    simp only [leafS, digestFrom, Vector.getElem_ofFn, byteAt_eq]
    exact congrArg _ (hg (8 + i) (by omega))
  · ext i hi
    simp only [leafH, digestFrom, Vector.getElem_ofFn, byteAt_eq]
    exact congrArg _ (hg (48 + i) (by omega))

theorem take_push {π : Proof} {m : ℕ} (hs : m ≤ π.size) (b : UInt8) :
    (π.push b).data.toList.take m = π.data.toList.take m := by
  have : m ≤ π.data.toList.length := by rw [← size_eq_length]; exact hs
  simp [ByteArray.push, List.take_append_of_le_length this]

theorem take_dropLast {π : Proof} {m : ℕ} (hs : m + 1 ≤ π.size) :
    (dropLast π).data.toList.take m = π.data.toList.take m := by
  have : m + 1 ≤ π.data.toList.length := by rw [← size_eq_length]; exact hs
  rw [dropLast, Array.toList_pop, List.dropLast_eq_take, List.take_take]
  congr 1; omega

theorem size_dropLast (π : Proof) : (dropLast π).size = π.size - 1 := by
  show π.data.pop.size = π.data.size - 1
  exact Array.size_pop

/-! ## The leaf branch's queries, and what `final` gets from it -/

/-- On the leaf branch, the only queries are the SNARK verifier's. -/
theorem leafProg_queries (c : Digest) (π : Proof) (H : ByteArray → Digest) :
    (leafProg LV c π).queries H =
      if leafHeaderOK LV c π = true ∧ leafN π ≠ 0 then
        (LV.prog (leafS π) (leafN π) (leafH π) (leafSnark π)).queries H
      else [] := by
  unfold leafProg
  split_ifs <;> simp_all [OProg.queries]

/-- **An accepted leaf branch** (on any log) has a header that holds, decodes (for the extractor)
to its start and length, and either is the zero-step leaf with `h = s` or was accepted by the
SNARK verifier on the same log. -/
theorem leafProg_final {c : Digest} {π : Proof} {L : Log}
    (h : (leafProg LV c π).runLog L = some true) (ht : tagWord π = 0) :
    decode π = some (.leaf (leafS π) (leafN π)) ∧ leafN π ≤ chainCap ∧
      c = leafStmt (leafH π) (leafN π) ∧ (leafN π = 0 → leafH π = leafS π) ∧
      (leafN π ≠ 0 → (LV.prog (leafS π) (leafN π) (leafH π) (leafSnark π)).runLog L =
        some true) := by
  have hh := leafProg_header LV h rfl
  obtain ⟨hn, hsz, hc⟩ := (leafHeaderOK_iff LV).mp hh
  have hs : 48 ≤ π.size := by have := LV.size_ge (leafN π); omega
  refine ⟨decode_leaf hs ht, hn, hc, fun h0 => ?_, fun h0 => ?_⟩
  · rw [leafProg, ite_eq_left hh, ite_eq_left h0] at h
    exact of_decide_eq_true (Option.some.inj h)
  · rw [leafProg, ite_eq_left hh, ite_eq_right h0] at h
    exact h

/-! ## Controls (BLUEPRINT-R1 §10.1, the leaf header) -/

/-- The start of the control leaf: `01…01`. -/
abbrev ctlStart : Digest := Vector.replicate 32 1

/-- An 80-byte leaf proof of the zero-step chain from `01…01`: tag `0`, `s`, `n = 0`, `h = s`. -/
def zeroLeaf : Proof :=
  ⟨#[0, 0, 0, 0, 0, 0, 0, 0] ++ Array.replicate 32 1 ++ #[0, 0, 0, 0, 0, 0, 0, 0] ++
    Array.replicate 32 1⟩

theorem zeroLeaf_parse : zeroLeaf.size = 80 ∧ tagWord zeroLeaf = 0 ∧ leafN zeroLeaf = 0 ∧
    leafS zeroLeaf = ctlStart ∧ leafH zeroLeaf = ctlStart := by
  decide +kernel

/-- The statement of the control leaf. -/
abbrev ctlStmt : Digest := leafStmt ctlStart 0

end SpartanSrom
