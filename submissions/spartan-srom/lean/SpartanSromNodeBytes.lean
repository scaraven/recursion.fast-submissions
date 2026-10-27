/-
# The plain node read at byte level (review F1-M2; new in the fix pass)

`V`'s node branch reads a node proof once per level of a recursive proof, and a plain-node chain
under the public `σ0` can nest about 100 levels within `proofCap` (review F1-M2). Through the
library's list-based `decodeF` and `encodeF` a level costs about 1 µs per byte, so such a chain
cost about a minute. This module reads a node at byte level, **validated**: `nodeFast π` parses
`π` with plain offsets (`parseNodeB`, no proof about it) and accepts the result only if its
byte-level encoding `encodeB` (proved equal to the library's `encode`, `encodeB_eq`) is `π`
byte for byte (`bytesEqB`) and it fits the output format. So `nodeFast_sound`: whatever
`nodeFast` returns is the canonical node `π` encodes (`decodeF π = some w`, `encodeF w = π`).
`V` tries it first and falls back to `decodeFront` when it returns `none`, so `V`'s semantics, and
every statement about it, are unchanged (`V_tag`); only the compiled cost of a level drops.
-/
import SpartanSromVerifierTop

namespace SpartanSrom
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode encodeF decodeF encodeF_eq
  decodeF_eq size_eq_length)

/-! ## The byte-level encoder -/

/-- The zero bytes that pad a byte string of length `l` to a multiple of 8. -/
def padLen (l : ℕ) : ℕ := (8 - l % 8) % 8

/-- A number as a word's 8 bytes (the output format's numbers). -/
def wordB (n : ℕ) : ByteArray := ⟨(wordBytes (toWord n)).toArray⟩

/-- A byte string in the output format: its length word, its bytes, zero padding to 8. -/
def bytesB (b : ByteArray) : ByteArray := wordB b.size ++ b ++ ⟨Array.replicate (padLen b.size) 0⟩

/-- A digest's 32 bytes. -/
def digB (d : Digest) : ByteArray := ⟨d.toArray⟩

/-- A trace in the output format: its length word, then each entry's query and answer. -/
def traceB (tr : Trace) : ByteArray :=
  tr.foldl (fun acc e => acc ++ bytesB e.1 ++ digB e.2) (wordB tr.length)

/-- A signature in the output format: its index word, then the chain values and the path. -/
def sigB (σ : Sig) : ByteArray := (σ.ots ++ σ.path).foldl (fun acc d => acc ++ digB d) (wordB σ.idx)

/-- A signed proof in the output format. -/
def signedB (p : Signed) : ByteArray := bytesB p.π ++ traceB p.tr ++ sigB p.σ

/-- **A witness's encoding, built at byte level** (`encodeB_eq`: the library's `encode`). -/
def encodeB : Wit → ByteArray
  | .leaf s n => wordB 0 ++ digB s ++ wordB n
  | .node c₁ c₂ p₁ p₂ => wordB 1 ++ digB c₁ ++ digB c₂ ++ signedB p₁ ++ signedB p₂

private theorem toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

theorem wordsBytes_cons (w : Word) (ws : List Word) :
    wordsBytes (w :: ws) = wordBytes w ++ wordsBytes ws := List.flatMap_cons

theorem wordsBytes_append (a b : List Word) : wordsBytes (a ++ b) = wordsBytes a ++ wordsBytes b :=
  List.flatMap_append

theorem wordsBytes_flatMap {α : Type} (l : List α) (g : α → List Word) :
    wordsBytes (l.flatMap g) = l.flatMap fun e => wordsBytes (g e) := List.flatMap_assoc

/-- Packed bytes unpack to the bytes and the zero padding. -/
theorem wordsBytes_packBytes (b : List UInt8) :
    wordsBytes (packBytes b) = b ++ List.replicate (padLen b.length) 0 := by
  rw [← packFast_eq]
  fun_induction packFast b with
  | case1 => rfl
  | case2 x xs ih =>
    rw [wordsBytes, List.flatMap_cons, ← wordsBytes, ih]
    by_cases h : 8 ≤ (x :: xs).length
    · rw [wordBytes_ofLE (by simp), List.length_take, Nat.min_eq_left h, Nat.sub_self,
        List.replicate_zero, List.append_nil, ← List.append_assoc, List.take_append_drop,
        List.length_drop]
      congr 2; unfold padLen; omega
    · rw [List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega),
        wordBytes_ofLE (by omega)]
      simp only [List.nil_append, List.length_nil, padLen]
      simp only [List.length_cons] at h ⊢
      rw [show (8 - 0 % 8) % 8 = 0 from rfl, List.replicate_zero, List.append_nil]
      congr 2; omega

theorem wordB_toList (n : ℕ) : (wordB n).data.toList = wordBytes (toWord n) := rfl

theorem digB_toList (d : Digest) : (digB d).data.toList = wordsBytes (packBytes d.toList) := by
  rw [wordsBytes_packBytes_digest]; rfl

theorem bytesB_toList (b : ByteArray) :
    (bytesB b).data.toList = wordsBytes (bytesWords b.data.toList) := by
  rw [bytesWords, wordsBytes_cons, wordsBytes_packBytes, bytesB, toList_append, toList_append,
    wordB_toList, ← size_eq_length]
  simp

theorem foldl_append_toList {α : Type} (f : α → ByteArray) :
    ∀ (l : List α) (a₀ : ByteArray), (l.foldl (fun acc e => acc ++ f e) a₀).data.toList =
      a₀.data.toList ++ l.flatMap fun e => (f e).data.toList
  | [], a₀ => by simp
  | e :: l, a₀ => by
    rw [List.foldl_cons, foldl_append_toList f l, toList_append, List.flatMap_cons,
      List.append_assoc]

theorem traceB_toList (tr : Trace) : (traceB tr).data.toList = wordsBytes (logWords tr) := by
  have := foldl_append_toList (fun e : ByteArray × Digest => bytesB e.1 ++ digB e.2) tr
    (wordB tr.length)
  simp only [← ByteArray.append_assoc] at this
  rw [traceB, this, logWords, wordsBytes_cons, wordB_toList, wordsBytes_flatMap]
  congr 1
  congr 1; funext e
  rw [toList_append, bytesB_toList, digB_toList, wordsBytes_append]

theorem sigB_toList (σ : Sig) : (sigB σ).data.toList = wordsBytes (sigWords σ) := by
  rw [sigB, foldl_append_toList, sigWords, List.cons_append, wordsBytes_cons, wordB_toList,
    wordsBytes_append, List.flatMap_append, wordsBytes_flatMap, wordsBytes_flatMap]
  congr 1
  congr 1 <;> (congr 1; funext d; rw [digB_toList])

theorem signedB_toList (p : Signed) : (signedB p).data.toList = wordsBytes (signedWords p) := by
  rw [signedB, toList_append, toList_append, bytesB_toList, traceB_toList, sigB_toList,
    signedWords, wordsBytes_append, wordsBytes_append]

/-- **The byte-level encoder is the library's `encode`.** -/
theorem encodeB_eq (w : Wit) : encodeB w = encode w := by
  refine ByteArray.ext_toList ?_
  rw [WitnessSending.encode_data]
  cases w with
  | leaf s n =>
    rw [encodeB, toList_append, toList_append, wordB_toList, digB_toList, wordB_toList, witWords,
      List.cons_append, wordsBytes_cons, wordsBytes_append]
    simp [wordsBytes]
  | node c₁ c₂ p₁ p₂ =>
    rw [encodeB, toList_append, toList_append, toList_append, toList_append, wordB_toList,
      digB_toList, digB_toList, signedB_toList, signedB_toList, witWords]
    simp only [List.cons_append, wordsBytes_cons, wordsBytes_append, List.append_assoc]

/-! ## Byte-array comparison in place -/

/-- Bytes `i, i + 1, …` of `a` and `b` agree, for `fuel` bytes. -/
def bytesEqFrom (a b : ByteArray) : ℕ → ℕ → Bool
  | _, 0 => true
  | i, fuel + 1 => byteAt a i == byteAt b i && bytesEqFrom a b (i + 1) fuel

/-- **Equal byte arrays**, compared in place: equal sizes and equal bytes. -/
def bytesEqB (a b : ByteArray) : Bool := a.size == b.size && bytesEqFrom a b 0 a.size

theorem bytesEqFrom_spec (a b : ByteArray) :
    ∀ (fuel i : ℕ), bytesEqFrom a b i fuel = true → ∀ j, i ≤ j → j < i + fuel →
      byteAt a j = byteAt b j
  | 0, _, _, j, h1, h2 => absurd h2 (by omega)
  | fuel + 1, i, h, j, h1, h2 => by
    simp only [bytesEqFrom, Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact bytesEqFrom_spec a b fuel (i + 1) h.2 j (by omega) (by omega)

theorem bytesEqB_eq {a b : ByteArray} (h : bytesEqB a b = true) : a = b := by
  simp only [bytesEqB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hs, hb⟩ := h
  refine ByteArray.ext_toList (List.ext_getElem (by rw [← size_eq_length, ← size_eq_length, hs])
    fun j h1 h2 => ?_)
  have := bytesEqFrom_spec a b _ 0 hb j (Nat.zero_le _) (by rw [size_eq_length]; omega)
  rw [byteAt_toList, byteAt_toList, List.getD_eq_getElem _ _ h1,
    List.getD_eq_getElem _ _ h2] at this
  exact this

/-! ## The unvalidated reader -/

/-- Reads `|b| ‖ b ‖ padding` at byte `o`: the byte string and the offset after it. -/
def readBytesB (π : Proof) (o : ℕ) : Option (ByteArray × ℕ) :=
  if o + 8 + u64From π o ≤ π.size then
    some (π.extract (o + 8) (o + 8 + u64From π o), o + 8 + u64From π o + padLen (u64From π o))
  else none

/-- Reads `m` trace entries from byte `o` (accumulated in reverse in `acc`). -/
def readEntriesB (π : Proof) : ℕ → ℕ → Trace → Option (Trace × ℕ)
  | 0, o, acc => some (acc.reverse, o)
  | m + 1, o, acc =>
    match readBytesB π o with
    | some (q, o') =>
      if o' + 32 ≤ π.size then readEntriesB π m (o' + 32) ((q, digestFrom π o') :: acc) else none
    | none => none

/-- Reads a signed proof at byte `o`: its proof, its trace, its signature; and the offset after
it. -/
def readSignedB (π : Proof) (o : ℕ) : Option (Signed × ℕ) :=
  match readBytesB π o with
  | some (pb, o₁) =>
    if o₁ + 8 ≤ π.size then
      match readEntriesB π (u64From π o₁) (o₁ + 8) [] with
      | some (tr, o₂) =>
        if o₂ + 8 + 32 * (wotsLen + sigHeight) ≤ π.size then
          some (⟨pb, tr, ⟨u64From π o₂,
            (List.range wotsLen).map fun i => digestFrom π (o₂ + 8 + 32 * i),
            (List.range sigHeight).map fun i => digestFrom π (o₂ + 8 + 32 * (wotsLen + i))⟩⟩,
            o₂ + 8 + 32 * (wotsLen + sigHeight))
        else none
      | none => none
    else none
  | none => none

/-- **The node a proof's bytes spell**, read by offsets (unvalidated): tag word `1`, two
digests, two signed proofs, ending at the proof's end. -/
def parseNodeB (π : Proof) : Option Wit :=
  if 72 ≤ π.size ∧ u64From π 0 = 1 then
    match readSignedB π 72 with
    | some (p₁, o) =>
      match readSignedB π o with
      | some (p₂, o') =>
        if o' = π.size then some (.node (digestFrom π 8) (digestFrom π 40) p₁ p₂) else none
      | none => none
    | none => none
  else none

/-! ## Validation -/

/-- A signed proof fits the output format (`Signed.Fits`), decided. -/
def signedFitsB (p : Signed) : Bool :=
  decide (p.π.size < 2 ^ 64) && decide (p.tr.length < 2 ^ 64) &&
    decide (∀ e ∈ p.tr, e.1.size < 2 ^ 64) && decide (p.σ.idx < 2 ^ 64) &&
    decide (p.σ.ots.length = wotsLen) && decide (p.σ.path.length = sigHeight)

theorem signedFitsB_fits {p : Signed} (h : signedFitsB p = true) : p.Fits := by
  simp only [signedFitsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **The plain node `π` is, read at byte level and validated**: the reader's node, if it fits
the format and its encoding is `π` byte for byte. -/
def nodeFast (π : Proof) : Option Wit :=
  match parseNodeB π with
  | some (.node c₁ c₂ p₁ p₂) =>
    if signedFitsB p₁ && signedFitsB p₂ && bytesEqB (encodeB (.node c₁ c₂ p₁ p₂)) π then
      some (.node c₁ c₂ p₁ p₂)
    else none
  | _ => none

/-- **What `nodeFast` returns is the canonical node `π` encodes.** -/
theorem nodeFast_sound {π : Proof} {w : Wit} (h : nodeFast π = some w) :
    ∃ c₁ c₂ p₁ p₂, w = .node c₁ c₂ p₁ p₂ ∧ decodeF π = some w ∧ encodeF w = π := by
  unfold nodeFast at h
  split at h
  · rename_i c₁ c₂ p₁ p₂ _
    split_ifs at h with hv
    simp only [Bool.and_eq_true] at hv
    obtain ⟨⟨f₁, f₂⟩, he⟩ := hv
    cases h
    have hπ : encode (.node c₁ c₂ p₁ p₂) = π := by rw [← encodeB_eq]; exact bytesEqB_eq he
    refine ⟨c₁, c₂, p₁, p₂, rfl, ?_, by rw [encodeF_eq, hπ]⟩
    rw [decodeF_eq, ← hπ,
      decode_encode (.node c₁ c₂ p₁ p₂) ⟨signedFitsB_fits f₁, signedFitsB_fits f₂⟩]
  · cases h

/-- The children of a node `nodeFast` reads are shorter than it. -/
theorem nodeFast_child_lt {π : Proof} {c₁ c₂ : Digest} {p₁ p₂ : Signed}
    (h : nodeFast π = some (.node c₁ c₂ p₁ p₂)) : p₁.π.size < π.size ∧ p₂.π.size < π.size := by
  obtain ⟨_, _, _, _, hw, -, he⟩ := nodeFast_sound h
  cases hw
  rw [← he, encodeF_eq]
  exact WitnessSending.size_child_lt _ _ _ _

end SpartanSrom
