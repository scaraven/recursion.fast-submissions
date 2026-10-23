-- Ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to the v4 contract.
/-
# The proof formats' byte facts (v4; BLUEPRINT §1)

v3's module of this name held a linear-time codec for v3's node format (two plain child proofs:
`packFast`, `decodeWitF`, the byte-level `nodeParse`), copied from `submissions/baseline`. v4's
node witness carries two **signed** children (proof, trace, signature), its output format is the
contract's new strict `decodeWit`, and the v4 library has the linear-time twins
(`WitnessSending.decodeF`, `encodeF`). What is left here are the byte facts the v4 formats need:

* `packBytes_append_mul8`: packing a prefix of a multiple of 8 bytes packs it separately; so
  `decode_append`: **the library's `decode` of `encode w ‖ T` is `w`** (`decodeWit` ignores the
  words after a witness), which is how a bundle (`B`, `encode W ‖ T`) decodes to its clear tree.
* `wordBytes_ofLE` (v3's, unchanged): the 8 bytes of the word of at most 8 bytes are those bytes,
  zero-padded.
* `IsStrictPrefix e π`: `e` is a strict prefix of `π`.
* `decodeFront π`: the library's `decodeF π` read from a prefix of `π` (16 KB, then four times
  longer while it does not decode), equal to it (`decodeFront_eq`) because the decoder's readers
  read the same from a longer word list (`decodeWit_append`). A bundle `encode W ‖ T` decodes
  without packing `T`.
* A decidable equality of signatures (`Sig` has none in the contract), for the bundle's "every
  slot carries the same signature" test.
-/
import RecursionFast.Library.WitnessSending

namespace SpartanSrom
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode size_encode size_eq_length)

/-! ## Packing -/

/-- Packing a prefix of `8 k` bytes packs it separately from the rest. -/
theorem packBytes_append_mul8 : ∀ (k : ℕ) (pre rest : List UInt8), pre.length = 8 * k →
    packBytes (pre ++ rest) = packBytes pre ++ packBytes rest
  | 0, pre, rest, h => by
    rw [List.length_eq_zero_iff.mp (show pre.length = 0 by simpa using h)]
    simp [packBytes]
  | k + 1, pre, rest, h => by
    have h8 : (pre.take 8).length = 8 := by simp [h]
    have hd : (pre.drop 8).length = 8 * k := by simp [h]; omega
    rw [← List.take_append_drop 8 pre, List.append_assoc, packBytes_append8 _ h8,
      packBytes_append8 _ h8, packBytes_append_mul8 k _ rest hd, List.cons_append]

theorem wordBytes_ofLE {p : List UInt8} (hp : p.length ≤ 8) :
    wordBytes (toWord (ofLE p)) = p ++ List.replicate (8 - p.length) 0 := by
  have hlt : ofLE p < 2 ^ 64 :=
    (ofLE_lt p).trans_le (by
      calc 256 ^ p.length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hp
        _ = 2 ^ 64 := by norm_num)
  apply List.ext_getElem
  · rw [wordBytes_length]; simp; omega
  intro i h1 h2
  simp only [wordBytes, enc64, List.getElem_ofFn, toNat_toWord hlt]
  rw [← toUInt8_mod, ofLE_div_mod]
  by_cases hi : i < p.length
  · rw [List.getElem_append_left hi, List.getD_eq_getElem _ _ hi]; simp
  · rw [List.getElem_append_right (by omega), List.getElem_replicate,
      List.getD_eq_default _ _ (by omega)]; rfl

/-- An 8-byte list is the bytes of its word. -/
theorem wordBytes_ofLE8 {p : List UInt8} (hp : p.length = 8) :
    wordBytes (toWord (ofLE p)) = p := by
  rw [wordBytes_ofLE hp.le, hp]; simp

/-- **A proof that starts with a witness's encoding decodes to the witness** (the words after a
witness are ignored by `decodeWit`). -/
theorem decode_of_take {w : Wit} (h : w.Fits) {π : Proof}
    (ht : π.data.toList.take (encode w).size = (encode w).data.toList) : decode π = some w := by
  have hl : (wordsBytes (witWords w)).length = 8 * (witWords w).length := wordsBytes_length _
  have hd : π.data.toList = wordsBytes (witWords w) ++ π.data.toList.drop (encode w).size := by
    rw [← WitnessSending.encode_data, ← ht, List.take_append_drop]
  rw [decode, hd, packBytes_append_mul8 _ _ _ hl, packBytes_wordsBytes]
  have := readWit_witWords w h (packBytes (π.data.toList.drop (encode w).size))
  simp only [decodeWit, StateT.run', StateT.run] at this ⊢
  rw [this]; rfl

/-- **A witness's encoding with bytes after it decodes to the witness.** -/
theorem decode_append (w : Wit) (h : w.Fits) (T : ByteArray) :
    decode (encode w ++ T) = some w := by
  refine decode_of_take h ?_
  rw [ByteArray.data_append, Array.toList_append, size_eq_length,
    List.take_left' rfl]

/-! ## Strict prefixes -/

/-- `e` is a strict prefix of `π`. -/
def IsStrictPrefix (e π : ByteArray) : Prop := e.size < π.size ∧ π.extract 0 e.size = e

/-- `IsStrictPrefix` is decided by a size comparison and one byte-array comparison. -/
instance (e π : ByteArray) : Decidable (IsStrictPrefix e π) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The bytes of `π.extract 0 k` are the first `k` bytes of `π`. -/
theorem extract_zero_toList (π : ByteArray) (k : ℕ) :
    (π.extract 0 k).data.toList = π.data.toList.take k := by
  simp [ByteArray.data_extract, Array.toList_extract, List.extract]

/-- **A proof that starts with a witness's encoding decodes to the witness**, by `extract`. -/
theorem decode_of_extract {w : Wit} (h : w.Fits) {π : Proof}
    (he : π.extract 0 (encode w).size = encode w) : decode π = some w :=
  decode_of_take h (by rw [← extract_zero_toList, he])

theorem isStrictPrefix_append {e T : ByteArray} (hT : 0 < T.size) :
    IsStrictPrefix e (e ++ T) := by
  refine ⟨by rw [ByteArray.size_append]; omega, ?_⟩
  exact ByteArray.extract_append_eq_left rfl

/-! ## Decoding from a prefix -/

/-- A reader that succeeds on `o` reads the same from `o ++ o₂` and leaves its rest followed by
`o₂`. -/
private def Stable {α : Type} (r : Reader α) : Prop :=
  ∀ o o₂ a rest, r.run o = some (a, rest) → r.run (o ++ o₂) = some (a, rest ++ o₂)

private theorem Stable.pure {α : Type} (a : α) : Stable (Pure.pure a : Reader α) := by
  intro o o₂ b rest h
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h ⊢
  obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

private theorem Stable.bind {α β : Type} {r : Reader α} {f : α → Reader β} (hr : Stable r)
    (hf : ∀ a, Stable (f a)) : Stable (r >>= f) := by
  intro o o₂ b rest h
  simp only [StateT.run_bind] at h ⊢
  cases h1 : r.run o with
  | none => rw [h1] at h; cases h
  | some p =>
    rw [h1] at h
    rw [hr o o₂ p.1 p.2 h1]
    exact hf p.1 p.2 o₂ b rest h

private theorem stable_readNat : Stable readNat := by
  intro o o₂ a rest h
  cases o with
  | nil => cases h
  | cons w o => cases h; rfl

private theorem stable_readBytes (n : ℕ) : Stable (readBytes n) := by
  intro o o₂ a rest h
  simp only [StateT.run, readBytes] at h ⊢
  split_ifs at h with hl
  cases h
  have hle : (n + 7) / 8 ≤ o.length := by rw [List.length_take] at hl; omega
  rw [List.take_append_of_le_length hle, ite_eq_left hl, List.drop_append_of_le_length hle]

private theorem stable_readList {α : Type} {r : Reader α} (hr : Stable r) :
    ∀ n, Stable (readList r n)
  | 0 => Stable.pure _
  | n + 1 => Stable.bind hr fun _ => Stable.bind (stable_readList hr n) fun _ => Stable.pure _

private theorem stable_readWit : Stable readWit := by
  have hs : Stable readString := Stable.bind stable_readNat fun _ =>
    Stable.bind (stable_readBytes _) fun _ => Stable.pure _
  have hd : Stable readDigest := Stable.bind (stable_readBytes _) fun _ => Stable.pure _
  have ht : Stable readTrace := Stable.bind stable_readNat fun _ => stable_readList
    (Stable.bind hs fun _ => Stable.bind hd fun _ => Stable.pure _) _
  have hp : Stable readSigned := Stable.bind hs fun _ => Stable.bind ht fun _ =>
    Stable.bind (Stable.bind stable_readNat fun _ => Stable.bind (stable_readList hd _) fun _ =>
      Stable.bind (stable_readList hd _) fun _ => Stable.pure _) fun _ => Stable.pure _
  refine Stable.bind stable_readNat fun k => ?_
  rcases k with _ | _ | k
  · exact Stable.bind hd fun _ => Stable.bind stable_readNat fun _ => Stable.pure _
  · exact Stable.bind hd fun _ => Stable.bind hd fun _ => Stable.bind hp fun _ =>
      Stable.bind hp fun _ => Stable.pure _
  · intro o o₂ b rest h; cases h

/-- **The decoder ignores the words after a witness it reads.** -/
theorem decodeWit_append {o : List Word} {w : Wit} (h : decodeWit o = some w) (o₂ : List Word) :
    decodeWit (o ++ o₂) = some w := by
  simp only [decodeWit, StateT.run', Functor.map, Option.map] at h ⊢
  cases h1 : readWit o with
  | none => rw [h1] at h; cases h
  | some p =>
    rw [h1] at h; cases h
    have h2 := stable_readWit o o₂ p.1 p.2 h1
    simp only [StateT.run] at h2
    rw [h2]

/-- A witness decoded from the first `8 k` bytes of `π` is `π`'s. -/
theorem decodeF_of_prefix {π : Proof} {k : ℕ} (hk : 8 * k ≤ π.size) {w : Wit}
    (h : WitnessSending.decodeF (π.extract 0 (8 * k)) = some w) :
    WitnessSending.decodeF π = some w := by
  rw [WitnessSending.decodeF, packFast_eq, extract_zero_toList] at h
  rw [WitnessSending.decodeF, packFast_eq, ← List.take_append_drop (8 * k) π.data.toList,
    packBytes_append_mul8 k _ _ (by rw [List.length_take, ← size_eq_length]; omega)]
  exact decodeWit_append h _

/-- `decodeF π` from the first `8 k` bytes, then `32 k`, …, at most `fuel` times, then from all of
`π`. -/
def decodePre (π : Proof) : ℕ → ℕ → Option Wit
  | 0, _ => WitnessSending.decodeF π
  | fuel + 1, k =>
    if 8 * k < π.size then
      match WitnessSending.decodeF (π.extract 0 (8 * k)) with
      | some w => some w
      | none => decodePre π fuel (4 * k)
    else WitnessSending.decodeF π

theorem decodePre_eq (π : Proof) : ∀ fuel k, decodePre π fuel k = WitnessSending.decodeF π
  | 0, _ => rfl
  | fuel + 1, k => by
    rw [decodePre]
    split_ifs with hk
    · split
      · rename_i w h; exact (decodeF_of_prefix hk.le h).symm
      · exact decodePre_eq π fuel _
    · rfl

/-- **The library's `decodeF π`, read from a prefix**: the first 16 KB, then 64 KB, … . -/
def decodeFront (π : Proof) : Option Wit := decodePre π 8 2048

theorem decodeFront_eq (π : Proof) : decodeFront π = WitnessSending.decodeF π :=
  decodePre_eq π 8 2048

/-! ## Signatures -/

/-- Equality of signatures is decidable: index, chain values and path compared. -/
instance : DecidableEq Sig := fun a b =>
  decidable_of_iff (a.idx = b.idx ∧ a.ots = b.ots ∧ a.path = b.path) (by
    cases a; cases b; simp)

end SpartanSrom
