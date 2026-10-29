-- New for `flock-recursive` (BLUEPRINT §4.3, A.7; stage RET-4, PATH-review F2): the declarations of
-- `FRNodeSoundA` that the revision 4 certificate reads, moved here verbatim (same names, statements
-- and proofs): `toListLE_eq_ofFn`, `enc64_toListLE`, `wordBytes_ofBytes`, `wordsBytes_elemWords`,
-- `digestOf_halves`, `readItems_qlen`. `FRNodeSoundA` imports this module.
import FRNodeReadW
import FRVIRCompile

/-!
# Bytes of digests and field elements, and the read items' query lengths

`digestOf_halves`: a digest's two F halves read back as the digest (through `wordsBytes_elemWords`).
`readItems_qlen`: every entry `Read.readItems` reads has a query no longer than its item's `qlen`.
-/

namespace FR.Snd
open RecursionFast Finset Circ

set_option linter.constructorNameAsVariable false

/-! ## From `FRNodeSoundA`: bytes of digests and field elements -/

theorem toListLE_eq_ofFn : ∀ (n x : ℕ),
    CompPoly.Bytes.toListLE n x = List.ofFn fun i : Fin n => (x / 256 ^ i.val).toUInt8
  | 0, _ => rfl
  | n + 1, x => by
    rw [CompPoly.Bytes.toListLE, toListLE_eq_ofFn n (x / 256), List.ofFn_succ]
    congr 1
    · apply UInt8.toNat_inj.mp; simp [Nat.toUInt8]
    · refine congrArg List.ofFn (funext fun i => ?_)
      rw [Fin.val_succ, Nat.div_div_eq_div_mul, pow_succ', Nat.mul_comm]

theorem enc64_toListLE (n : ℕ) : enc64 n = CompPoly.Bytes.toListLE 8 n := by
  rw [toListLE_eq_ofFn, enc64]

/-- A word decoded from eight bytes encodes back to them. -/
theorem wordBytes_ofBytes (v : Vector UInt8 8) : wordBytes (B64.ofBytes v).val.toBitVec = v.toList := by
  have h := congrArg Vector.toList (B64.toBytes_ofBytes v)
  rw [B64.toBytes_toList] at h
  rw [wordBytes, enc64_toListLE]
  exact h

/-- An F element decoded from 16 bytes: its two coefficient words are those bytes. -/
theorem wordsBytes_elemWords (v : Vector UInt8 16) :
    wordsBytes (Read.elemWords (F.ofBytes v)) = v.toList := by
  simp only [Read.elemWords, wordsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    F.ofBytes, wordBytes_ofBytes]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.toList_ofFn, List.getElem_append, List.length_ofFn, List.getElem_ofFn,
    Vector.getElem_toList]
  split_ifs with h
  · rfl
  · congr 1; simp at h1; omega

/-- **A digest's two F halves read back as the digest.** -/
theorem digestOf_halves {w : ℕ → F} {a b : ℕ} {d : Digest} (ha : w a = dlo d) (hb : w b = dhi d) :
    Read.digestOf w a b = d := by
  apply Vector.toList_inj.mp
  rw [Read.digestOf, Read.digestW_toList (by simp [Read.elemWords]), wordsBytes, List.flatMap_append,
    ← wordsBytes, ← wordsBytes, ha, hb, dlo, dhi, wordsBytes_elemWords, wordsBytes_elemWords]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.toList_ofFn, List.getElem_append, List.length_ofFn, List.getElem_ofFn,
    Vector.getElem_toList]
  split_ifs with h
  · rfl
  · congr 1; simp at h1; omega

/-! ## From `FRNodeSoundA`: the read items' query lengths -/

theorem readItems_qlen (B : List UInt8) : ∀ (o : ℕ) (its : List Item), ∀ e ∈ Read.readItems B o its,
    ∃ it ∈ its, e.1.size ≤ it.qlen
  | _, [], e, he => by simp [Read.readItems] at he
  | o, it :: its, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · refine ⟨it, List.mem_cons_self .., ?_⟩
      simp only [Read.entryAt, ByteArray.size, List.size_toArray]
      exact List.length_take_le _ _
    · obtain ⟨it', hit', h⟩ := readItems_qlen B _ its e he
      exact ⟨it', List.mem_cons_of_mem _ hit', h⟩

end FR.Snd
