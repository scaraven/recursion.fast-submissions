-- New for `flock-recursive` (BLUEPRINT §4.1 `leaf_sound`, A.10 S1/Z1 for a leaf; stage S-N1).
import FRSoundnessExtStmt
import FRSoundnessFrDF

/-!
# The leaf case: `SLeaf` on the run's chain gives the leaf witness

On a leaf kind's accepted run (`SkRun`, `k ≠ N30`), the extractor outputs
`.leaf (bytesAt π 16 32) (leafN k)` (`E_leaf`). It is a witness when the leaf statement
`SLeaf = ShHoldsL ∧ ZHolds` holds on the run's chain:

* **`digBit_readF`**: the shift's boundary bits (`digBit` of two `readF` halves) are the
  digest's bits (`digestBit`), so `ShHoldsL` is `leaf_sound`'s `ChainLinks`
  (**`chainLinks_of_shHoldsL`**) with `s` the seed's `hdr.pub` and `h` the statement's digest;
* `ZHolds zlmFR` is the Z truth with every block a chain block (`zHolds_iff_truthZ`), so
  `leaf_of_truthZ` gives `chainEnd s n = h` (**`chainEnd_of_sLeaf`**);
* the run's statement check gives `c = leafStmt h (leafN k)` (**`c_leaf_of_run`**);
* **`rel_leaf_of_run`**: `Rel acc c (.leaf (bytesAt π 16 32) (leafN k))`.
-/

namespace FR.Snd
open RecursionFast Finset ProductCircuit Blake2sCircuit

set_option linter.constructorNameAsVariable false

/-! ## Bits of bytes -/

theorem testBit_ofListLE : ∀ (l : List UInt8) (j : ℕ),
    (CompPoly.Bytes.ofListLE l).testBit j = ((l.getD (j / 8) 0).toNat).testBit (j % 8)
  | [], j => by simp [CompPoly.Bytes.ofListLE]
  | b :: l, j => by
    rw [CompPoly.Bytes.ofListLE_cons, Nat.add_comm, show (256 : ℕ) = 2 ^ 8 from rfl,
      Nat.testBit_two_pow_mul_add _ (by simpa using b.toNat_lt)]
    split_ifs with h
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]; rfl
    · rw [testBit_ofListLE l (j - 8)]
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 8 := ⟨j - 8, by omega⟩
      rw [Nat.add_sub_cancel, show (t + 8) / 8 = t / 8 + 1 by omega, Nat.add_mod_right]
      rfl

theorem getLsbD_ofBytes (v : Vector UInt8 8) (j : ℕ) :
    (B64.ofBytes v).val.toBitVec.getLsbD j = ((v.toList.getD (j / 8) 0).toNat).testBit (j % 8) := by
  rw [BitVec.getLsbD, ← UInt64.toNat, B64.ofBytes_toNat, CompPoly.Bytes.ofVecLE, testBit_ofListLE]

/-- **Bit `j` of a decoded F element is bit `j mod 8` of byte `j / 8`.** -/
theorem bitF_ofBytes (v : Vector UInt8 16) (j : Fin 128) :
    FR.bitF (F.ofBytes v) j = ((v.toList.getD (j.val / 8) 0).toNat).testBit (j.val % 8) := by
  have hj := j.isLt
  unfold FR.bitF F.ofBytes
  split_ifs with h
  · rw [getLsbD_ofBytes]
    congr 2
    simp only [Vector.toList_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      show j.val / 8 < 8 by omega, dite_true, Option.getD_some, Vector.getElem_toList,
      List.getElem?_eq_getElem (show j.val / 8 < v.toList.length by simp; omega)]
  · rw [getLsbD_ofBytes]
    rw [show (j.val - 64) % 8 = j.val % 8 by omega]
    congr 2
    simp only [Vector.toList_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      show (j.val - 64) / 8 < 8 by omega, dite_true, Option.getD_some,
      List.getElem?_eq_getElem (show j.val / 8 < v.toList.length by simp; omega)]
    simp only [Vector.getElem_toList]
    congr 1; omega

theorem bytesAt_toList_getD (q : ByteArray) (o n k : ℕ) (hk : k < n) :
    (bytesAt q o n).toList.getD k 0 = q.data.toList.getD (o + k) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk), Option.getD_some,
    Vector.getElem_toList, getElem_bytesAt _ _ _ _ hk]

theorem digestBit_bytesAt (q : ByteArray) (o : ℕ) {σ : ℕ} (hσ : σ < 256) :
    Block.digestBit (bytesAt q o 32) σ = ((q.data.toList.getD (o + σ / 8) 0).toNat).testBit (σ % 8) := by
  simp only [Block.digestBit, hσ, dite_true]
  rw [getElem_bytesAt _ _ _ _ (by omega)]
  rfl

/-- **The boundary bits are the digest's bits**: `digBit` of the two 16-byte halves at `o` and
`o + 16` is `digestBit` of the 32 bytes at `o`. -/
theorem digBit_readF (q : ByteArray) (o : ℕ) {σ : ℕ} (hσ : σ < 256) :
    Impl.digBit (readF q o) (readF q (o + 16)) σ = Block.digestBit (bytesAt q o 32) σ := by
  rw [digestBit_bytesAt q o hσ, Impl.digBit]
  split_ifs with h
  · rw [readF, bitF_ofBytes, bytesAt_toList_getD _ _ _ _ (by omega)]
  · rw [readF, bitF_ofBytes, bytesAt_toList_getD _ _ _ _ (by simp only; omega)]
    simp only
    rw [show (σ - 128) % 128 % 8 = σ % 8 by omega,
      show o + 16 + (σ - 128) % 128 / 8 = o + σ / 8 by omega]

/-! ## `ShHoldsL` is `ChainLinks` -/

theorem zBlk_pos (κ : Kind) (L es : Log) (blk x : ℕ) (hx : x < 2 ^ 14) :
    zBlk κ L es blk (pos x) = zNode κ L es blk x := by
  simp only [zBlk, zNode, pos, Nat.mod_eq_of_lt hx]

/-- The leaf's start and end bits (`sbL`, `hbL`) as `ofBool` of the boundary digests. -/
theorem sbL_leaf {κ : Kind} (hκ : κ.isNode = false) (es : Log) {σ : ℕ} (hσ : σ < 256) :
    sbL κ es σ = ofBool F (Block.digestBit (bytesAt (entAt es 0).1 87 32) σ) := by
  simp only [sbL, bndL, hκ, Bool.false_eq_true, ite_false, List.getD_cons_zero,
    List.getD_cons_succ, ofBool]
  rw [show (103 : ℕ) = 87 + 16 from rfl, digBit_readF _ _ hσ]

theorem hbL_leaf {κ : Kind} (hκ : κ.isNode = false) (es : Log) {σ : ℕ} (hσ : σ < 256) :
    hbL κ es σ = ofBool F (Block.digestBit (bytesAt (msgAt es 1) 1 32) σ) := by
  simp only [hbL, bndL, hκ, Bool.false_eq_true, ite_false, List.getD_cons_zero,
    List.getD_cons_succ, ofBool]
  rw [show (17 : ℕ) = 1 + 16 from rfl, digBit_readF _ _ hσ]

/-- **`ShHoldsL` is `leaf_sound`'s `ChainLinks`** over the decoded blocks. -/
theorem chainLinks_of_shHoldsL {κ : Kind} (hκ : κ.isNode = false) {L es : Log}
    (h : ShHoldsL (nbS κ) (zNode κ L es) (sbL κ es) (hbL κ es)) :
    Leaf.ChainLinks (2 ^ nbS κ) (zBlk κ L es) (bytesAt (entAt es 0).1 87 32)
      (bytesAt (msgAt es 1) 1 32) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i hi j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [zBlk_pos _ _ _ _ _ (by simp only [Chain.dBase]; omega),
      zBlk_pos _ _ _ _ _ (by omega)]
    exact h1 i hi j hj
  · rw [zBlk_pos _ _ _ _ _ (by simp only [Chain.dBase]; omega), ← sbL_leaf hκ es hj]
    exact h2 j hj
  · rw [zBlk_pos _ _ _ _ _ (by omega), ← hbL_leaf hκ es hj]
    exact h3 j hj

theorem qL_eq_nbS (κ : Kind) : qL κ = nbS κ := rfl

/-- **The leaf statement gives the chain's end** (`leaf_of_truthZ`). -/
theorem chainEnd_of_sLeaf {L es : Log} (hκ : (kindOf es).isNode = false)
    (h : SLeaf (kindOf es) L es) :
    chainEnd (bytesAt (entAt es 0).1 87 32) (2 ^ nbS (kindOf es)) = bytesAt (msgAt es 1) 1 32 := by
  have hZ := (zHolds_iff_truthZ hκ).1 h.2
  rw [qL_eq_nbS] at hZ
  exact leaf_of_truthZ (Nat.one_le_two_pow) hZ (chainLinks_of_shHoldsL hκ h.1)

/-! ## The statement on the run -/

variable {impl : OpImpl} {vk c : Digest} {π : Proof} {tr : Trace}
  {y : List Val × List Bool × Trace}

theorem extract_getD (π : ByteArray) {a b i : ℕ} (hi : i < b - a) :
    (π.extract a b).data.toList.getD i 0 = π.data.toList.getD (a + i) 0 := by
  rw [toList_extract, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hi, List.getElem?_drop]

/-- The little-endian sum of eight bytes that are `enc64 n`'s is `n` (a leaf kind's length). -/
theorem sum_enc64 {n : ℕ} (hn : n = 2 ^ 18 ∨ n = 2 ^ 16) {b : ℕ → ℕ}
    (hb : ∀ i < 8, b i = ((enc64 n).getD i 0).toNat) :
    ((List.range 8).map fun i => b i * 256 ^ i).sum = n := by
  have e : (List.range 8).map (fun i => b i * 256 ^ i) =
      (List.range 8).map (fun i => ((enc64 n).getD i 0).toNat * 256 ^ i) :=
    List.map_congr_left fun i hi => by rw [hb i (List.mem_range.1 hi)]
  rw [e]
  rcases hn with rfl | rfl <;> decide

/-- **A leaf's statement on its run**: `c = leafStmt h (leafN k)` with `h` the log's
statement digest. -/
theorem c_leaf_of_run {k : Kind} (hk : k.isNode = false) (hπ : π.size = piSize)
    (h : SkRun impl k ⟨vk, c, π⟩ tr y) :
    c = leafStmt (stL (fsOf tr items) 0) (leafN k) := by
  obtain ⟨h1, h2, -⟩ := stmt_view h
  have hn := h2 hk
  have h1' : stmtDigest k (FR.msgAt ⟨vk, c, π⟩ fStmt 0 128) = c := h1
  have hkN : k ≠ .N30 := by rintro rfl; cases hk
  rw [← h1', stLog_eq h.hq (by norm_num)]
  have ha : absOff fStmt 0 = 48 := by decide
  have ha1 : absOff fStmt (1 + 32 * 0) = 49 := by decide
  have ha33 : absOff fStmt 33 = 48 + 33 := by decide
  simp only [FR.msgAt, ha, ha33] at hn ⊢
  rw [ha1]
  have hs : 48 + 128 ≤ π.size := by rw [hπ, piSize_eq]; norm_num
  have hlt : leafN k = 2 ^ 18 ∨ leafN k = 2 ^ 16 := by
    cases k
    · exact .inl rfl
    · exact .inr rfl
    · exact absurd rfl hkN
  have hbytes : ∀ i < 8, ((π.extract 48 (48 + 128)).data.getD (33 + i) 0).toNat =
      ((enc64 (leafN k)).getD i 0).toNat := by
    intro i hi
    have e := congrArg (fun a : Array UInt8 => a.toList.getD i 0) hn
    simp only [bytesOf, List.toList_toArray] at e
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD,
      extract_getD π (by omega), ← e, extract_getD π (by omega), Nat.add_assoc]
  cases k with
  | N30 => exact absurd rfl hkN
  | L32 =>
    simp only [stmtDigest, leafStmtF_eq]
    rw [sum_enc64 hlt hbytes, bytesAt_extract_le _ (by omega)]
  | P30 =>
    simp only [stmtDigest, leafStmtF_eq]
    rw [sum_enc64 hlt hbytes, bytesAt_extract_le _ (by omega)]

/-- **The leaf witness on the run's chain is a witness**: the run's statement check, the seed's
`hdr.pub` and `SLeaf` on the chain. -/
theorem rel_leaf_of_run {k : Kind} (hk : k.isNode = false) (hkπ : FR.kindOf π = .snark k)
    (h : SkRun impl k ⟨vk, c, π⟩ tr y) (acc : Digest → Signed → Bool) {L : Log}
    (hS : SLeaf k L (fsOf tr items)) :
    Rel acc c (.leaf (bytesAt π 16 32) (leafN k)) := by
  have hπ := size_of_snark hkπ
  have hkc : kindOf (fsOf tr items) = k := kindOf_chain h.hq hkπ
  have hS' : SLeaf (kindOf (fsOf tr items)) L (fsOf tr items) := hkc ▸ hS
  have he := chainEnd_of_sLeaf (hkc ▸ hk) hS'
  rw [seed_bytesAt h.hq (o := 16) (n := 32) (by norm_num), hkc] at he
  refine ⟨?_, ?_⟩
  · cases k <;> simp [leafN, Kind.m, chainCap]
  · rw [c_leaf_of_run hk hπ h]
    show leafStmt (stL _ 0) _ = leafStmt (chainEnd _ (2 ^ nbS k)) _
    rw [he]; rfl

/-! ## Controls -/

/-- Control (positive / negative): the byte order of `testBit_ofListLE` (little-endian, bit 8 is
byte 1's bit 0, not byte 0's). -/
theorem testBit_ofListLE_ctl : (CompPoly.Bytes.ofListLE [1, 0]).testBit 0 = true ∧
    (CompPoly.Bytes.ofListLE [0, 1]).testBit 8 = true ∧
    (CompPoly.Bytes.ofListLE [1, 0]).testBit 8 = false := by decide

/-- Control (negative): `sum_enc64` reads the bytes in little-endian order: `enc64 (2^16)`'s
bytes summed big-endian are not `2^16`. -/
theorem sum_enc64_neg : ((List.range 8).map fun i =>
    ((enc64 (2 ^ 16)).getD (7 - i) 0).toNat * 256 ^ i).sum ≠ 2 ^ 16 := by decide

end FR.Snd
