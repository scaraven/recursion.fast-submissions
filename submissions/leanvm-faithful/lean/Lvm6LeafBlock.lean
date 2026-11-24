/-
# The two leaf hashes as one permutation of explicit lanes (lvm6, work package T1)

The contract's leaf hashes (`RecursionFast/Contract/Relation.lean`) are each one block of the
Keccak-256 sponge: `leafItem x = Keccak-256(0x48 ‖ x)` (33 bytes) and
`dataNode l r = Keccak-256(0x44 ‖ l ‖ r)` (65 bytes) fit in one 136-byte block, so each is one
`Keccak-f[1600]` (`keccakF`) of the zero state with its padded block absorbed. This module writes
that block as 25 explicit lanes, in the words the Keccak GKR works with (BLUEPRINT §2.3):

* `dLane d j`: the digest's word `j < 4`, bytes `8j … 8j + 7` little-endian (the contract's
  `blockLane` on the digest's bytes); `outDigest a`: the contract's output map (lanes `0 … 3`).
* `itemLanes w`, `nodeLanes l r`: the input lanes. The tag byte shifts the digest up by 8 bits, so
  lane `ℓ` carries `w (ℓ-1) >>> 56 ^^^ w ℓ <<< 8` (`Sh_ℓ` of the blueprint); the right digest of a
  node starts 33 bytes in, at lane 4 plus one byte. Then the padding: `0x01` after the message
  (byte 33 or 65: `0x100` in lane 4 or 8) and `0x80` in byte 135 (the top byte of lane 16).
  Lanes are combined by `^^^` (their bytes are disjoint), the `F₂`-linear form of the wiring.

Main statements: **`leafItem_block`**, **`dataNode_block`**, and `dLane_outDigest`,
`digest_ext_dLane` (a digest is its four output lanes). Byte-level helpers are at the end.
-/
import RecursionFast.Library.KeccakFast
import RecursionFast.Library.Keccak

namespace Lvm6

open RecursionFast RecursionFast.Keccak

/-! ## Specification -/

/-- Word `j` of a digest: its bytes `8j … 8j + 7`, little-endian (`0` for `j ≥ 4`). -/
def dLane (d : Digest) (j : ℕ) : UInt64 := blockLane d.toArray j

/-- The digest of a state: its first 32 bytes, lanes `0 … 3` little-endian (`keccak256`'s map). -/
def outDigest (a : State) : Digest :=
  ⟨((a.toList.flatMap fun w => (List.range 8).map fun k => (w >>> (8 * k).toUInt64).toUInt8).take
    32).toArray, by simp [List.map_const']⟩

/-- The padded block `0x48 ‖ x ‖ 0x01 ‖ 0 … ‖ 0x80` as 25 lanes, from the words `w 0 … w 3`
of `x`. -/
def itemLanes (w : ℕ → UInt64) : State :=
  #v[(0x48 : UInt64) ^^^ w 0 <<< 8, w 0 >>> 56 ^^^ w 1 <<< 8, w 1 >>> 56 ^^^ w 2 <<< 8,
    w 2 >>> 56 ^^^ w 3 <<< 8, w 3 >>> 56 ^^^ 0x100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0x8000000000000000, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The padded block `0x44 ‖ l ‖ r ‖ 0x01 ‖ 0 … ‖ 0x80` as 25 lanes, from the words of `l`
and `r`. -/
def nodeLanes (l r : ℕ → UInt64) : State :=
  #v[(0x44 : UInt64) ^^^ l 0 <<< 8, l 0 >>> 56 ^^^ l 1 <<< 8, l 1 >>> 56 ^^^ l 2 <<< 8,
    l 2 >>> 56 ^^^ l 3 <<< 8, l 3 >>> 56 ^^^ r 0 <<< 8, r 0 >>> 56 ^^^ r 1 <<< 8,
    r 1 >>> 56 ^^^ r 2 <<< 8, r 2 >>> 56 ^^^ r 3 <<< 8, r 3 >>> 56 ^^^ 0x100, 0, 0, 0, 0, 0, 0,
    0, 0x8000000000000000, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## Proof helpers -/

/-- Byte `k` of a word, little-endian. -/
def byteOf (w : UInt64) (k : ℕ) : UInt8 := (w >>> (8 * k).toUInt64).toUInt8

theorem byteOf_bit (w : UInt64) {k r : ℕ} (hk : k < 8) (hr : r < 8) :
    (byteOf w k).toBitVec.getLsbD r = w.toBitVec.getLsbD (8 * k + r) := by
  interval_cases k <;> simp [byteOf] <;> omega

theorem word_ext {a b : UInt64} (h : ∀ k < 8, byteOf a k = byteOf b k) : a = b := by
  refine UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun t ht => ?_)
  have e : t = 8 * (t / 8) + t % 8 := (Nat.div_add_mod t 8).symm
  rw [e, ← byteOf_bit a (by omega) (Nat.mod_lt _ (by decide)),
    ← byteOf_bit b (by omega) (Nat.mod_lt _ (by decide)), h _ (by omega)]

theorem byte_ext {a b : UInt8} (h : ∀ r < 8, a.toBitVec.getLsbD r = b.toBitVec.getLsbD r) :
    a = b :=
  UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq h)

theorem byteOf_xor (a b : UInt64) {k : ℕ} (hk : k < 8) :
    byteOf (a ^^^ b) k = byteOf a k ^^^ byteOf b k :=
  byte_ext fun r hr => by
    rw [UInt8.toBitVec_xor, BitVec.getLsbD_xor, byteOf_bit _ hk hr, byteOf_bit _ hk hr,
      byteOf_bit _ hk hr, UInt64.toBitVec_xor, BitVec.getLsbD_xor]

theorem byteOf_shl8 (a : UInt64) {k : ℕ} (hk : k < 8) :
    byteOf (a <<< 8) k = if k = 0 then 0 else byteOf a (k - 1) := by
  refine byte_ext fun r hr => ?_
  rw [byteOf_bit _ hk hr]
  split
  · subst_vars; simp; omega
  · rw [byteOf_bit _ (by omega) hr, show 8 * (k - 1) + r = 8 * k + r - 8 by omega]
    simp [show 8 * k + r < 64 by omega, show ¬ 8 * k + r < 8 by omega]
    rw [BitVec.getLsbD_eq_getElem (by omega)]

theorem byteOf_shr56 (a : UInt64) {k : ℕ} (hk : k < 8) :
    byteOf (a >>> 56) k = if k = 0 then byteOf a 7 else 0 := by
  refine byte_ext fun r hr => ?_
  rw [byteOf_bit _ hk hr]
  split
  · subst_vars; rw [byteOf_bit _ (by omega) hr]; simp
  · simp
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem blockLane_bit (a : Array UInt8) (i t : ℕ) (ht : t < 64) :
    (blockLane a i).toBitVec.getLsbD t = (a.getD (8 * i + t / 8) 0).toBitVec.getLsbD (t % 8) := by
  rw [blockLane_unfold]
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64,
    BitVec.getLsbD_or, BitVec.getLsbD_zero, BitVec.ofNat_eq_ofNat,
    BitVec.zero_umod, BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod,
    BitVec.shiftLeft_zero, UInt64.toBitVec_ofNat, BitVec.reduceMod, Bool.false_or]
  interval_cases t <;> simp only [Nat.reduceLT, BitVec.getLsbD_eq_getElem,
    BitVec.getElem_setWidth, Nat.reduceLeDiff, BitVec.getLsbD_of_ge, Bool.or_self,
    Nat.reduceMod, BitVec.getElem_shiftLeft, decide_false, Bool.not_false, Nat.reduceSub,
    Bool.true_and, Bool.false_or, decide_true, Bool.not_true, Nat.sub_eq_zero_of_le, Nat.ofNat_pos,
    Bool.false_and, Bool.or_false, Nat.reduceDiv, Nat.add_zero]

theorem byteOf_blockLane (a : Array UInt8) (i : ℕ) {k : ℕ} (hk : k < 8) :
    byteOf (blockLane a i) k = a.getD (8 * i + k) 0 :=
  byte_ext fun r hr => by
    rw [byteOf_bit _ hk hr, blockLane_bit _ _ _ (by omega), show (8 * k + r) / 8 = k by omega,
      show (8 * k + r) % 8 = r by omega]

theorem byteOf_zero (k : ℕ) : byteOf 0 k = 0 := by simp [byteOf]

theorem byteOf_0x48 {k : ℕ} (hk : k < 8) : byteOf 0x48 k = if k = 0 then 0x48 else 0 := by
  interval_cases k <;> rfl

theorem byteOf_0x44 {k : ℕ} (hk : k < 8) : byteOf 0x44 k = if k = 0 then 0x44 else 0 := by
  interval_cases k <;> rfl

theorem byteOf_0x100 {k : ℕ} (hk : k < 8) : byteOf 0x100 k = if k = 1 then 1 else 0 := by
  interval_cases k <;> rfl

theorem byteOf_0x80 {k : ℕ} (hk : k < 8) :
    byteOf 0x8000000000000000 k = if k = 7 then 0x80 else 0 := by
  interval_cases k <;> rfl

/-- A message shorter than a block: its bytes, `0x01`, zeros, and `0x80` at byte 135. -/
theorem pad_getD (msg : List UInt8) (h : msg.length + 1 < rate) (q : ℕ) :
    (pad msg).toArray.getD q 0 =
      if q < msg.length then msg.getD q 0 else if q = msg.length then 1
      else if q = rate - 1 then 0x80 else 0 := by
  have r : rate = 136 := rfl
  have hp : pad msg = msg ++ (0x01 :: List.replicate (134 - msg.length) 0 ++ [0x80]) := by
    simp only [pad, r] at h ⊢
    rw [Nat.mod_eq_of_lt (by omega), ite_eq_right (by omega), show 136 - msg.length - 2 =
      134 - msg.length by omega]
  rw [hp, r]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge q msg.length with h1 | h1
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right (by omega), List.getElem?_append_right h1]
    rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · subst h2; simp
    · rw [ite_eq_right (by omega), List.cons_append, List.getElem?_cons, ite_eq_right (by omega)]
      simp only [List.getElem?_append, List.length_replicate, List.getElem?_replicate]
      by_cases h3 : q < 135
      · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]; rfl
      · rw [ite_eq_right (by omega)]
        by_cases h4 : q = 135
        · subst h4
          rw [ite_eq_left rfl, show 135 - msg.length - 1 - (134 - msg.length) = 0 by omega]
          rfl
        · rw [ite_eq_right (by omega), List.getElem?_eq_none (by simp; omega)]; rfl

/-- One block: a message shorter than the rate hashes to one permutation of its padded block. -/
theorem keccakDigest_one (msg : List UInt8) (h : msg.length < rate) :
    keccakDigest msg =
      outDigest (keccakF (Vector.ofFn fun i => blockLane (pad msg).toArray i)) := by
  have hp : (pad msg).length = rate := by
    have := pad_length msg
    simp only [rate] at this h ⊢
    omega
  have hst : absorb (Vector.replicate 25 0) (pad msg) ((pad msg).length / rate) =
      keccakF (Vector.ofFn fun i => blockLane (pad msg).toArray i) := by
    rw [hp, Nat.div_self (by decide), show (1 : ℕ) = 0 + 1 from rfl, absorb, absorb,
      List.take_of_length_le hp.le]
    refine congrArg keccakF (Vector.ext fun i hi => ?_)
    simp
  have e : keccakDigest msg =
      outDigest (absorb (Vector.replicate 25 0) (pad msg) ((pad msg).length / rate)) := rfl
  rw [e, hst]

theorem toList_getD (d : Digest) (q : ℕ) : d.toList.getD q 0 = d.toArray.getD q 0 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

theorem byteOf_dLane (d : Digest) (j : ℕ) {k : ℕ} (hk : k < 8) :
    byteOf (dLane d j) k = d.toArray.getD (8 * j + k) 0 :=
  byteOf_blockLane _ _ hk

/-! ## The two blocks -/

theorem itemLanes_eq (x : Digest) :
    (Vector.ofFn fun i => blockLane (pad (tagItem :: x.toList)).toArray i) =
      itemLanes (dLane x) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_ofFn]
  refine word_ext fun k hk => ?_
  rw [byteOf_blockLane _ _ hk, pad_getD _ (by simp [rate])]
  interval_cases i <;> interval_cases k <;>
    simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem_cons_succ,
      List.getElem_cons_zero, List.getElem_toArray, List.length_cons, Nat.add_one_sub_one, Nat.lt_add_one,
      Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceMul,
      Nat.succ_ne_self, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero, OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat,
      Option.getD_some, UInt8.xor_self, UInt8.xor_zero, UInt8.zero_xor, Vector.getElem_mk,
      Vector.getElem_toArray, Vector.getElem_toList, Vector.length_toList, Vector.size_toArray, add_zero,
      byteOf_0x100, byteOf_0x48, byteOf_0x80, byteOf_dLane, byteOf_shl8, byteOf_shr56, byteOf_xor,
      byteOf_zero, getElem?_pos, itemLanes, lt_self_iff_false, mul_one, mul_zero, one_ne_zero, rate,
      tagItem, tsub_self, zero_add, zero_ne_one, ↓reduceIte]

/-- **A leaf item is one permutation** of `itemLanes` of the block's words. -/
theorem leafItem_block (x : Digest) : leafItem x = outDigest (keccakF (itemLanes (dLane x))) := by
  rw [leafItem, keccakDigest_one _ (by simp [rate]), itemLanes_eq]

theorem nodeLanes_eq (l r : Digest) :
    (Vector.ofFn fun i => blockLane (pad (tagData :: l.toList ++ r.toList)).toArray i) =
      nodeLanes (dLane l) (dLane r) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_ofFn]
  refine word_ext fun k hk => ?_
  rw [byteOf_blockLane _ _ hk, pad_getD _ (by simp [rate])]
  interval_cases i <;> interval_cases k <;>
    simp only [Array.getD_eq_getD_getElem?, List.cons_append, List.getD_eq_getElem?_getD,
      List.getElem_append_left, List.getElem_append_right, List.getElem_cons_succ, List.getElem_cons_zero,
      List.getElem_toArray, List.length_append, List.length_cons, Nat.add_one_sub_one, Nat.lt_add_one,
      Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceLeDiff,
      Nat.reduceMul, Nat.reduceSub, Nat.succ_ne_self, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero,
      OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, Option.getD_some, Std.le_refl, UInt8.xor_self,
      UInt8.xor_zero, UInt8.zero_xor, Vector.getElem_mk, Vector.getElem_toArray, Vector.getElem_toList,
      Vector.length_toList, Vector.size_toArray, add_zero, byteOf_0x100, byteOf_0x44, byteOf_0x80,
      byteOf_dLane, byteOf_shl8, byteOf_shr56, byteOf_xor, byteOf_zero, getElem?_pos, lt_self_iff_false,
      mul_one, mul_zero, nodeLanes, one_ne_zero, rate, tagData, tsub_self, zero_add, zero_ne_one,
      ↓reduceIte]

/-- **A data-tree node is one permutation** of `nodeLanes` of its children's words. -/
theorem dataNode_block (l r : Digest) :
    dataNode l r = outDigest (keccakF (nodeLanes (dLane l) (dLane r))) := by
  rw [dataNode, keccakDigest_one _ (by simp [rate]), nodeLanes_eq]

/-! ## A digest is its four output lanes -/

theorem outDigest_eq_outBytes (a : State) : outDigest a = outBytes (S25.ofVec a) := by
  rw [outBytes_eq, S25.toVec_ofVec]; rfl

/-- The words of a state's digest are its lanes `0 … 3`. -/
theorem dLane_outDigest (a : State) {j : ℕ} (hj : j < 4) : dLane (outDigest a) j = a[j] := by
  refine word_ext fun k hk => ?_
  rw [byteOf_dLane _ _ hk, outDigest_eq_outBytes]
  interval_cases j <;> interval_cases k <;> rfl

/-- Two digests with the same four words are equal. -/
theorem digest_ext_dLane {a b : Digest} (h : ∀ j < 4, dLane a j = dLane b j) : a = b := by
  refine Vector.ext fun q hq => ?_
  have e : ∀ d : Digest, d[q] = byteOf (dLane d (q / 8)) (q % 8) := fun d => by
    rw [byteOf_dLane _ _ (Nat.mod_lt _ (by decide)), Nat.div_add_mod]
    simp [Array.getD_eq_getD_getElem?, hq]
  rw [e, e, h _ (by omega)]

/-- The digest whose words are `w 0 … w 3`. -/
def ofWords (w : ℕ → UInt64) : Digest := outDigest (Vector.ofFn fun i => w i)

theorem dLane_ofWords (w : ℕ → UInt64) {j : ℕ} (hj : j < 4) : dLane (ofWords w) j = w j := by
  rw [ofWords, dLane_outDigest _ hj, Vector.getElem_ofFn]

end Lvm6
