-- New for `flock-recursive` (BLUEPRINT revision 3.4, Appendix A.6's kind table; S-E1-M1, S-E1-M2).
import FRBlockChain
import FRBlockStream

/-!
# The block kinds of A.6

A **kind** is a public target of the block R1CS (`FRBlockLayout`): which inputs it pins and to
which bits, besides `one = 1` and slot 8. Every kind of A.6 is an instance of one shape
(`Kind`): `h_in` pinned to `h0` or free, some message bytes pinned (`msgPin p = some u`), and slot
8 (`t_lo`, `t_hi` = the counter `t`, `f0 = flagOf fin`, `f1 = 0`) as in `Stream.blockTarget`.

| kind | `h0` | pinned message bytes | `t` | final |
|---|---|---|---|---|
| `streamKind t fin` | no | — | `t` | `fin` |
| `streamStart` | yes | — | 64 | no |
| `streamEnd41` | no | `41…63 = 0` | 4,265 | yes |
| `hashA` | yes | `0 = 0x4C`, `41…63 = 0` | 41 | yes |
| `hashB1 tag` | yes | `0 = tag` (`0x4E`, `0x4B`, `0x4D`) | 64 | no |
| `hashB2` | no | `1…63 = 0` | 65 | yes |
| `w43 i s` | yes | `0 = 0x57`, `9 = i`, `10 = s`, `43…63 = 0` | 43 | yes |

A.6's `chain` kind is `Chain.chainTarget` (`FRBlockChain`, with its own `block_sound` and
`block_complete`, used by `leaf_sound`); `stream` is `Stream.blockTarget t fin`, equal to
`(streamKind t fin).target` (`streamKind_target`), so the digest chain's statements are
instances.

Results (generic, then per kind):
* `Kind.target_ok`: every kind pins `one` and otherwise only inputs;
* `Kind.block_sound` (`h_out` is the compression with the kind's counter and flag),
  `Kind.hIn_eq_h0`, `Kind.msgByte_eq` (the pinned values), `Kind.block_complete` (the honest block
  of any free inputs satisfies the kind);
* `one_block_sound`: a fresh-hash single-block kind (`h0`, `t = L ≤ 64`, final, zero bytes from
  `L`) outputs `blake2sDigest` of its first `L` message bytes; `two_block_sound`: a fresh first
  block (`t = 64`, not final) linked to a final second block (`t = L ∈ [65, 128]`, zero bytes from
  `L − 64`) outputs `blake2sDigest` of the `L` message bytes;
* for `hashStmt` (BLUEPRINT §4.2): `hashA_sound`, `hashA_leafStmt`, `hashB_sound`,
  `hashB_nodeStmt`. **`hashStmt_sound` itself** (the 8 element equalities with `stmt` and its parse
  into `h`, `n`, `c₁`, `c₂`) is S-E2's (`FRWots`), on top of these;
* the dump (A.6's KAT): `kindRows base tgt`, the rows of `A₀^kind`, `B₀^kind` and `E`
  (`kindRows_eq`), `kindLine`, `allKinds`. No evaluation happens in the entry.
-/

namespace FR

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit Block FR.Stream

namespace Kinds

/-! ## The shape of a kind -/

/-- A block kind of A.6. -/
structure Kind where
  /-- `h_in` pinned to `h0` (a fresh hash). -/
  h0Pin : Bool
  /-- The pinned message bytes (`p < 64`). -/
  msgPin : ℕ → Option UInt8
  /-- The counter. -/
  t : ℕ
  /-- The last-block flag. -/
  fin : Bool

/-- The public target of a kind. -/
def Kind.target (κ : Kind) (k : Pos) : Option Bool :=
  if k.val < 256 then (if κ.h0Pin then some (wordsBit h0 k.val) else none)
  else if k.val < 512 then none
  else if k.val < 1024 then
    (κ.msgPin ((k.val - 512) / 8)).map fun u ↦ u.toBitVec.getLsbD ((k.val - 512) % 8)
  else blockTarget κ.t κ.fin k

private theorem pv {v : ℕ} (h : v < 16384) : ((pos v : Pos) : ℕ) = v := pos_val h

section Generic

variable (κ : Kind)

theorem Kind.target_ge {k : Pos} (hk : 1024 ≤ k.val) : κ.target k = blockTarget κ.t κ.fin k := by
  rw [Kind.target, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem Kind.target_h0 (hp : κ.h0Pin = true) : ∀ j < 256, κ.target (pos j) = some (wordsBit h0 j) :=
  fun j hj ↦ by rw [Kind.target, pv (by omega), ite_eq_left hj, hp, ite_eq_left rfl]

theorem Kind.target_hfree (hp : κ.h0Pin = false) {j : ℕ} (hj : j < 256) :
    κ.target (pos j) = none := by
  rw [Kind.target, pv (by omega), ite_eq_left hj, hp]
  rfl

theorem Kind.target_msg {p : ℕ} (hp : p < 64) {i : ℕ} (hi : i < 8) :
    κ.target (pos (msgBase + 8 * p + i)) =
      (κ.msgPin p).map fun u ↦ u.toBitVec.getLsbD i := by
  have hv := pv (show msgBase + 8 * p + i < 16384 by simp only [msgBase]; omega)
  rw [Kind.target, hv, ite_eq_right (by simp only [msgBase]; omega),
    ite_eq_right (by simp only [msgBase]; omega), ite_eq_left (by simp only [msgBase]; omega)]
  simp only [msgBase, show (512 + 8 * p + i - 512) / 8 = p by omega,
    show (512 + 8 * p + i - 512) % 8 = i by omega]

/-- **Every kind is a target of the entry**: it pins `one` to `1` and otherwise only inputs. -/
theorem Kind.target_ok : TargetOk κ.target := by
  refine ⟨by rw [κ.target_ge (by rw [onePos_val]; omega)]; exact blockTarget_ok.1, fun k b h ↦ ?_⟩
  rcases Nat.lt_or_ge k.val 1024 with hk | hk
  · right
    unfold Kind.target at h
    split_ifs at h <;> omega
  · rw [κ.target_ge hk] at h
    exact blockTarget_ok.2 k b h

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {w : Pos → Bool}

/-- The kind's slot 8 as a `blockTarget`, met by a block meeting the kind. -/
private theorem meets_block (hm : MeetsB κ.target w) : MeetsB (blockTarget κ.t κ.fin) w :=
  fun k b hk ↦ hm k b (by
    rcases Nat.lt_or_ge k.val 1024 with h | h
    · rw [blockTarget_low h] at hk; cases hk
    · rwa [κ.target_ge h])

/-- **A kind, soundness.** A Boolean block satisfying the block R1CS with a kind's target carries
at `h_out` the compression of its `h_in` and its message with the kind's counter and flag. -/
theorem Kind.block_sound
    (h : HoldsE (blockR1CS κ.target) (targetVal R κ.target) (liftBlock R w)) :
    hOut w = compress (hIn w) (block (msgBytes w)) κ.t.toUInt64 (flagOf κ.fin) 0 :=
  have ⟨hz, h1, hm⟩ := holdsE_sound κ.target_ok h
  have hb := meets_block κ hm
  compress_sound hz h1 rfl rfl (readWord_of_meets hb pat_tlo) (readWord_of_meets hb pat_thi)
    (readWord_of_meets hb pat_f0) (readWord_of_meets hb pat_f1)

/-- A fresh-hash kind's block has `h_in = h0`. -/
theorem Kind.hIn_eq_h0 (hp : κ.h0Pin = true)
    (h : HoldsE (blockR1CS κ.target) (targetVal R κ.target) (liftBlock R w)) : hIn w = h0 :=
  hIn_of_meets (holdsE_sound κ.target_ok h).2.2 (κ.target_h0 hp)

/-- A pinned message byte holds its value. -/
theorem Kind.msgByte_eq {p : ℕ} (hp : p < 64) {u : UInt8} (hu : κ.msgPin p = some u)
    (h : HoldsE (blockR1CS κ.target) (targetVal R κ.target) (liftBlock R w)) :
    readByte w (msgBase + 8 * p) = u :=
  readByte_of_meets (holdsE_sound κ.target_ok h).2.2 fun i hi ↦ by
    rw [κ.target_msg hp hi, hu]
    rfl

end Generic

/-! ## Completeness -/

/-- The input block of a kind with free chaining value `h` and free message bytes `m`. -/
def Kind.inp (κ : Kind) (h : Vector UInt32 8) (m : List UInt8) (k : Pos) : Bool :=
  match κ.target k with
  | some b => b
  | none =>
    if k.val < 256 then wordsBit h k.val
    else if msgBase ≤ k.val ∧ k.val < msgBase + 512 then
      (m.getD ((k.val - msgBase) / 8) 0).toBitVec.getLsbD ((k.val - msgBase) % 8)
    else false

/-- The honest block of a kind. -/
noncomputable def Kind.trace (κ : Kind) (h : Vector UInt32 8) (m : List UInt8) : Pos → Bool :=
  blake2sCircuit.traceF (κ.inp h m)

private theorem trace_input (κ : Kind) (h : Vector UInt32 8) (m : List UInt8) {k : Pos}
    (hk : k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152)) : κ.trace h m k = κ.inp h m k :=
  traceF_input bounded_blake2s _
    (by rw [blake2sCircuit_inputs, getLsbD_inputs]; exact decide_eq_true hk)
    (by rw [blake2sCircuit_cpos]; exact Fin.ne_of_val_ne (by rw [constPos_val]; omega))

/-- **A kind, completeness.** The honest block of any free inputs satisfies the kind's block R1CS
with its target, holds `h` as `h_in` if `h_in` is free, and the free message bytes of `m`. -/
theorem Kind.block_complete {R : Type*} [CommRing R] [CharP R 2] (κ : Kind) (h : Vector UInt32 8)
    (m : List UInt8) :
    HoldsE (blockR1CS κ.target) (targetVal R κ.target) (liftBlock R (κ.trace h m)) ∧
      (κ.h0Pin = false → hIn (κ.trace h m) = h) ∧
      ∀ p < 64, κ.msgPin p = none → readByte (κ.trace h m) (msgBase + 8 * p) = m.getD p 0 := by
  have h1 : κ.trace h m onePos = true := by
    rw [Kind.trace, onePos, ← blake2sCircuit_cpos]; exact traceF_cpos bounded_blake2s _
  refine ⟨holdsE_complete (trace_satisfies (R := R) bounded_blake2s (κ.inp h m)).1
    fun k b hk ↦ ?_, fun hp ↦ hIn_of_bits fun j hj ↦ ?_, fun p hp hu ↦ ?_⟩
  · rcases κ.target_ok.2 k b hk with rfl | hin
    · rw [κ.target_ok.1] at hk; cases hk; exact h1
    · rw [trace_input κ h m hin, Kind.inp, hk]
  · have hv : ((pos j : Pos) : ℕ) = j := pv (by omega)
    rw [trace_input _ _ _ (by rw [hv]; omega), Kind.inp, κ.target_hfree hp hj, hv, ite_eq_left hj]
  · refine UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun b hb ↦ ?_)
    have hv := pv (show msgBase + 8 * p + b < 16384 by simp only [msgBase]; omega)
    rw [readByte_getLsbD _ _ hb, trace_input _ _ _ (by rw [hv]; simp only [msgBase]; omega),
      Kind.inp, κ.target_msg hp hb, hu, Option.map_none, hv,
      ite_eq_right (by simp only [msgBase]; omega), ite_eq_left (by simp only [msgBase]; omega)]
    simp only [msgBase, show (512 + 8 * p + b - 512) / 8 = p by omega,
      show (512 + 8 * p + b - 512) % 8 = b by omega]

/-! ## The kinds of A.6 -/

/-- `stream`: digest-chain and key-leaf blocks after the first. -/
def streamKind (t : ℕ) (fin : Bool) : Kind := ⟨false, fun _ ↦ none, t, fin⟩

/-- `streamStart`: block 0 of a digest chain. -/
def streamStart : Kind := ⟨true, fun _ ↦ none, 64, false⟩

/-- `streamEnd41`: the key leaf's last block (a 41-byte tail). -/
def streamEnd41 : Kind := ⟨false, fun p ↦ if 41 ≤ p then some 0 else none, 4265, true⟩

/-- `hashA`: the leaf statement `tagLeaf ‖ h ‖ enc64 n` (41 bytes) in one block. -/
def hashA : Kind := ⟨true, fun p ↦ if p = 0 then some tagLeaf else if 41 ≤ p then some 0 else none,
  41, true⟩

/-- `hashB1`: the first block of a 65-byte hash with tag `tag` (`tagNode`, `tagWotsLeaf`,
`tagSigNode`). -/
def hashB1 (tag : UInt8) : Kind := ⟨true, fun p ↦ if p = 0 then some tag else none, 64, false⟩

/-- `hashB2`: the second block of a 65-byte hash (one byte, then zeros). -/
def hashB2 : Kind := ⟨false, fun p ↦ if 1 ≤ p then some 0 else none, 65, true⟩

/-- `w43`: a WOTS chain step `tagWots ‖ enc64 j ‖ i ‖ s ‖ x` (43 bytes), `i`, `s` per block. -/
def w43 (i s : UInt8) : Kind :=
  ⟨true, fun p ↦ if p = 0 then some tagWots else if p = 9 then some i else if p = 10 then some s
    else if 43 ≤ p then some 0 else none, 43, true⟩

theorem streamKind_target (t : ℕ) (fin : Bool) : (streamKind t fin).target = blockTarget t fin := by
  funext k
  rcases Nat.lt_or_ge k.val 1024 with h | h
  · rw [blockTarget_low h]
    simp only [Kind.target, streamKind, Bool.false_eq_true, ↓reduceIte, Option.map_none]
    split_ifs <;> rfl
  · exact (streamKind t fin).target_ge h

/-! ## Hashes of one and two blocks -/

private theorem msgBytes_length (w : Pos → Bool) : (msgBytes w).length = 64 := by
  simp [msgBytes]

/-- **One fresh block.** A block of a kind with `h_in = h0`, counter `L ∈ [1, 64]`, final, and the
message bytes from `L` pinned to `0` outputs the contract's BLAKE2s-256 of its first `L` message
bytes. -/
theorem one_block_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (κ : Kind)
    {L : ℕ} (hL : 1 ≤ L ∧ L ≤ 64) (hp : κ.h0Pin = true) (ht : κ.t = L) (hf : κ.fin = true)
    (hz : ∀ p, L ≤ p → p < 64 → κ.msgPin p = some 0) {w : Pos → Bool}
    (h : HoldsE (blockR1CS κ.target) (targetVal R κ.target) (liftBlock R w)) :
    readDigest w 256 = blake2sDigest ((msgBytes w).take L) := by
  have hl : ((msgBytes w).take L).length = L := by simp [msgBytes_length]; omega
  have hN : nBlocks L = 1 := by simp only [nBlocks]; omega
  rw [readDigest_hOut, κ.block_sound h, κ.hIn_eq_h0 hp h, blake2s_chain, hl, hN, chainState,
    chainState, hl, ctrAt, flagAt, hN, ite_eq_left rfl, ite_eq_left rfl, ht, hf, flagOf,
    ite_eq_left rfl,
    Nat.mul_zero, List.drop_zero]
  rw [block_congr (l := msgBytes w) (l' := (msgBytes w).take L) fun p hp64 ↦ ?_]
  rw [msgBytes_getD _ hp64, List.getD_eq_getElem?_getD, List.getElem?_take]
  rcases Nat.lt_or_ge p L with hpL | hpL
  · rw [ite_eq_left hpL, ← List.getD_eq_getElem?_getD, msgBytes_getD _ hp64]
  · rw [ite_eq_right (by omega)]
    exact κ.msgByte_eq hp64 (hz p hpL hp64) h

/-- **Two linked blocks.** A fresh first block (`h0`, counter `64`, not final) whose output is the
second block's `h_in`, the second block final with counter `L ∈ [65, 128]` and message bytes from
`L − 64` pinned to `0`: the second block outputs the contract's BLAKE2s-256 of the first block's
64 message bytes followed by the second's first `L − 64`. -/
theorem two_block_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (κ₁ κ₂ : Kind)
    {L : ℕ} (hL : 65 ≤ L ∧ L ≤ 128) (hp : κ₁.h0Pin = true) (ht₁ : κ₁.t = 64)
    (hf₁ : κ₁.fin = false) (ht₂ : κ₂.t = L) (hf₂ : κ₂.fin = true)
    (hz : ∀ p, L - 64 ≤ p → p < 64 → κ₂.msgPin p = some 0) {w₁ w₂ : Pos → Bool}
    (h₁ : HoldsE (blockR1CS κ₁.target) (targetVal R κ₁.target) (liftBlock R w₁))
    (h₂ : HoldsE (blockR1CS κ₂.target) (targetVal R κ₂.target) (liftBlock R w₂))
    (hl : ∀ j < 256, w₂ (pos j) = w₁ (pos (256 + j))) :
    readDigest w₂ 256 = blake2sDigest (msgBytes w₁ ++ (msgBytes w₂).take (L - 64)) := by
  set B := msgBytes w₁ ++ (msgBytes w₂).take (L - 64) with hB
  have hBl : B.length = L := by simp [hB, msgBytes_length]; omega
  have hN : nBlocks L = 2 := by simp only [nBlocks]; omega
  have hin : hIn w₂ = hOut w₁ :=
    hIn_of_bits fun j hj ↦ by rw [hl j hj, hOut_bit _ hj]
  have h1 : hOut w₁ = chainState B 1 := by
    rw [κ₁.block_sound h₁, κ₁.hIn_eq_h0 hp h₁]
    rw [chainState]
    rw [chainState]
    rw [ctrAt, flagAt]
    rw [hBl, hN]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [ht₁, hf₁, flagOf, ite_eq_right Bool.false_ne_true, Nat.mul_zero, List.drop_zero,
      show 64 * (0 + 1) = 64 from rfl, block_congr (l := msgBytes w₁) (l' := B) fun p hp64 ↦ ?_]
    rw [hB, List.getD_append _ _ _ _ (by rw [msgBytes_length]; omega)]
  rw [readDigest_hOut, κ₂.block_sound h₂, hin, blake2s_chain, hBl, hN, chainState, h1, hBl,
    ctrAt, flagAt, hN, ite_eq_left rfl, ite_eq_left rfl, ht₂, hf₂, flagOf, ite_eq_left rfl,
    block_congr (l := msgBytes w₂) (l' := B.drop (64 * 1)) fun p hp64 ↦ ?_]
  rw [hB, Nat.mul_one, List.drop_left' (msgBytes_length w₁), msgBytes_getD _ hp64,
    List.getD_eq_getElem?_getD, List.getElem?_take]
  rcases Nat.lt_or_ge p (L - 64) with hpL | hpL
  · rw [ite_eq_left hpL, ← List.getD_eq_getElem?_getD, msgBytes_getD _ hp64]
  · rw [ite_eq_right (by omega)]
    exact κ₂.msgByte_eq hp64 (hz p hpL hp64) h₂

/-! ## The statement hash (`hashStmt`'s blocks) -/

section HashStmt

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- **Block A.** A `hashA` block outputs the BLAKE2s-256 of its first 41 message bytes, whose
first is `tagLeaf`. -/
theorem hashA_sound {w : Pos → Bool}
    (h : HoldsE (blockR1CS hashA.target) (targetVal R hashA.target) (liftBlock R w)) :
    readDigest w 256 = blake2sDigest ((msgBytes w).take 41) ∧ readByte w msgBase = tagLeaf :=
  ⟨one_block_sound hashA (L := 41) (by omega) rfl rfl rfl
      (fun p hp _ ↦ by simp [hashA, show p ≠ 0 by omega, hp]) h,
    by simpa using hashA.msgByte_eq (p := 0) (by omega) rfl h⟩

/-- Block A with its message bytes `tagLeaf ‖ h ‖ enc64 n` outputs `leafStmt h n`. -/
theorem hashA_leafStmt {w : Pos → Bool}
    (h : HoldsE (blockR1CS hashA.target) (targetVal R hashA.target) (liftBlock R w))
    {d : Digest} {n : ℕ} (hm : (msgBytes w).take 41 = tagLeaf :: d.toList ++ enc64 n) :
    readDigest w 256 = leafStmt d n := by
  rw [(hashA_sound h).1, hm]
  rfl

/-- **Blocks B1, B2.** A `hashB1 tag` block linked to a `hashB2` block: the second outputs the
BLAKE2s-256 of the 64 message bytes of the first and the first message byte of the second; the
first message byte of B1 is `tag`. -/
theorem hashB_sound {tag : UInt8} {w₁ w₂ : Pos → Bool}
    (h₁ : HoldsE (blockR1CS (hashB1 tag).target) (targetVal R (hashB1 tag).target)
      (liftBlock R w₁))
    (h₂ : HoldsE (blockR1CS hashB2.target) (targetVal R hashB2.target) (liftBlock R w₂))
    (hl : ∀ j < 256, w₂ (pos j) = w₁ (pos (256 + j))) :
    readDigest w₂ 256 = blake2sDigest (msgBytes w₁ ++ (msgBytes w₂).take 1) ∧
      readByte w₁ msgBase = tag :=
  ⟨two_block_sound (hashB1 tag) hashB2 (L := 65) (by omega) rfl rfl rfl rfl rfl
      (fun p hp _ ↦ by simp [hashB2, show 1 ≤ p by omega]) h₁ h₂ hl,
    by simpa using (hashB1 tag).msgByte_eq (p := 0) (by omega) rfl h₁⟩

/-- Blocks B1, B2 with message bytes `tagNode ‖ c₁ ‖ c₂` output `nodeStmt c₁ c₂`. -/
theorem hashB_nodeStmt {w₁ w₂ : Pos → Bool}
    (h₁ : HoldsE (blockR1CS (hashB1 tagNode).target) (targetVal R (hashB1 tagNode).target)
      (liftBlock R w₁))
    (h₂ : HoldsE (blockR1CS hashB2.target) (targetVal R hashB2.target) (liftBlock R w₂))
    (hl : ∀ j < 256, w₂ (pos j) = w₁ (pos (256 + j))) {c₁ c₂ : Digest}
    (hm : msgBytes w₁ ++ (msgBytes w₂).take 1 = tagNode :: c₁.toList ++ c₂.toList) :
    readDigest w₂ 256 = nodeStmt c₁ c₂ := by
  rw [(hashB_sound h₁ h₂ hl).1, hm]
  rfl

end HashStmt

/-! ## The dump (A.6's KAT) -/

/-- The rows of `A₀^kind`, `B₀^kind` and the target bit `E`, position by position, with the
circuit's gates recorded from `base` (`gateBase` for the entry; the argument keeps the circuit out
of closed-term extraction). -/
def kindRows (base : ℕ) (tgt : Target) : List (Gate Blake2sCircuit.m × Bool) :=
  let c := blockAt base
  let l := c.gates.toList
  (List.finRange (2 ^ Blake2sCircuit.m)).map fun k ↦
    (if (tgt k).isSome then ⟨0, 0⟩ else c.rowOfList l k, (tgt k).getD false)

/-- The dumped rows are the kind's block matrices and target. -/
theorem kindRows_eq (tgt : Target) :
    kindRows gateBase tgt = (List.finRange (2 ^ Blake2sCircuit.m)).map fun k ↦
      (if (tgt k).isSome then ⟨0, 0⟩ else blake2sCircuit.rowOf k, (tgt k).getD false) := by
  unfold kindRows
  rw [blockAt_eq]
  rfl

/-- The matrices of `blockR1CS tgt` are the dumped rows' forms. -/
theorem blockR1CS_rows (tgt : Target) (k j : Pos) :
    (blockR1CS tgt).A k j =
        (if (tgt k).isSome then (⟨0, 0⟩ : Gate _) else blake2sCircuit.rowOf k).a.getLsbD j ∧
      (blockR1CS tgt).B k j =
        (if (tgt k).isSome then (⟨0, 0⟩ : Gate _) else blake2sCircuit.rowOf k).b.getLsbD j := by
  rcases h : tgt k with _ | b <;> simp [blockR1CS, circuitR1CS, toBlockR1CS, h]

/-- A dump line: `k <a-form> <b-form> <E bit>`. -/
def kindLine (k : ℕ) (r : Gate Blake2sCircuit.m × Bool) : String :=
  rowLine k r.1 ++ " " ++ (if r.2 then "1" else "0")

/-- Every kind of A.6 with one sample block (per-block values: the stream's `t = 64`, not final;
`w43`'s `i = s = 0`). -/
def allKinds : List (String × Target) :=
  [("chain", Chain.chainTarget), ("stream", blockTarget 64 false),
    ("streamStart", streamStart.target), ("streamEnd41", streamEnd41.target),
    ("hashA", hashA.target), ("hashB1", (hashB1 tagNode).target), ("hashB2", hashB2.target),
    ("w43", (w43 0 0).target)]

end Kinds

end FR
