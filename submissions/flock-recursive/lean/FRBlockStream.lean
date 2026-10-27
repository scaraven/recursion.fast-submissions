-- New for `flock-recursive` (BLUEPRINT §1.2, §4.2, Appendix A.2, A.6, revision 3.1).
import RecursionFast.Contract.Signature
import FRBlockLayout

/-!
# The stream block and the digest chain (BLUEPRINT §4.2)

**The digest chain** of a byte string `B` of length `L` (`blake2s_chain`, kernel-checked against the
contract's BLAKE2s): `N = nBlocks L = ⌊(L − 1)/64⌋ + 1` compressions from `h0`,
`hᵢ₊₁ = compress hᵢ (block (B.drop 64i)) (ctrAt L i) (flagAt L i) 0`, where the counter is `64(i+1)`
and the flag `0` except at the last block (`L`, `0xFFFFFFFF`); `blake2sDigest B = le h_N`. The
contract's trace digest is the case `B = 0x54 ‖ traceBytes tr` (`traceDigest_chain`).

**The stream block** is the block R1CS of `FRBlockLayout` with the public target
`streamTarget L i` of block `i` of a stream of length `L` (BLUEPRINT revision 3.1, §4.2): `(0, 0)`
rows pin the counter `ctrAt L i` in `t_lo`, `t_hi`, the flag `flagAt L i` in `f0`, `f1 = 0` and
`one = 1`; `h_in` and the message are inputs. Block `i` holds stream bytes `[64i, 64i + 64)` in its
message slots: stream byte `p` is message byte `p mod 64` of block `⌊p/64⌋` (`streamBytes`), so the
stream's 16-byte element `e` is message slot `4 + e mod 4` of block `⌊e/4⌋` (`elem_slot`).

Results:
* `block_sound_gen`: a Boolean block satisfying the block R1CS with the target `blockTarget t fin`
  (any counter `t`, any final flag) carries the compression of its `h_in` and message with that
  counter and flag; `block_sound` is the case of block `i` of a stream (for the node's statement
  hash, the cases `(41, final)`, `(64, ¬ final)`, `(65, final)`);
* `stream_sound`: `N` such blocks, starting from `h_in = h0`, linked `h_out(i) = h_in(i+1)` (both
  the shift argument's content) and zero past `L` bytes (`Padded`: point claims on `f`), carry at
  the last block's `h_out` the contract's `blake2sDigest` of the bytes in their message slots;
  `stream_traceDigest`: when those bytes are `0x54 ‖ traceBytes tr`, it is `traceDigest tr`;
* `item_aligned`: with a 7-byte tag on the first query and 8-byte tags on the others (A.2), every
  item after the first, and every payload, starts at an offset `≡ 0 mod 16` of `0x54 ‖ traceBytes`;
* controls: `stream_complete` (the honest blocks of any stream meet every hypothesis of
  `stream_sound`), `zero_control` (the all-zero block fails the target).
-/

namespace FR

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit Block

namespace Stream

/-! ## The digest chain of a byte string -/

/-- The number of compressions of an input of `L` bytes, `max 1 ⌈L/64⌉` (RFC 7693 §3.3). -/
def nBlocks (L : ℕ) : ℕ := (L - 1) / 64 + 1

/-- The counter of compression `i` of an input of `L` bytes: `64 (i + 1)`, or `L` at the last. -/
def ctrAt (L i : ℕ) : ℕ := if i + 1 = nBlocks L then L else 64 * (i + 1)

/-- The last-block flag of compression `i`: `0xFFFFFFFF` at the last, else `0`. -/
def flagAt (L i : ℕ) : UInt32 := if i + 1 = nBlocks L then 0xFFFFFFFF else 0

/-- The chaining value after `j` compressions of `B`. -/
def chainState (B : List UInt8) : ℕ → Vector UInt32 8
  | 0 => h0
  | j + 1 => compress (chainState B j) (block (B.drop (64 * j))) (ctrAt B.length j).toUInt64
      (flagAt B.length j) 0

/-- RFC 7693's block loop from compression `j` on is the chain from `j`. -/
theorem compressInput_eq (B : List UInt8) :
    ∀ n j, j + n + 1 = nBlocks B.length →
      compressInput (chainState B j) (64 * j) (B.drop (64 * j)) n = chainState B (j + n + 1) := by
  intro n
  induction n with
  | zero =>
    intro j hj
    have hL : 64 * j + (B.drop (64 * j)).length = B.length := by
      simp only [List.length_drop, nBlocks] at hj ⊢
      omega
    rw [compressInput, hL, Nat.add_zero, chainState, ctrAt, flagAt, ite_eq_left hj, ite_eq_left hj]
  | succ n ih =>
    intro j hj
    have hne : ¬ j + 1 = nBlocks B.length := by omega
    rw [compressInput, List.drop_drop, show 64 * j + 64 = 64 * (j + 1) by omega]
    have hs : compress (chainState B j) (block (B.drop (64 * j))) (64 * (j + 1)).toUInt64 0 0 =
        chainState B (j + 1) := by
      rw [chainState, ctrAt, flagAt, ite_eq_right hne, ite_eq_right hne]
    rw [hs, ih (j + 1) (by omega)]
    congr 1
    omega

/-- **The digest chain.** The contract's BLAKE2s-256 of a byte string is the little-endian encoding
of the chaining value after its `nBlocks` compressions. -/
theorem blake2s_chain (B : List UInt8) :
    blake2sDigest B = leDigest (chainState B (nBlocks B.length)) := by
  have h := compressInput_eq B ((B.length - 1) / 64) 0 (by simp [nBlocks])
  rw [show chainState B 0 = h0 from rfl, Nat.mul_zero, List.drop_zero, Nat.zero_add] at h
  rw [blake2sDigest_eq, h, nBlocks]

/-- **The trace digest** is the digest chain of `0x54 ‖ traceBytes tr`. -/
theorem traceDigest_chain (tr : Trace) :
    traceDigest tr = leDigest (chainState (tagTrace :: traceBytes tr)
      (nBlocks (tagTrace :: traceBytes tr).length)) :=
  blake2s_chain _

/-! ## The stream block -/

/-- The last-block flag word: `0xFFFFFFFF` for a final block, `0` otherwise. -/
def flagOf (fin : Bool) : UInt32 := if fin then 0xFFFFFFFF else 0

theorem flagAt_eq (L i : ℕ) : flagAt L i = flagOf (decide (i + 1 = nBlocks L)) := by
  unfold flagAt flagOf
  split_ifs <;> simp_all

/-- The public target of a stream block with counter `t` and final flag `fin`: `t` in `t_lo`,
`t_hi`, `flagOf fin` in `f0`, `f1 = 0`, `one = 1`; `h_in` and the message are inputs. Block `i` of
a stream of `L` bytes uses `(ctrAt L i, i + 1 = nBlocks L)` (`streamTarget`); the node's statement
hash uses `(41, final)`, `(64, ¬ final)`, `(65, final)` (BLUEPRINT §4.2). -/
def blockTarget (t : ℕ) (fin : Bool) (k : Pos) : Option Bool :=
  if k.val < 1024 then none
  else if k.val < 1056 then some (t.toUInt64.toUInt32.toBitVec.getLsbD (k.val - 1024))
  else if k.val < 1088 then some ((t.toUInt64 >>> 32).toUInt32.toBitVec.getLsbD (k.val - 1056))
  else if k.val < 1120 then some fin
  else if k.val < 1152 then some false
  else if k.val = 1152 then some true
  else none

/-- The public target of block `i` of a stream of `L` bytes. -/
def streamTarget (L i : ℕ) : Target := blockTarget (ctrAt L i) (decide (i + 1 = nBlocks L))

private theorem pv {v : ℕ} (h : v < 16384) : ((pos v : Pos) : ℕ) = v := pos_val h

section Pins

variable {t : ℕ} {fin : Bool}

theorem pat_tlo : ∀ j < 32, blockTarget t fin (pos (counterLo + j)) =
    some (t.toUInt64.toUInt32.toBitVec.getLsbD j) := fun j hj ↦ by
  simp (disch := omega) only [blockTarget, counterLo, pv (show 1024 + j < 16384 by omega),
    ite_eq_left, ite_eq_right, Nat.add_sub_cancel_left]

theorem pat_thi : ∀ j < 32, blockTarget t fin (pos (counterHi + j)) =
    some ((t.toUInt64 >>> 32).toUInt32.toBitVec.getLsbD j) := fun j hj ↦ by
  simp (disch := omega) only [blockTarget, counterHi, pv (show 1056 + j < 16384 by omega),
    ite_eq_left, ite_eq_right, Nat.add_sub_cancel_left]

private theorem ones_getLsbD : ∀ i : Fin 32, (0xFFFFFFFF : UInt32).toBitVec.getLsbD i = true := by
  decide

theorem pat_f0 : ∀ j < 32, blockTarget t fin (pos (finalFlag + j)) =
    some ((flagOf fin).toBitVec.getLsbD j) := fun j hj ↦ by
  simp (disch := omega) only [blockTarget, finalFlag, pv (show 1088 + j < 16384 by omega),
    ite_eq_left, ite_eq_right]
  cases fin
  · simp [flagOf]
  · rw [flagOf, ite_eq_left rfl, ones_getLsbD ⟨j, hj⟩]

theorem pat_f1 : ∀ j < 32, blockTarget t fin (pos (lastNodeFlag + j)) =
    some ((0 : UInt32).toBitVec.getLsbD j) := fun j hj ↦ by
  simp (disch := omega) only [blockTarget, lastNodeFlag, pv (show 1120 + j < 16384 by omega),
    UInt32.toBitVec_zero, BitVec.getLsbD_zero, ite_eq_left, ite_eq_right]

/-- The target pins `one` to `1` and otherwise only inputs (`t`, `f`). -/
theorem blockTarget_ok : TargetOk (blockTarget t fin) := by
  refine ⟨by rw [blockTarget, onePos_val]; rfl, fun k b h ↦ ?_⟩
  rw [← Fin.val_inj, onePos_val]
  by_contra hk
  rcases Nat.lt_or_ge k.val 1024 with h2 | h2
  · rw [blockTarget, ite_eq_left h2] at h
    cases h
  · simp (disch := omega) only [blockTarget, ite_eq_right, reduceCtorEq] at h

/-- The target pins no position below `1024` (`h_in`, `h_out`, the message). -/
theorem blockTarget_low {k : Pos} (hk : k.val < 1024) : blockTarget t fin k = none := by
  rw [blockTarget, ite_eq_left hk]

/-- **A stream block, soundness.** A Boolean block satisfying the block R1CS with the target of
counter `t` and final flag `fin`, over a nontrivial ring of characteristic two, carries at `h_out`
the compression of its `h_in` and its message with that counter and flag. -/
theorem block_sound_gen {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {w : Pos → Bool}
    (h : HoldsE (blockR1CS (blockTarget t fin)) (targetVal R (blockTarget t fin)) (liftBlock R w)) :
    hOut w = compress (hIn w) (block (msgBytes w)) t.toUInt64 (flagOf fin) 0 :=
  have ⟨hz, h1, hp⟩ := holdsE_sound blockTarget_ok h
  compress_sound hz h1 rfl rfl (readWord_of_meets hp pat_tlo) (readWord_of_meets hp pat_thi)
    (readWord_of_meets hp pat_f0) (readWord_of_meets hp pat_f1)

end Pins

theorem streamTarget_ok {L i : ℕ} : TargetOk (streamTarget L i) := blockTarget_ok

theorem streamTarget_low {L i : ℕ} {k : Pos} (hk : k.val < 1024) : streamTarget L i k = none :=
  blockTarget_low hk

/-- **The stream block, soundness.** A Boolean block satisfying the block R1CS with the target of
block `i` of a stream of `L` bytes carries at `h_out` the compression of its `h_in` and its message
with that block's counter and flag. -/
theorem block_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {L i : ℕ} {w : Pos → Bool}
    (h : HoldsE (blockR1CS (streamTarget L i)) (targetVal R (streamTarget L i)) (liftBlock R w)) :
    hOut w = compress (hIn w) (block (msgBytes w)) (ctrAt L i).toUInt64 (flagAt L i) 0 := by
  rw [block_sound_gen h, flagAt_eq]

/-! ## A stream of blocks -/

/-- The stream a family of blocks holds in its message slots: byte `p < L` is message byte
`p mod 64` of block `⌊p / 64⌋`. -/
def streamBytes (w : ℕ → Pos → Bool) (L : ℕ) : List UInt8 :=
  (List.range L).map fun p ↦ readByte (w (p / 64)) (msgBase + 8 * (p % 64))

theorem streamBytes_length (w : ℕ → Pos → Bool) (L : ℕ) : (streamBytes w L).length = L := by
  simp [streamBytes]

/-- The 16-byte element `e` of the stream (bytes `16e … 16e + 15`) is message slot `4 + e mod 4`
(bits `128 (4 + e mod 4) …`) of block `⌊e / 4⌋`: the address rule of BLUEPRINT §4.2. -/
theorem elem_slot (e r : ℕ) (hr : r < 16) :
    (16 * e + r) / 64 = e / 4 ∧ msgBase + 8 * ((16 * e + r) % 64) = 128 * (4 + e % 4) + 8 * r := by
  simp only [msgBase]
  omega

/-- The stream's padding: the message bytes of its blocks past its `L` bytes are `0`. -/
def Padded (w : ℕ → Pos → Bool) (L : ℕ) : Prop :=
  ∀ p, L ≤ p → p < 64 * nBlocks L → readByte (w (p / 64)) (msgBase + 8 * (p % 64)) = 0

/-- The message bytes of block `i` of a padded stream are the stream's bytes from `64 i`, zero
past its end. -/
theorem msg_eq {L i : ℕ} {w : ℕ → Pos → Bool} (hpad : Padded w L) (hi : i < nBlocks L) :
    block (msgBytes (w i)) = block ((streamBytes w L).drop (64 * i)) := by
  refine block_congr fun p hp64 ↦ ?_
  rw [msgBytes_getD _ hp64, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rcases Nat.lt_or_ge (64 * i + p) L with hlt | hge
  · rw [List.getElem?_eq_getElem (by rw [streamBytes_length]; omega), Option.getD_some]
    simp only [streamBytes, List.getElem_map, List.getElem_range]
    rw [show (64 * i + p) / 64 = i by omega, show (64 * i + p) % 64 = p by omega]
  · rw [List.getElem?_eq_none (by rw [streamBytes_length]; omega), Option.getD_none]
    have := hpad (64 * i + p) hge (by omega)
    rwa [show (64 * i + p) / 64 = i by omega, show (64 * i + p) % 64 = p by omega] at this

/-- **A stream of blocks.** `N = nBlocks L` Boolean blocks satisfying the block R1CS with their
stream targets, starting from `h_in = h0`, linked `h_out(i) = h_in(i + 1)` (the shift argument's
content) and padded with zeros past `L` bytes (point claims), carry at the last block's `h_out`
the contract's BLAKE2s-256 of the `L` bytes in their message slots. -/
theorem stream_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (L : ℕ)
    (w : ℕ → Pos → Bool)
    (hE : ∀ i < nBlocks L,
      HoldsE (blockR1CS (streamTarget L i)) (targetVal R (streamTarget L i)) (liftBlock R (w i)))
    (hstart : ∀ j < 256, w 0 (pos j) = wordsBit h0 j)
    (hl : ∀ i, i + 1 < nBlocks L → ∀ j < 256, w (i + 1) (pos j) = w i (pos (256 + j)))
    (hpad : Padded w L) :
    readDigest (w (nBlocks L - 1)) 256 = blake2sDigest (streamBytes w L) := by
  set B := streamBytes w L with hB
  have hBl : B.length = L := streamBytes_length w L
  have hs : ∀ j, chainState B (j + 1) =
      compress (chainState B j) (block (B.drop (64 * j))) (ctrAt L j).toUInt64 (flagAt L j) 0 :=
    fun j ↦ by rw [chainState, hBl]
  have key : ∀ i < nBlocks L, hIn (w i) = chainState B i ∧ hOut (w i) = chainState B (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro h0'
      have hin : hIn (w 0) = chainState B 0 := hIn_of_bits hstart
      refine ⟨hin, ?_⟩
      rw [block_sound (hE 0 h0'), hin, msg_eq hpad h0', ← hB]
      exact (hs 0).symm
    | succ i ih =>
      intro hi
      have hin : hIn (w (i + 1)) = chainState B (i + 1) := hIn_of_bits fun j hj ↦ by
        rw [hl i hi j hj, ← hOut_bit (w i) hj, (ih (by omega)).2]
      refine ⟨hin, ?_⟩
      rw [block_sound (hE _ hi), hin, msg_eq hpad hi, ← hB]
      exact (hs (i + 1)).symm
  have hN : nBlocks L - 1 + 1 = nBlocks L := by simp [nBlocks]
  rw [readDigest_hOut, (key _ (by simp [nBlocks])).2, hN, blake2s_chain, hBl]

/-- **The trace digest of a stream.** When the stream in the blocks' message slots is
`0x54 ‖ traceBytes tr`, the last block's `h_out` carries `traceDigest tr`. -/
theorem stream_traceDigest {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (L : ℕ)
    (w : ℕ → Pos → Bool)
    (hE : ∀ i < nBlocks L,
      HoldsE (blockR1CS (streamTarget L i)) (targetVal R (streamTarget L i)) (liftBlock R (w i)))
    (hstart : ∀ j < 256, w 0 (pos j) = wordsBit h0 j)
    (hl : ∀ i, i + 1 < nBlocks L → ∀ j < 256, w (i + 1) (pos j) = w i (pos (256 + j)))
    (hpad : Padded w L) (tr : Trace) (htr : streamBytes w L = tagTrace :: traceBytes tr) :
    readDigest (w (nBlocks L - 1)) 256 = traceDigest tr := by
  rw [stream_sound L w hE hstart hl hpad, htr, traceDigest]

/-! ## Alignment of the hashed trace (BLUEPRINT §1.2, A.2) -/

/-- The bytes of one trace item: `enc64 |q| ‖ q ‖ a`. -/
theorem traceBytes_cons (e : ByteArray × Digest) (tr : Trace) :
    traceBytes (e :: tr) = enc64 e.1.size ++ e.1.data.toList ++ e.2.toList ++ traceBytes tr := by
  simp [traceBytes, List.append_assoc]

theorem traceBytes_length_cons (e : ByteArray × Digest) (tr : Trace) :
    (traceBytes (e :: tr)).length = 8 + e.1.size + 32 + (traceBytes tr).length := by
  rw [traceBytes_cons]
  simp only [List.length_append, enc64, List.length_ofFn, Array.length_toList, ByteArray.size_data,
    Vector.length_toList]

/-- **Alignment.** If the first query has size `≡ 7 mod 16` (the 7-byte seed tag and a payload of
`16`-byte elements) and every other query `≡ 8 mod 16`, then in the stream `0x54 ‖ traceBytes tr`
the first item's payload starts at offset `16`, and every later item, hence its payload (at `+16`)
and its answer, starts at an offset `≡ 0 mod 16`. -/
theorem item_aligned (e₀ : ByteArray × Digest) (rest : Trace) (h₀ : e₀.1.size % 16 = 7)
    (hr : ∀ e ∈ rest, e.1.size % 16 = 8) :
    1 + 8 + 7 = 16 ∧ ∀ k ≤ rest.length,
      (1 + (traceBytes (e₀ :: rest.take k)).length) % 16 = 0 := by
  refine ⟨rfl, fun k _ ↦ ?_⟩
  rw [traceBytes_length_cons]
  suffices h : ∀ (l : Trace), (∀ e ∈ l, e.1.size % 16 = 8) → (traceBytes l).length % 16 = 0 by
    have := h (rest.take k) fun e he ↦ hr e (List.mem_of_mem_take he)
    omega
  intro l hl
  induction l with
  | nil => simp [traceBytes]
  | cons e l ih =>
    rw [traceBytes_length_cons]
    have := hl e List.mem_cons_self
    have := ih fun e he ↦ hl e (List.mem_cons_of_mem _ he)
    omega

/-! ## Completeness of a stream (a control) -/

/-- The input of block `i` of the stream `B`: the target's bits where it pins; the chaining value
`chainState B i` at `h_in`; the stream's bytes `[64 i, 64 i + 64)` in the message, zero past its
end. -/
def streamInp (B : List UInt8) (i : ℕ) (k : Pos) : Bool :=
  match streamTarget B.length i k with
  | some b => b
  | none =>
    if k.val < 256 then wordsBit (chainState B i) k.val
    else if msgBase ≤ k.val ∧ k.val < msgBase + 512 then
      (B.getD (64 * i + (k.val - msgBase) / 8) 0).toBitVec.getLsbD ((k.val - msgBase) % 8)
    else false

/-- The honest block `i` of the stream `B`. -/
noncomputable def streamTrace (B : List UInt8) (i : ℕ) : Pos → Bool :=
  blake2sCircuit.traceF (streamInp B i)

private theorem streamTrace_input (B : List UInt8) (i : ℕ) {k : Pos}
    (hk : k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152)) : streamTrace B i k = streamInp B i k :=
  traceF_input bounded_blake2s _
    (by rw [blake2sCircuit_inputs, getLsbD_inputs]; exact decide_eq_true hk)
    (by rw [blake2sCircuit_cpos]; exact Fin.ne_of_val_ne (by rw [constPos_val]; omega))

private theorem streamTrace_hIn_bit (B : List UInt8) (i : ℕ) {j : ℕ} (hj : j < 256) :
    streamTrace B i (pos j) = wordsBit (chainState B i) j := by
  have hv : ((pos j : Pos) : ℕ) = j := pv (by omega)
  rw [streamTrace_input _ _ (by rw [hv]; omega), streamInp,
    streamTarget_low (by rw [hv]; omega), hv, ite_eq_left hj]

private theorem streamTrace_byte (B : List UInt8) (i : ℕ) {p : ℕ} (hp : p < 64) :
    readByte (streamTrace B i) (msgBase + 8 * p) = B.getD (64 * i + p) 0 := by
  refine UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun b hb ↦ ?_)
  have hv : msgBase + 8 * p + b < 16384 := by simp only [msgBase]; omega
  rw [readByte_getLsbD _ _ hb, streamTrace_input _ _ (by rw [pv hv]; simp only [msgBase]; omega),
    streamInp, streamTarget_low (by rw [pv hv]; simp only [msgBase]; omega), pv hv,
    ite_eq_right (by simp only [msgBase]; omega), ite_eq_left (by simp only [msgBase]; omega)]
  have e1 : (msgBase + 8 * p + b - msgBase) / 8 = p := by simp only [msgBase]; omega
  have e2 : (msgBase + 8 * p + b - msgBase) % 8 = b := by simp only [msgBase]; omega
  rw [e1, e2]

/-- **Stream completeness (a control).** The honest blocks of a stream `B` satisfy every
hypothesis of `stream_sound` for `L = |B|` and hold `B` in their message slots; so
`stream_sound`'s hypotheses are satisfiable for every stream. -/
theorem stream_complete {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (B : List UInt8) :
    (∀ i, HoldsE (blockR1CS (streamTarget B.length i)) (targetVal R (streamTarget B.length i))
        (liftBlock R (streamTrace B i))) ∧
      (∀ j < 256, streamTrace B 0 (pos j) = wordsBit h0 j) ∧
      (∀ i, ∀ j < 256, streamTrace B (i + 1) (pos j) = streamTrace B i (pos (256 + j))) ∧
      Padded (streamTrace B) B.length ∧ streamBytes (streamTrace B) B.length = B := by
  have hz : ∀ i, circuitR1CS.Holds (liftBlock R (streamTrace B i)) := fun i ↦
    (trace_satisfies (R := R) bounded_blake2s (streamInp B i)).1
  have h1 : ∀ i, streamTrace B i onePos = true := fun i ↦ by
    rw [streamTrace, onePos, ← blake2sCircuit_cpos]; exact traceF_cpos bounded_blake2s _
  have hp : ∀ i, MeetsB (streamTarget B.length i) (streamTrace B i) := fun i k b hk ↦ by
    rcases streamTarget_ok.2 k b hk with rfl | hin
    · exact Option.some.inj (streamTarget_ok.1.symm.trans hk) ▸ h1 i
    · rw [streamTrace_input B i hin, streamInp, hk]
  have hE : ∀ i, HoldsE (blockR1CS (streamTarget B.length i))
      (targetVal R (streamTarget B.length i)) (liftBlock R (streamTrace B i)) := fun i ↦
    holdsE_complete (hz i) (hp i)
  have hout : ∀ i, hOut (streamTrace B i) = chainState B (i + 1) := fun i ↦ by
    rw [block_sound (hE i), hIn_of_bits fun j hj ↦ streamTrace_hIn_bit B i hj]
    have hm : block (msgBytes (streamTrace B i)) = block (B.drop (64 * i)) :=
      block_congr fun p hp64 ↦ by
        rw [msgBytes_getD _ hp64, streamTrace_byte _ _ hp64, List.getD_eq_getElem?_getD,
          List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [hm]
    rfl
  refine ⟨hE, fun j hj ↦ streamTrace_hIn_bit B 0 hj, fun i j hj ↦ ?_, fun p hp _ ↦ ?_, ?_⟩
  · rw [streamTrace_hIn_bit B (i + 1) hj, ← hout i, hOut_bit _ hj]
  · rw [streamTrace_byte _ _ (Nat.mod_lt _ (by omega)), show 64 * (p / 64) + p % 64 = p by omega,
      List.getD_eq_default _ _ hp]
  · refine List.ext_getElem (streamBytes_length _ _) fun p hp _ ↦ ?_
    rw [streamBytes_length] at hp
    simp only [streamBytes, List.getElem_map, List.getElem_range]
    rw [streamTrace_byte _ _ (Nat.mod_lt _ (by omega)), show 64 * (p / 64) + p % 64 = p by omega,
      List.getD_eq_getElem _ _ hp]

/-- **Negative control (BP-C-M5).** The all-zero block satisfies the circuit's R1CS (with
`one = 0`) but not the block R1CS with a stream target. -/
theorem zero_control {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {L i : ℕ} :
    circuitR1CS.Holds (fun _ : Pos ↦ (0 : R)) ∧
      ¬ HoldsE (blockR1CS (streamTarget L i)) (targetVal R (streamTarget L i)) (fun _ ↦ (0 : R)) :=
  ⟨zero_holds, zero_not_holdsE streamTarget_ok⟩

end Stream

end FR
