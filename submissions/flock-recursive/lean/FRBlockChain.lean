-- New for `flock-recursive` (BLUEPRINT §4.1, Appendix A.6, revision 3.1). `stepWords`,
-- `chainStep_eq`, `not_holds_flip` and the known-answer controls are adapted from
-- `submissions/spartan-srom/lean/SpartanSromBlake2sR1CS.lean` (this repository, branch
-- `v4/flock-recursive` at `783328c`): there the constants were rows `(one, one)` of the block,
-- here they are `(0, 0)` rows pinned by the public target.
import FRBlockLayout

/-!
# The chain block (BLUEPRINT §4.1)

The chain step of the contract, `chainStep d = blake2sDigest (0x43 ‖ d)` (33 bytes), is one
compression: chaining value `h0`, message block `0x43 ‖ d ‖ 0^31`, counter `33`, the last-block flag
`0xFFFFFFFF`, the last-node flag `0` (`chainStep_eq`). The chain block is the block R1CS of
`FRBlockLayout` with the **public target** `chainTarget`, whose `(0, 0)` rows pin:

* `h_in = h0` (`0 … 255`), the tag byte `0x43` (`512 … 519`), the zero message bytes `33 … 63`
  (`776 … 1023`), `t_lo = 33`, `t_hi = 0`, `f0 = 0xFFFFFFFF`, `f1 = 0` (`1024 … 1151`), and
  `one = 1` (`1152`);
* free: the digest `d` being hashed, message bytes `1 … 32`, bits `520 … 775` (`dBase`).

Results:
* `block_sound`: a Boolean block satisfying the chain block's R1CS with its target
  (`HoldsE (blockR1CS chainTarget) (targetVal R chainTarget)`) carries at `256 … 511` the chain
  step of the digest at `520 … 775`;
* `block_complete`: the honest block of a digest (`chainTrace`) satisfies it and carries the digest
  and its chain step;
* controls: `chainStep_zero_kat` and `chainTrace_zero_kat` (positive: the contract's BLAKE2s on
  one block), `not_holds_flip` (negative: an output bit flipped breaks the R1CS),
  `zero_control` (negative, BP-C-M5: the all-zero block, which satisfies the circuit's R1CS
  with `one = 0`, fails the target).
-/

namespace FR

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit Block

namespace Chain

/-! ## The chain step as one compression -/

/-- The first position of the digest a chain block hashes: message byte `1`, bit `520`. -/
abbrev dBase : ℕ := 520

/-- The compression that a chain step is: chaining value `h0`, message block `0x43 ‖ d`, counter
`33`, the last-block flag set and the last-node flag clear. -/
def stepWords (d : Digest) : Vector UInt32 8 :=
  compress h0 (block (tagChain :: d.toList)) 33 0xFFFFFFFF 0

/-- The chain step of the contract is one compression (`(33 - 1) / 64 = 0` blocks before the
final one), encoded little-endian. -/
theorem chainStep_eq (d : Digest) : chainStep d = leDigest (stepWords d) := by
  have hlen : (tagChain :: d.toList).length = 33 := by simp
  rw [chainStep, blake2sDigest_eq, hlen, show (33 - 1) / 64 = 0 from rfl, compressInput, hlen]
  rfl

/-! ## The target -/

/-- The public target of a chain block: `h_in = h0`, message byte `0` is `0x43`, message bytes
`33 … 63` are `0`, `t_lo = 33`, `t_hi = 0`, `f0 = 0xFFFFFFFF`, `f1 = 0`, `one = 1`. -/
def chainTarget (k : Pos) : Option Bool :=
  if k.val < 256 then some (wordsBit h0 k.val)
  else if k.val < 512 then none
  else if k.val < 520 then some (tagChain.toBitVec.getLsbD (k.val - 512))
  else if k.val < 776 then none
  else if k.val < 1024 then some false
  else if k.val < 1056 then some ((33 : UInt32).toBitVec.getLsbD (k.val - 1024))
  else if k.val < 1088 then some false
  else if k.val < 1120 then some true
  else if k.val < 1152 then some false
  else if k.val = 1152 then some true
  else none

private theorem pv {v : ℕ} (h : v < 16384) : ((pos v : Pos) : ℕ) = v := pos_val h

theorem pat_h0 : ∀ j < 256, chainTarget (pos j) = some (wordsBit h0 j) := fun j hj ↦ by
  rw [chainTarget, pv (by omega), ite_eq_left hj]

theorem pat_tag : ∀ i < 8, chainTarget (pos (msgBase + i)) = some (tagChain.toBitVec.getLsbD i) :=
  fun i hi ↦ by
    simp (disch := omega) only [chainTarget, msgBase, pv (show 512 + i < 16384 by omega),
      ite_eq_left, ite_eq_right, Nat.add_sub_cancel_left]

theorem pat_pad {v : ℕ} (h1 : 776 ≤ v) (h2 : v < 1024) : chainTarget (pos v) = some false := by
  simp (disch := omega) only [chainTarget, pv (show v < 16384 by omega), ite_eq_left,
    ite_eq_right]

theorem pat_tlo : ∀ i < 32, chainTarget (pos (counterLo + i)) =
    some ((33 : UInt64).toUInt32.toBitVec.getLsbD i) := fun i hi ↦ by
  simp (disch := omega) only [chainTarget, counterLo, pv (show 1024 + i < 16384 by omega),
    ite_eq_left, ite_eq_right, Nat.add_sub_cancel_left]
  rfl

theorem pat_zero {b : ℕ} (hb : b = counterHi ∨ b = lastNodeFlag) :
    ∀ i < 32, chainTarget (pos (b + i)) = some ((0 : UInt32).toBitVec.getLsbD i) := fun i hi ↦ by
  simp only [counterHi, lastNodeFlag] at hb
  simp only [chainTarget, pv (show b + i < 16384 by omega), UInt32.toBitVec_zero,
    BitVec.getLsbD_zero]
  rcases hb with rfl | rfl
  · simp (disch := omega) only [ite_eq_left, ite_eq_right]
  · simp (disch := omega) only [ite_eq_left, ite_eq_right]

private theorem ones_getLsbD : ∀ i : Fin 32, (0xFFFFFFFF : UInt32).toBitVec.getLsbD i = true := by
  decide

theorem pat_f0 : ∀ i < 32, chainTarget (pos (finalFlag + i)) =
    some ((0xFFFFFFFF : UInt32).toBitVec.getLsbD i) := fun i hi ↦ by
  simp (disch := omega) only [chainTarget, finalFlag, pv (show 1088 + i < 16384 by omega),
    ones_getLsbD ⟨i, hi⟩, ite_eq_left, ite_eq_right]

/-- The target pins `one` to `1` and otherwise only inputs. -/
theorem chainTarget_ok : TargetOk chainTarget := by
  refine ⟨by rw [chainTarget, onePos_val]; rfl, fun k b h ↦ ?_⟩
  rw [← Fin.val_inj, onePos_val]
  by_contra hk
  rcases Nat.lt_or_ge k.val 512 with h2 | h2
  · rw [chainTarget, ite_eq_right (by omega), ite_eq_left h2] at h
    cases h
  · simp (disch := omega) only [chainTarget, ite_eq_right, reduceCtorEq] at h

/-- The target pins bit `0` to `1` (bit `0` of `h0`). -/
theorem chainTarget_zero : chainTarget (pos 0) = some true := by
  rw [pat_h0 0 (by omega)]
  rfl

/-! ## Soundness -/

/-- The gate-level form of `block_sound`: the circuit's R1CS, `one = 1`, the target's bits. -/
theorem block_sound_circuit {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {w : Pos → Bool}
    (hz : circuitR1CS.Holds (liftBlock R w)) (h1 : w onePos = true) (hp : MeetsB chainTarget w) :
    readDigest w 256 = chainStep (readDigest w dBase) := by
  rw [readDigest_hOut, chainStep_eq, stepWords]
  congr 1
  refine compress_sound hz h1 (hIn_of_meets hp pat_h0) ?_ (readWord_of_meets hp pat_tlo)
    (readWord_of_meets hp (pat_zero (Or.inl rfl))) (readWord_of_meets hp pat_f0)
    (readWord_of_meets hp (pat_zero (Or.inr rfl)))
  refine block_congr fun p hp64 ↦ ?_
  rw [msgBytes_getD _ hp64]
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero]
    exact readByte_of_meets hp pat_tag
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [List.getD_cons_succ]
    rcases Nat.lt_or_ge q 32 with hq | hq
    · rw [List.getD_eq_getElem _ _ (by simp; omega), Vector.getElem_toList, readDigest,
        Vector.getElem_ofFn]
      congr 1
      simp only [msgBase, dBase]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      exact readByte_of_meets hp fun i hi ↦ by
        rw [UInt8.toBitVec_zero, BitVec.getLsbD_zero]
        exact pat_pad (by simp only [msgBase]; omega) (by simp only [msgBase]; omega)

/-- **The chain block, soundness.** A Boolean block satisfying the chain block's R1CS with its
public target, over a nontrivial ring of characteristic two, carries at `256 … 511` the chain step
of the digest it carries at `520 … 775`. -/
theorem block_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {w : Pos → Bool}
    (h : HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (liftBlock R w)) :
    readDigest w 256 = chainStep (readDigest w dBase) :=
  have h' := holdsE_sound chainTarget_ok h
  block_sound_circuit h'.1 h'.2.1 h'.2.2

/-! ## Completeness -/

/-- The input block of the chain step from `d`: the target's bits where it pins, the digest's
bits at `520 … 775`, `0` elsewhere. -/
def chainInp (d : Digest) (k : Pos) : Bool :=
  match chainTarget k with
  | some b => b
  | none => if dBase ≤ k.val ∧ k.val < dBase + 256 then digestBit d (k.val - dBase) else false

/-- The honest chain block of `d`: the trace of the block circuit on `chainInp d`. -/
noncomputable def chainTrace (d : Digest) : Pos → Bool := blake2sCircuit.traceF (chainInp d)

/-- The trace keeps every input. -/
theorem chainTrace_input (d : Digest) {k : Pos} (hk : k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152)) :
    chainTrace d k = chainInp d k :=
  traceF_input bounded_blake2s _
    (by rw [blake2sCircuit_inputs, getLsbD_inputs]; exact decide_eq_true hk)
    (by rw [blake2sCircuit_cpos]; exact Fin.ne_of_val_ne (by rw [constPos_val]; omega))

/-- **The chain block, completeness.** Over a nontrivial ring of characteristic two, the honest
block of a digest satisfies the chain block's R1CS with its target, carries the digest at
`520 … 775` and its chain step at `256 … 511`. -/
theorem block_complete {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (d : Digest) :
    HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (liftBlock R (chainTrace d)) ∧
      readDigest (chainTrace d) dBase = d ∧ readDigest (chainTrace d) 256 = chainStep d := by
  have hs : circuitR1CS.Holds (liftBlock R (chainTrace d)) :=
    (trace_satisfies (R := R) bounded_blake2s (chainInp d)).1
  have h1 : chainTrace d onePos = true := by
    rw [chainTrace, onePos, ← blake2sCircuit_cpos]; exact traceF_cpos bounded_blake2s _
  have hp : MeetsB chainTarget (chainTrace d) := fun k b hk ↦ by
    rcases chainTarget_ok.2 k b hk with rfl | hin
    · exact Option.some.inj (chainTarget_ok.1.symm.trans hk) ▸ h1
    · rw [chainTrace_input d hin, chainInp, hk]
  have hd : readDigest (chainTrace d) dBase = d := by
    refine (readDigest_eq_iff _ _ _).mpr fun j hj ↦ ?_
    have hv : dBase + j < 16384 := by simp only [dBase]; omega
    rw [chainTrace_input d (by rw [pv hv]; simp only [dBase]; omega), chainInp]
    simp (disch := omega) only [chainTarget, pv hv, dBase, ite_eq_left, ite_eq_right,
      Nat.add_sub_cancel_left]
  refine ⟨holdsE_complete hs hp, hd, ?_⟩
  rw [block_sound_circuit hs h1 hp, hd]

/-! ## Controls -/

/-- **Positive control (kernel-checked).** The chain step of the zero digest, i.e. the contract's
BLAKE2s-256 of `0x43 ‖ 0^32` (Python's `hashlib.blake2s`). -/
theorem chainStep_zero_kat : chainStep (Vector.replicate 32 0) =
    #v[0x95, 0x4a, 0xc2, 0xa4, 0xd6, 0xa7, 0x90, 0x03, 0x28, 0x4c, 0x9e, 0x3f, 0x09, 0xf5, 0x9d,
        0x21,
      0x8e, 0xa7, 0x53, 0x8f, 0x69, 0x63, 0x1c, 0xab, 0x53, 0x12, 0x4a, 0xe6, 0xcd, 0x41, 0x8d,
          0x8d]
    := by decide +kernel

/-- **Positive control.** The honest chain block of the zero digest satisfies the block R1CS and
carries the known answer of the contract's BLAKE2s at its output positions. -/
theorem chainTrace_zero_kat {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] :
    HoldsE (blockR1CS chainTarget) (targetVal R chainTarget)
        (liftBlock R (chainTrace (Vector.replicate 32 0))) ∧
      readDigest (chainTrace (Vector.replicate 32 0)) 256 =
        #v[0x95, 0x4a, 0xc2, 0xa4, 0xd6, 0xa7, 0x90, 0x03, 0x28, 0x4c, 0x9e, 0x3f, 0x09, 0xf5,
          0x9d, 0x21, 0x8e, 0xa7, 0x53, 0x8f, 0x69, 0x63, 0x1c, 0xab, 0x53, 0x12, 0x4a, 0xe6, 0xcd,
          0x41, 0x8d, 0x8d] := by
  obtain ⟨h, -, ho⟩ := block_complete (R := R) (Vector.replicate 32 0)
  exact ⟨h, ho.trans chainStep_zero_kat⟩

/-- **Negative control.** Flipping any output bit of a block satisfying the chain block's R1CS
with its target breaks it (over a nontrivial ring of characteristic two). With `block_complete`,
this applies to every honest block. -/
theorem not_holds_flip {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (w : Pos → Bool)
    (hz : HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (liftBlock R w))
    (k : Pos) (hk : 256 ≤ k.val ∧ k.val < 512) :
    ¬ HoldsE (blockR1CS chainTarget) (targetVal R chainTarget)
      (liftBlock R (Function.update w k (!w k))) := by
  intro hz'
  have hne : ∀ {j : Pos}, j.val < 256 ∨ 512 ≤ j.val → j ≠ k := fun hj h ↦ by
    rw [h] at hj; omega
  have hin : readDigest (Function.update w k (!w k)) dBase = readDigest w dBase :=
    readDigest_congr fun e he i hi ↦ by
      have hv : dBase + 8 * e + i < 16384 := by simp only [dBase]; omega
      rw [Function.update_of_ne (hne (by rw [pv hv]; simp only [dBase]; omega))]
  have hout := block_sound hz'
  rw [hin, ← block_sound hz] at hout
  have hb := congrArg (fun d : Digest ↦ (d[(k.val - 256) / 8]'(by omega)).toBitVec.getLsbD
    ((k.val - 256) % 8)) hout
  rw [readDigest_getLsbD _ _ _ (by omega) (Nat.mod_lt _ (by omega)),
    readDigest_getLsbD _ _ _ (by omega) (Nat.mod_lt _ (by omega))] at hb
  have hpk : (pos (256 + 8 * ((k.val - 256) / 8) + (k.val - 256) % 8) : Pos) = k :=
    Fin.ext (by rw [pv (by omega)]; omega)
  simp only [hpk, Function.update_self] at hb
  cases w k <;> simp at hb

/-- **Negative control (BP-C-M5).** The all-zero block satisfies the circuit's R1CS (with
`one = 0`) but not the chain block's R1CS with its target. -/
theorem zero_control {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] :
    circuitR1CS.Holds (fun _ : Pos ↦ (0 : R)) ∧
      ¬ HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (fun _ ↦ (0 : R)) :=
  ⟨zero_holds, zero_not_holdsE chainTarget_ok⟩

end Chain

end FR
