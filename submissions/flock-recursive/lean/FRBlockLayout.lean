-- New for `flock-recursive` (BLUEPRINT Appendix A.6). `h0`, `leDigest`, the byte and digest readers
-- and `block_getLsbD` are copied from `submissions/spartan-srom/lean/SpartanSromBlake2sR1CS.lean`
-- (this repository, branch `v4/flock-recursive` at `783328c`), renamed to the namespace `FR`.
import RecursionFast.Contract.Relation
import Mathlib.Tactic.IntervalCases
import FRBlake2sWitness

/-!
# The block layout and the block R1CS with its public target (BLUEPRINT §4, Appendix A.6)

One block of `2 ^ 14` bits is one BLAKE2s compression, laid out as A.6:

| bits | slot | content |
|---|---|---|
| `0 … 255` | 0–1 | `h_in` (8 words, little-endian) |
| `256 … 511` | 2–3 | `h_out` (output rows `(out form, one)`) |
| `512 … 1023` | 4–7 | the 64-byte message, byte `p` bit `b` at `512 + 8 p + b` |
| `1024`, `1056` | 8 | the counter's words `t_lo`, `t_hi` |
| `1088`, `1120` | 8 | the flags `f0`, `f1` |
| `1152` | 9 | `one` |
| `1153 … 1279` | | zero rows |
| `1280 … 15999` | | the 14,720 product gates in leanVM's order |
| `16000 … 16383` | | zero rows |

**Two R1CS.** `circuitR1CS` is the R1CS of the re-based BLAKE2s circuit (`FRBlake2sCompress`):
every input (`h_in`, the message, `t`, `f`) has the row `(var k, var one)`, `one` the row
`(one, one)`, a gate its two forms, an output `(out form, one)`. It is the gate-level object the
soundness proofs run on (`compress_sound`).

The **block R1CS of the entry** (BLUEPRINT revision 3.1, §4 and P1-D2/D3) carries a **public
target** `E`: the constraint is `(A₀ z) ∘ (B₀ z) = z + E`, and the positions that hold per-block
public constants have the row `(0, 0)`, so there the constraint reads `z = E` (characteristic
two). A `Target` says which positions are pinned and to which bit (`tgt k = some b`);
`blockR1CS tgt` is `circuitR1CS` with the rows of the pinned positions replaced by `(0, 0)`,
`targetVal R tgt` is `E`, and `HoldsE` is the constraint with the target. Every target of the
entry pins `one` to `1` and otherwise only inputs (`TargetOk`); then a Boolean block satisfying
`HoldsE` satisfies `circuitR1CS`, has `one = 1` and holds the target's bits (`holdsE_sound`),
and conversely (`holdsE_complete`).

**The `one` bit (BP-C-M5).** The all-zero block satisfies `circuitR1CS` (`zero_holds`: every row
is a product of linear forms) with `one = 0`; the target excludes it (`zero_not_holdsE`).

**The walk** of `blockR1CS tgt` is the walk of `circuitR1CS` with the row weights of the pinned
positions set to `0` (`walkE_eq_sum`); the row weights are arbitrary (the verifier passes the
Lagrange weights of the skip coordinate at `λ` and the `eq` table of the other row bits).

Main results: `holdsE_sound`, `holdsE_complete`, `compress_sound`, the readers `hIn`, `hOut`,
`msgBytes`, `readDigest`, the rows of `circuitR1CS` (`rowOf_one`, `rowOf_input`, `rowOf_zero`),
the BLAKE2s facts `blake2sDigest_eq`, `block_congr`, and `walkE_eq_sum`.
-/

namespace FR

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

namespace Block

/-! ## Positions and the block R1CS -/

/-- A position of a block. -/
abbrev Pos := ProductCircuit.Pos Blake2sCircuit.m

/-- The position of `one` (bit `1152`, BLUEPRINT A.6). -/
def onePos : Pos := constPos

theorem onePos_val : (onePos : ℕ) = 1152 := rfl

/-- The R1CS of the re-based BLAKE2s circuit, `C = I`, no target: the gate-level object. -/
noncomputable def circuitR1CS : BlockR1CS Blake2sCircuit.m := blake2sCircuit.toBlockR1CS

/-! ## Rows of `circuitR1CS` -/

/-- The row of `one` is `(one, one)`. -/
theorem rowOf_one : blake2sCircuit.rowOf onePos = ⟨Form.var onePos, Form.var onePos⟩ := by
  have := rowOf_cpos bounded_blake2s
  rwa [blake2sCircuit_cpos] at this

/-- The row of an input of a bounded circuit is `(var k, var one)`. -/
theorem rowOf_input' {m : ℕ} {c : ProductCircuit m} (hc : c.Bounded) {k : ProductCircuit.Pos m}
    (hk : c.inputs.getLsbD k = true) (hkc : k ≠ c.cpos) :
    c.rowOf k = ⟨Form.var k, Form.var c.cpos⟩ := by
  have hnm : k ∉ c.gates.toList.map Prod.fst := fun hm ↦ by
    have := boundedFrom_fresh hc hm
    rw [BitVec.getLsbD_or, hk, Bool.true_or] at this
    exact Bool.noConfusion this
  have hl : c.gates.toList.lookup k = none :=
    Option.eq_none_iff_forall_ne_some.mpr fun _ h ↦ hnm (mem_of_lookup h)
  simp only [rowOf, rowOfList, hl, hkc, ↓reduceIte, hk]

/-- The row of an input of the block (`h_in`, the message, `t`, `f`): `(var k, var one)`. -/
theorem rowOf_input {k : Pos} (hk : k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152)) :
    blake2sCircuit.rowOf k = ⟨Form.var k, Form.var onePos⟩ := by
  have := rowOf_input' bounded_blake2s (k := k)
    (by rw [blake2sCircuit_inputs, getLsbD_inputs]; exact decide_eq_true hk)
    (by rw [blake2sCircuit_cpos]; exact Fin.ne_of_val_ne (by rw [constPos_val]; omega))
  rwa [blake2sCircuit_cpos] at this

/-- The row of a position of a circuit that is no gate, no input and not the constant is
`(0, 0)`. -/
theorem rowOf_zero' {m : ℕ} {c : ProductCircuit m} {k : ProductCircuit.Pos m}
    (hnm : k ∉ c.gates.toList.map Prod.fst) (hk : c.inputs.getLsbD k = false) (hkc : k ≠ c.cpos) :
    c.rowOf k = ⟨0, 0⟩ := by
  have hl : c.gates.toList.lookup k = none :=
    Option.eq_none_iff_forall_ne_some.mpr fun _ h ↦ hnm (mem_of_lookup h)
  simp only [rowOf, rowOfList, hl, hkc, ↓reduceIte, hk, Bool.false_eq_true]

/-- The rows of `1153 … 1279` and `16000 …` are `(0, 0)`. -/
theorem rowOf_zero {k : Pos} (hk : (1152 < k.val ∧ k.val < 1280) ∨ 16000 ≤ k.val) :
    blake2sCircuit.rowOf k = ⟨0, 0⟩ := by
  have hnm : k ∉ blake2sCircuit.gates.toList.map Prod.fst := by
    intro hm
    obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hm
    have hp' := Array.mem_toList_iff.mp hp
    rw [blake2sCircuit_gates] at hp'
    rcases Array.mem_append.mp hp' with hp | hp
    · have := compress_keys (Array.mem_toList_iff.mpr hp)
      rw [hpk] at this
      omega
    · obtain ⟨w, i, rfl⟩ := mem_outRows (List.mem_toArray.mp hp)
      have := pos_out_val w i
      rw [show (pos (256 + 32 * w.val + i.val) : Pos) = k from hpk] at this
      have := w.isLt
      have := i.isLt
      omega
  have hkc : k ≠ blake2sCircuit.cpos := by
    rw [blake2sCircuit_cpos]; exact Fin.ne_of_val_ne (by rw [constPos_val]; omega)
  have hin : blake2sCircuit.inputs.getLsbD k = false := by
    rw [blake2sCircuit_inputs, getLsbD_inputs]; exact decide_eq_false (by omega)
  exact rowOf_zero' hnm hin hkc

/-! ## The all-zero block and the `one` bit -/

/-- The all-zero block satisfies the circuit's R1CS (without target) over any ring. -/
theorem zero_holds {R : Type*} [CommRing R] : circuitR1CS.Holds (fun _ : Pos ↦ (0 : R)) := by
  intro k
  simp [BlockR1CS.mulVec]

/-! ## Reading a block -/

/-- The byte a block holds at the positions `b, …, b + 7`, low bit first. -/
def readByte (w : Pos → Bool) (b : ℕ) : UInt8 := ⟨BitVec.ofFnLE fun i : Fin 8 ↦ w (pos (b + i))⟩

/-- The digest a block holds from position `b`: byte `e` bit `b'` at `b + 8 e + b'`. -/
def readDigest (w : Pos → Bool) (b : ℕ) : Digest :=
  Vector.ofFn fun e : Fin 32 ↦ readByte w (b + 8 * e)

/-- The chaining value `h_in`, eight words. -/
def hIn (w : Pos → Bool) : Vector UInt32 8 := Vector.ofFn fun j : Fin 8 ↦ readWord w (32 * j)

/-- The output `h_out`, eight words. -/
def hOut (w : Pos → Bool) : Vector UInt32 8 :=
  Vector.ofFn fun j : Fin 8 ↦ readWord w (256 + 32 * j)

/-- The 64 message bytes, byte `p` at `512 + 8 p`. -/
def msgBytes (w : Pos → Bool) : List UInt8 :=
  List.ofFn fun p : Fin 64 ↦ readByte w (msgBase + 8 * p)

theorem readByte_getLsbD (w : Pos → Bool) (b : ℕ) {i : ℕ} (hi : i < 8) :
    (readByte w b).toBitVec.getLsbD i = w (pos (b + i)) := by
  simp [readByte, hi]

theorem readWord_getLsbD (w : Pos → Bool) (b : ℕ) {i : ℕ} (hi : i < 32) :
    (readWord w b).toBitVec.getLsbD i = w (pos (b + i)) := by
  simp [readWord, hi]

theorem readDigest_getLsbD (w : Pos → Bool) (b e : ℕ) (he : e < 32) {i : ℕ} (hi : i < 8) :
    (readDigest w b)[e].toBitVec.getLsbD i = w (pos (b + 8 * e + i)) := by
  rw [readDigest, Vector.getElem_ofFn, readByte_getLsbD _ _ hi]

/-- Two digests are equal when their bits are. -/
theorem digest_ext {d d' : Digest}
    (h : ∀ e (he : e < 32), ∀ i < 8, d[e].toBitVec.getLsbD i = d'[e].toBitVec.getLsbD i) :
    d = d' :=
  Vector.ext fun e he ↦ UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi ↦ h e he i hi)

/-- The digest a block holds depends only on its positions. -/
theorem readDigest_congr {w w' : Pos → Bool} {b b' : ℕ}
    (h : ∀ e < 32, ∀ i < 8, w (pos (b + 8 * e + i)) = w' (pos (b' + 8 * e + i))) :
    readDigest w b = readDigest w' b' :=
  digest_ext fun e he i hi ↦ by
    rw [readDigest_getLsbD _ _ _ he hi, readDigest_getLsbD _ _ _ he hi, h e he i hi]

/-- Bit `j < 256` of a digest: bit `j mod 8` of byte `j / 8`. -/
def digestBit (d : Digest) (j : ℕ) : Bool :=
  if h : j < 256 then (d[j / 8]'(by omega)).toBitVec.getLsbD (j % 8) else false

/-- A block holds the digest `d` from `b` iff its 256 positions hold the bits of `d`. -/
theorem readDigest_eq_iff (w : Pos → Bool) (b : ℕ) (d : Digest) :
    readDigest w b = d ↔ ∀ j < 256, w (pos (b + j)) = digestBit d j := by
  constructor
  · rintro rfl j hj
    rw [digestBit, dite_eq_left hj, readDigest_getLsbD _ _ _ (by omega) (Nat.mod_lt _ (by omega))]
    congr 2
    omega
  · intro h
    refine digest_ext fun e he i hi ↦ ?_
    rw [readDigest_getLsbD _ _ _ he hi, show b + 8 * e + i = b + (8 * e + i) by omega,
      h _ (by omega), digestBit, dite_eq_left (by omega)]
    simp only [show (8 * e + i) / 8 = e by omega, show (8 * e + i) % 8 = i by omega]

/-! ## BLAKE2s facts -/

/-- The chaining value of an unkeyed 32-byte BLAKE2s (RFC 7693 §2.5, §3.3): `iv` with the parameter
block `0x0101kknn`, `kk = 0`, `nn = 32`, XORed into word `0`. -/
def h0 : Vector UInt32 8 :=
  iv.set 0 (iv[0] ^^^ (0x01010000 : UInt32) ^^^ (0 : ℕ).toUInt32 <<< 8 ^^^ (32 : ℕ).toUInt32)

/-- The 32-byte digest whose byte `e` is byte `e mod 4` of word `e / 4`, little-endian (the `le`
encoding of `blake2s`). -/
def leDigest (H : Vector UInt32 8) : Digest :=
  Vector.ofFn fun e : Fin 32 ↦ (H[e.val / 4] >>> (8 * (e.val % 4)).toUInt32).toUInt8

private theorem toList_eq_ofFn {α : Type} (H : Vector α 8) :
    H.toList = [H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.length_toList] at h1
  interval_cases i <;> simp

/-- BLAKE2s-256 of any input is the block loop of RFC 7693 §3.3 from `h0`, encoded little-endian
and truncated to 32 bytes. -/
theorem blake2s256_eq (l : List UInt8) :
    blake2s256 l = ((compressInput h0 0 l ((l.length - 1) / 64)).toList.flatMap
      (fun w : UInt32 ↦ [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8,
        (w >>> 24).toUInt8])).take 32 := by
  simp only [blake2s256, blake2s, List.length_nil, ↓reduceIte, List.nil_append]
  rfl

/-- The contract's digest of an input is the little-endian encoding of its final chaining
value. -/
theorem blake2sDigest_eq (l : List UInt8) :
    blake2sDigest l = leDigest (compressInput h0 0 l ((l.length - 1) / 64)) := by
  apply Vector.ext
  intro e he
  simp only [blake2sDigest, Vector.getElem_mk, List.getElem_toArray, blake2s256_eq, toList_eq_ofFn,
    leDigest, Vector.getElem_ofFn]
  interval_cases e <;> rfl

/-- Bit `b < 8` of a byte of a word is a bit of the word. -/
theorem toUInt8_shiftRight_getLsbD (w : UInt32) (q b : ℕ) (hq : q < 4) (hb : b < 8) :
    ((w >>> (8 * q).toUInt32).toUInt8).toBitVec.getLsbD b = w.toBitVec.getLsbD (8 * q + b) := by
  simp [hb, Nat.mod_eq_of_lt (show 8 * q < 32 by omega)]

/-- Bit `b` of byte `e` of `leDigest H` is bit `8 (e mod 4) + b` of word `e / 4`. -/
theorem leDigest_getLsbD (H : Vector UInt32 8) (e : ℕ) (he : e < 32) (b : ℕ) (hb : b < 8) :
    (leDigest H)[e].toBitVec.getLsbD b =
      (H[e / 4]'(by omega)).toBitVec.getLsbD (8 * (e % 4) + b) := by
  rw [leDigest, Vector.getElem_ofFn]
  exact toUInt8_shiftRight_getLsbD _ _ _ (by omega) hb

/-- The digest a block holds at `h_out` is the encoding of its output words. -/
theorem readDigest_hOut (w : Pos → Bool) : readDigest w 256 = leDigest (hOut w) := by
  refine digest_ext fun e he i hi ↦ ?_
  rw [readDigest_getLsbD _ _ _ he hi, leDigest_getLsbD _ _ he _ hi, hOut, Vector.getElem_ofFn,
    readWord_getLsbD _ _ (by omega)]
  show w (pos (256 + 8 * e + i)) = w (pos (256 + 32 * (e / 4) + (8 * (e % 4) + i)))
  congr 2
  omega

/-- Bit `i` of message word `j` is bit `i mod 8` of byte `4 j + i / 8` of the input (zero past
its end), for an input of at most 64 bytes. -/
theorem block_getLsbD (l : List UInt8) (hl : l.length ≤ 64) (j : Fin 16) (i : ℕ) (hi : i < 32) :
    (block l)[j].toBitVec.getLsbD i = (l.getD (4 * j.val + i / 8) 0).toBitVec.getLsbD (i % 8) := by
  simp only [block, List.take_of_length_le hl]
  simp [hi]
  have ge : ∀ k, 8 ≤ k → ∀ x : UInt8, x.toBitVec.getLsbD k = false :=
    fun k hk x ↦ BitVec.getLsbD_of_ge _ _ hk
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h
  · simp [h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, show i < 16 by omega, show i < 24 by omega]
  · simp [ge i (by omega), show ¬ i < 8 by omega, h.2, show i < 24 by omega,
      show i / 8 = 1 by omega, show i % 8 = i - 8 by omega]
  · simp [ge i (by omega), ge (i - 8) (by omega), show ¬ i < 8 by omega, show ¬ i < 16 by omega,
      h.2, show i / 8 = 2 by omega, show i % 8 = i - 16 by omega]
  · simp [ge i (by omega), ge (i - 8) (by omega), ge (i - 16) (by omega), show ¬ i < 8 by omega,
      show ¬ i < 16 by omega, show ¬ i < 24 by omega, show i / 8 = 3 by omega,
      show i % 8 = i - 24 by omega]

/-- A message block depends only on the first 64 bytes of its input, zero past the end. -/
theorem block_congr {l l' : List UInt8} (h : ∀ p < 64, l.getD p 0 = l'.getD p 0) :
    block l = block l' := by
  have ht : ∀ l : List UInt8, block l = block (l.take 64) := fun l ↦ by
    simp only [block, List.take_take, Nat.min_self]
  have hg : ∀ (l : List UInt8) p, p < 64 → (l.take 64).getD p 0 = l.getD p 0 := fun l p hp ↦ by
    simp [List.getD_eq_getElem?_getD, hp]
  rw [ht l, ht l']
  refine Vector.ext fun j hj ↦ UInt32.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi ↦ ?_)
  have e := block_getLsbD (l.take 64) (List.length_take_le _ _) ⟨j, hj⟩ i hi
  have e' := block_getLsbD (l'.take 64) (List.length_take_le _ _) ⟨j, hj⟩ i hi
  simp only [Fin.getElem_fin] at e e'
  rw [e, e', hg _ _ (by omega), hg _ _ (by omega), h _ (by omega)]

theorem msgBytes_getD (w : Pos → Bool) {p : ℕ} (hp : p < 64) :
    (msgBytes w).getD p 0 = readByte w (msgBase + 8 * p) := by
  rw [msgBytes, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hp]

/-! ## Soundness of one block -/

/-- **One block.** A Boolean block satisfying the block R1CS over a nontrivial ring of
characteristic two, with `one = 1`, carries at `h_out` the compression of its `h_in`, its message
bytes, its counter and its flags. -/
theorem compress_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {w : Pos → Bool}
    (hz : circuitR1CS.Holds (liftBlock R w)) (h1 : w onePos = true)
    {h : Vector UInt32 8} {msg : Vector UInt32 16} {t : UInt64} {f0 f1 : UInt32}
    (hh : hIn w = h) (hm : block (msgBytes w) = msg) (ht0 : readWord w counterLo = t.toUInt32)
    (ht1 : readWord w counterHi = (t >>> 32).toUInt32) (hf0 : readWord w finalFlag = f0)
    (hf1 : readWord w lastNodeFlag = f1) : hOut w = compress h msg t f0 f1 := by
  have hmw : ∀ k : Fin 16, Den w (msgW k) msg[k] := fun k ↦ by
    refine den_inW fun i ↦ ?_
    rw [← hm, block_getLsbD (msgBytes w) List.length_ofFn.le k i i.isLt,
      msgBytes_getD _ (by omega), readByte_getLsbD _ _ (Nat.mod_lt _ (by omega))]
    congr 2
    simp only [msgBase]
    omega
  have hout := blake2s_sound w hz h1 (h := h) (msg := msg) (t := t) (f0 := f0) (f1 := f1)
    (fun k ↦ den_congr (den_readWord w _) (by
      rw [← hh, hIn, Fin.getElem_fin, Vector.getElem_ofFn]))
    hmw (den_congr (den_readWord w _) ht0) (den_congr (den_readWord w _) ht1)
    (den_congr (den_readWord w _) hf0) (den_congr (den_readWord w _) hf1)
  refine Vector.ext fun k hk ↦ ?_
  rw [hOut, Vector.getElem_ofFn]
  exact den_unique (den_readWord w _) (hout ⟨k, hk⟩)

/-! ## The public target -/

/-- A public target on a block: `tgt k = some b` pins position `k` (row `(0, 0)`) to the bit
`b`; `none` leaves the circuit's row. -/
abbrev Target := Pos → Option Bool

/-- The block R1CS with the target's positions as `(0, 0)` rows: `A₀`, `B₀` of BLUEPRINT §4. -/
noncomputable def blockR1CS (tgt : Target) : BlockR1CS Blake2sCircuit.m :=
  ⟨fun k j ↦ (tgt k).isNone && circuitR1CS.A k j, fun k j ↦ (tgt k).isNone && circuitR1CS.B k j⟩

/-- The public target `E` as a block over `R`: the pinned bit, `0` where nothing is pinned. -/
def targetVal (R : Type*) [CommRing R] (tgt : Target) (k : Pos) : R := ofBool R ((tgt k).getD false)

/-- The constraint with a public target: `(A z)_k · (B z)_k = z_k + E_k` at every position. -/
def HoldsE {R : Type*} [CommRing R] (C : BlockR1CS Blake2sCircuit.m) (E z : Pos → R) : Prop :=
  ∀ k, BlockR1CS.mulVec C.A z k * BlockR1CS.mulVec C.B z k = z k + E k

/-- A Boolean block meets a target: every pinned position holds its bit. -/
def MeetsB (tgt : Target) (w : Pos → Bool) : Prop := ∀ k b, tgt k = some b → w k = b

/-- A target of the entry pins `one` to `1` and otherwise only inputs of the circuit. -/
def TargetOk (tgt : Target) : Prop :=
  tgt onePos = some true ∧
    ∀ k b, tgt k = some b → k = onePos ∨ k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152)

section Target

variable {R : Type*} [CommRing R] {tgt : Target}

private theorem mulVec_pinned {k : Pos} {b : Bool} (hk : tgt k = some b) (z : Pos → R) :
    BlockR1CS.mulVec (blockR1CS tgt).A z k = 0 ∧ BlockR1CS.mulVec (blockR1CS tgt).B z k = 0 := by
  simp [BlockR1CS.mulVec, blockR1CS, hk]

private theorem mulVec_free {k : Pos} (hk : tgt k = none) (z : Pos → R) :
    BlockR1CS.mulVec (blockR1CS tgt).A z k = BlockR1CS.mulVec circuitR1CS.A z k ∧
      BlockR1CS.mulVec (blockR1CS tgt).B z k = BlockR1CS.mulVec circuitR1CS.B z k := by
  simp [BlockR1CS.mulVec, blockR1CS, hk]

variable [CharP R 2] [Nontrivial R]

/-- **The target, soundness.** A Boolean block satisfying the block R1CS with a target of the
entry satisfies the circuit's R1CS, has `one = 1` and holds the target's bits. -/
theorem holdsE_sound (ht : TargetOk tgt) {w : Pos → Bool}
    (h : HoldsE (blockR1CS tgt) (targetVal R tgt) (liftBlock R w)) :
    circuitR1CS.Holds (liftBlock R w) ∧ w onePos = true ∧ MeetsB tgt w := by
  have hm : MeetsB tgt w := fun k b hk ↦ by
    have e := h k
    rw [(mulVec_pinned hk _).1, (mulVec_pinned hk _).2, mul_zero, targetVal, hk,
      Option.getD_some] at e
    have := eq_neg_of_add_eq_zero_left e.symm
    rw [CharTwo.neg_eq] at this
    exact ofBool_injective this
  have h1 : w onePos = true := hm _ _ ht.1
  refine ⟨fun k ↦ ?_, h1, hm⟩
  rcases hk : tgt k with _ | b
  · have e := h k
    rw [(mulVec_free hk _).1, (mulVec_free hk _).2, targetVal, hk] at e
    simpa [ofBool] using e
  · rcases ht.2 k b hk with rfl | hin
    · simp only [circuitR1CS]
      rw [mulVec_A_liftBlock, mulVec_B_liftBlock, rowOf_one]
      simp [liftBlock, h1, ofBool]
    · simp only [circuitR1CS]
      rw [mulVec_A_liftBlock, mulVec_B_liftBlock, rowOf_input hin]
      simp [liftBlock, h1, ofBool]

omit [Nontrivial R] in
/-- **The target, completeness.** A Boolean block satisfying the circuit's R1CS and holding the
bits of a target satisfies the block R1CS with that target. -/
theorem holdsE_complete {w : Pos → Bool}
    (hz : circuitR1CS.Holds (liftBlock R w)) (hm : MeetsB tgt w) :
    HoldsE (blockR1CS tgt) (targetVal R tgt) (liftBlock R w) := fun k ↦ by
  rcases hk : tgt k with _ | b
  · rw [(mulVec_free hk _).1, (mulVec_free hk _).2, targetVal, hk, hz k]
    simp [ofBool]
  · rw [(mulVec_pinned hk _).1, (mulVec_pinned hk _).2, mul_zero, targetVal, hk, Option.getD_some,
      liftBlock, hm k b hk, CharTwo.add_self_eq_zero]

/-- **Negative control (BP-C-M5).** The all-zero block, which satisfies the circuit's R1CS with
`one = 0` (`zero_holds`), does not satisfy the block R1CS with a target of the entry. -/
theorem zero_not_holdsE (ht : TargetOk tgt) :
    ¬ HoldsE (blockR1CS tgt) (targetVal R tgt) (fun _ ↦ (0 : R)) := fun h ↦ by
  have e : liftBlock R (fun _ : Pos ↦ false) = fun _ ↦ (0 : R) := by
    funext k; simp [liftBlock, ofBool]
  have := (holdsE_sound (w := fun _ ↦ false) ht (e ▸ h)).2.1
  simp at this

end Target

/-- **The walk of the block R1CS with a target.** The walk of the circuit with the row weights of
the pinned positions set to `0` computes the bilinear forms of `blockR1CS tgt`, for any row
weights `e` and column weights `wt`. -/
theorem walkE_eq_sum {R : Type} [CommRing R] [CharP R 2] (tgt : Target) (e wt : Pos → R) :
    walkAB (fun k ↦ if (tgt k).isNone then e k else 0) wt =
      (∑ k, e k * BlockR1CS.mulVec (blockR1CS tgt).A wt k,
        ∑ k, e k * BlockR1CS.mulVec (blockR1CS tgt).B wt k) := by
  have key : ∀ k, (if (tgt k).isNone then e k else 0) * BlockR1CS.mulVec circuitR1CS.A wt k =
        e k * BlockR1CS.mulVec (blockR1CS tgt).A wt k ∧
      (if (tgt k).isNone then e k else 0) * BlockR1CS.mulVec circuitR1CS.B wt k =
        e k * BlockR1CS.mulVec (blockR1CS tgt).B wt k := fun k ↦ by
    rcases hk : tgt k with _ | b
    · rw [(mulVec_free hk wt).1, (mulVec_free hk wt).2]
      simp only [Option.isNone_none, ↓reduceIte, and_self]
    · rw [(mulVec_pinned hk wt).1, (mulVec_pinned hk wt).2]
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, zero_mul, mul_zero, and_self]
  have hA : (fun k ↦ (if (tgt k).isNone then e k else 0) *
      BlockR1CS.mulVec blake2sCircuit.toBlockR1CS.A wt k) =
      fun k ↦ e k * BlockR1CS.mulVec (blockR1CS tgt).A wt k := funext fun k ↦ (key k).1
  have hB : (fun k ↦ (if (tgt k).isNone then e k else 0) *
      BlockR1CS.mulVec blake2sCircuit.toBlockR1CS.B wt k) =
      fun k ↦ e k * BlockR1CS.mulVec (blockR1CS tgt).B wt k := funext fun k ↦ (key k).2
  rw [walk_eq_sum, hA, hB]

/-- A word pinned by a target, read off a block meeting it. -/
theorem readWord_of_meets {tgt : Target} {w : Pos → Bool} (hm : MeetsB tgt w) {b : ℕ} {u : UInt32}
    (hp : ∀ i < 32, tgt (pos (b + i)) = some (u.toBitVec.getLsbD i)) : readWord w b = u :=
  UInt32.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi ↦ by
    rw [readWord_getLsbD _ _ hi, hm _ _ (hp i hi)])

/-- A byte pinned by a target, read off a block meeting it. -/
theorem readByte_of_meets {tgt : Target} {w : Pos → Bool} (hm : MeetsB tgt w) {b : ℕ} {u : UInt8}
    (hp : ∀ i < 8, tgt (pos (b + i)) = some (u.toBitVec.getLsbD i)) : readByte w b = u :=
  UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi ↦ by
    rw [readByte_getLsbD _ _ hi, hm _ _ (hp i hi)])

/-- Bit `j` of the eight words `h`: bit `j mod 32` of word `j / 32` (`false` past `256`). -/
def wordsBit (h : Vector UInt32 8) (j : ℕ) : Bool :=
  if hj : j < 256 then (h[j / 32]'(by omega)).toBitVec.getLsbD (j % 32) else false

/-- The chaining value pinned by a target at `0 … 255`, read off a block meeting it. -/
theorem hIn_of_meets {tgt : Target} {w : Pos → Bool} (hm : MeetsB tgt w) {h : Vector UInt32 8}
    (hp : ∀ j < 256, tgt (pos j) = some (wordsBit h j)) : hIn w = h := by
  refine Vector.ext fun k hk ↦ ?_
  rw [hIn, Vector.getElem_ofFn]
  refine readWord_of_meets hm fun i hi ↦ ?_
  rw [hp _ (by omega), wordsBit, dite_eq_left (by omega)]
  simp only [show (32 * k + i) / 32 = k by omega, show (32 * k + i) % 32 = i by omega]

/-- The chaining value a block holds, from its bits. -/
theorem hIn_of_bits {w : Pos → Bool} {h : Vector UInt32 8}
    (hb : ∀ j < 256, w (pos j) = wordsBit h j) : hIn w = h :=
  hIn_of_meets (tgt := fun k ↦ some (w k)) (fun _ _ hk ↦ Option.some.inj hk)
    fun j hj ↦ congrArg some (hb j hj)

/-- Bit `j` of the output words is the block's bit `256 + j`. -/
theorem hOut_bit (w : Pos → Bool) {j : ℕ} (hj : j < 256) :
    wordsBit (hOut w) j = w (pos (256 + j)) := by
  rw [wordsBit, dite_eq_left hj, hOut, Vector.getElem_ofFn, readWord_getLsbD _ _ (by omega)]
  congr 2
  simp only
  omega

/-! ## Blocks over a ring -/

section Ring

variable {R : Type*} [CommRing R] [DecidableEq R] [Nontrivial R]

/-- A `0`/`1` entry equal to `ofBool R b` holds the bit `b`. -/
theorem toBools_of_eq {z : Pos → R} {k : Pos} {b : Bool} (h : z k = ofBool R b) :
    toBools z k = b := by
  cases b <;> simp [toBools, h, ofBool]

omit [Nontrivial R] in
/-- Two `0`/`1` entries that are equal hold the same bit. -/
theorem toBools_congr {z z' : Pos → R} {k k' : Pos} (h : z k = z' k') :
    toBools z k = toBools z' k' := by
  simp [toBools, h]

end Ring

end Block

end FR
