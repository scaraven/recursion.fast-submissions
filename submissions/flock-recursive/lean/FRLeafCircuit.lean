-- New for `flock-recursive` (BLUEPRINT §4.1, revision 3.1). The chain induction follows
-- `submissions/spartan-srom/lean/SpartanSromChainSound.lean` (`chain_sound`), restated over the
-- block layout of Appendix A.6 with the constants pinned by the public target.
import FRBlockChain

/-!
# The leaf circuit (BLUEPRINT §4.1)

A tree leaf proves `chainEnd s n = h` for `n = 2^(m − 14)` chain steps. Its committed table holds
`n` chain blocks (`FRBlockChain`), block `i` the step from the `i`-th digest of the chain. The leaf
circuit is the conjunction of:

* **the block R1CS with its public target** on every used block: `(A₀ z) ∘ (B₀ z) = z + E` with
  `E` the chain block's constants (`chainTarget`: `h0`, the tag, the zero bytes, `t = 33`, the
  flags, `one = 1`) at `(0, 0)`-row positions (the zerocheck's summand of BLUEPRINT §4);
* **`ChainLinks`**, the content of the shift argument (P1-D5): `h_out` of block `i` (`256 … 511`)
  is the digest hashed by block `i + 1` (`520 … 775`) for `i + 1 < n`, block `0` hashes `s`, block
  `n − 1` outputs `h`.

`leaf_sound` states both as hypotheses about the committed table **restricted to the leaf's used
blocks** `i < n`; their derivation from the zerocheck and the shift sumcheck is L-cert's. The table
is over any nontrivial ring of characteristic two with `0`/`1` entries (`GF(2)` itself, or `F`
holding a Boolean table).

**BP-C-M5.** The target delivers `one = 1` (`Block.holdsE_sound`). `zero_table_control`: the
all-zero table of one block meets the circuit's R1CS (without target) and `ChainLinks` for
`s = h = 0`, yet `chainEnd 0 1 ≠ 0`; it fails the block R1CS with the target.

Results: `leaf_sound`, `chain_of_blocks` (the Boolean core), `leafWitness` and `leaf_complete` (the
honest table meets every hypothesis), `zero_table_control`.
-/

namespace FR

open RecursionFast ProductCircuit Blake2sCircuit Block Chain

namespace Leaf

/-! ## The Boolean core -/

/-- **The chain of blocks.** `n` Boolean blocks satisfying the chain block's R1CS with its
target, linked so that block `i + 1` hashes block `i`'s output, with block `0` hashing `s`, carry
`chainEnd s (i + 1)` at the output of block `i`. -/
theorem chain_of_blocks {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {n : ℕ}
    (w : ℕ → Pos → Bool) (s : Digest)
    (hE : ∀ i < n, HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (liftBlock R (w i)))
    (hl : ∀ i, i + 1 < n → readDigest (w (i + 1)) dBase = readDigest (w i) 256)
    (hs : readDigest (w 0) dBase = s) :
    ∀ i < n, readDigest (w i) 256 = chainEnd s (i + 1) := by
  intro i
  induction i with
  | zero =>
    intro h0'
    rw [block_sound (hE 0 h0'), hs, chainEnd, Function.iterate_one]
  | succ i ih =>
    intro hi
    rw [block_sound (hE _ hi), hl i hi, ih (by omega), chainEnd, chainEnd,
      Function.iterate_succ_apply' chainStep (i + 1)]

/-! ## Soundness -/

/-- **The links of a chain** (the shift argument's content): block `i + 1` hashes (`520 … 775`)
the output (`256 … 511`) of block `i`, block `0` hashes `s`, block `n − 1` outputs `h`. -/
def ChainLinks {R : Type*} [CommRing R] (n : ℕ) (z : ℕ → Pos → R) (s h : Digest) : Prop :=
  (∀ i, i + 1 < n → ∀ j < 256, z (i + 1) (pos (dBase + j)) = z i (pos (256 + j))) ∧
    (∀ j < 256, z 0 (pos (dBase + j)) = ofBool R (digestBit s j)) ∧
    ∀ j < 256, z (n - 1) (pos (256 + j)) = ofBool R (digestBit h j)

section Sound

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] [DecidableEq R]

omit [CharP R 2] in
private theorem digest_of_bits {z : Pos → R} {b : ℕ} {d : Digest}
    (h : ∀ j < 256, z (pos (b + j)) = ofBool R (digestBit d j)) : readDigest (toBools z) b = d :=
  (readDigest_eq_iff _ _ _).mpr fun j hj ↦ toBools_of_eq (h j hj)

/-- **Leaf soundness.** A table of `n ≥ 1` blocks over a nontrivial ring of characteristic two,
with `0`/`1` entries on its used blocks, satisfying on every used block the chain block's R1CS with
its public target, and whose blocks are linked from `s` to `h`, proves `chainEnd s n = h`. -/
theorem leaf_sound {n : ℕ} (hn : 1 ≤ n) (z : ℕ → Pos → R) (s h : Digest)
    (hbool : ∀ i < n, ∀ k, BlockR1CS.IsBool (z i k))
    (hE : ∀ i < n, HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (z i))
    (hlinks : ChainLinks n z s h) :
    chainEnd s n = h := by
  obtain ⟨hlink, hin, hout⟩ := hlinks
  set w : ℕ → Pos → Bool := fun i ↦ toBools (z i)
  have hE' : ∀ i < n, HoldsE (blockR1CS chainTarget) (targetVal R chainTarget)
      (liftBlock R (w i)) := fun i hi ↦ eq_liftBlock_toBools (hbool i hi) ▸ hE i hi
  have hl : ∀ i, i + 1 < n → readDigest (w (i + 1)) dBase = readDigest (w i) 256 := fun i hi ↦
    readDigest_congr fun e _ b _ ↦ by
      have := hlink i hi (8 * e + b) (by omega)
      rw [show dBase + (8 * e + b) = dBase + 8 * e + b by omega,
        show 256 + (8 * e + b) = 256 + 8 * e + b by omega] at this
      exact toBools_congr this
  have hc := chain_of_blocks w s hE' hl (digest_of_bits hin) (n - 1) (by omega)
  rw [digest_of_bits hout, Nat.sub_add_cancel hn] at hc
  exact hc.symm

end Sound

/-! ## Completeness -/

/-- The honest leaf table: block `i` is the honest chain block of the `i`-th digest of the chain
from `s`. -/
noncomputable def leafWitness (s : Digest) (i : ℕ) : Pos → Bool := chainTrace (chainEnd s i)

/-- The honest chain block of `d`, computed (`O(|circuit|)` Boolean operations). -/
def leafBlockBits (d : Digest) : Array Bool := fastTrace (chainInp d)

theorem leafBlockBits_eq (d : Digest) (k : Pos) :
    (leafBlockBits d)[k.val]? = some (chainTrace d k) :=
  fastTrace_eq _ k

/-- **Leaf completeness.** Over a nontrivial ring of characteristic two, the honest leaf table of
`n ≥ 1` steps from `s` meets every hypothesis of `leaf_sound` with `h = chainEnd s n`. -/
theorem leaf_complete {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (s : Digest) {n : ℕ}
    (hn : 1 ≤ n) :
    let z : ℕ → Pos → R := fun i ↦ liftBlock R (leafWitness s i)
    (∀ i < n, ∀ k, BlockR1CS.IsBool (z i k)) ∧
      (∀ i < n, HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (z i)) ∧
      ChainLinks n z s (chainEnd s n) := by
  intro z
  have hc := fun i ↦ block_complete (R := R) (chainEnd s i)
  refine ⟨fun i _ k ↦ ?_, fun i _ ↦ (hc i).1, fun i _ j hj ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · simp only [z, liftBlock, ofBool, BlockR1CS.IsBool]
    split <;> simp
  · have h1 := (readDigest_eq_iff _ _ _).mp (hc (i + 1)).2.1 j hj
    have h2 := (readDigest_eq_iff _ _ _).mp (hc i).2.2 j hj
    simp only [z, liftBlock, leafWitness]
    rw [h1, h2, chainEnd, chainEnd, Function.iterate_succ_apply']
  · have h1 := (readDigest_eq_iff _ _ _).mp (hc 0).2.1 j hj
    simp only [z, liftBlock, leafWitness]
    rw [h1, chainEnd, Function.iterate_zero, id]
  · have h2 := (readDigest_eq_iff _ _ _).mp (hc (n - 1)).2.2 j hj
    simp only [z, liftBlock, leafWitness]
    rw [h2, chainEnd, chainEnd, ← Function.iterate_succ_apply' chainStep, Nat.succ_eq_add_one,
      Nat.sub_add_cancel hn]

/-! ## Controls -/

/-- **Negative control (BP-C-M5).** The all-zero table of one block, with `s = h = 0`, has `0`/`1`
entries, satisfies the circuit's R1CS (without target, `one = 0`) and `ChainLinks`, yet
`chainEnd 0 1 ≠ 0`: it is excluded by the public target, which it fails. -/
theorem zero_table_control {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] :
    let z : ℕ → Pos → R := fun _ _ ↦ 0
    let d0 : Digest := Vector.replicate 32 0
    (∀ i < 1, ∀ k, BlockR1CS.IsBool (z i k)) ∧ (∀ i < 1, circuitR1CS.Holds (z i)) ∧
      ChainLinks 1 z d0 d0 ∧ chainEnd d0 1 ≠ d0 ∧
      ¬ (∀ i < 1, HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (z i)) := by
  intro z d0
  have hbit : ∀ j, digestBit d0 j = false := fun j ↦ by
    unfold digestBit
    split <;> simp [d0]
  refine ⟨fun _ _ _ ↦ Or.inl rfl, fun _ _ ↦ zero_holds,
    ⟨fun i hi ↦ absurd hi (by omega), fun j _ ↦ by simp [z, hbit, ofBool],
      fun j _ ↦ by simp [z, hbit, ofBool]⟩, ?_, fun h ↦ (zero_control (R := R)).2 (h 0 (by omega))⟩
  rw [chainEnd, Function.iterate_one, chainStep_zero_kat]
  intro h
  have := congrArg (fun v : Digest ↦ v[0]) h
  simp [d0] at this

end Leaf

end FR
