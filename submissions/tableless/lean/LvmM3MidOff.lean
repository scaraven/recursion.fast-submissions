/- `LvmM3MidOff` (GOLF2 off-path move, group 1 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmKeccakSpec, LvmFields, LvmFieldFacts, LvmProtoField, LvmSpineErrors, LvmBus, LvmM3Fid, LvmM3Mid,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmKeccakSpec
import LvmFields
import LvmFieldFacts
import LvmProtoField
import LvmSpineErrors
import LvmBus
import LvmM3Fid
import LvmM3Mid
import LvmMPMidTOff
import LvmTypedVEqPhasesXOff
import LvmMlListLemmas

-- ===== from `LvmKeccakSpec` =====

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters LeanVM.Semantics
namespace KeccakHash

/-- `PAD_FIRST`: the padding's first byte, after the message. -/
def padFirst : UInt8 := 0x01

/-- `PAD_LAST`: the padding's last byte, the block's last. -/
def padLast : UInt8 := 0x80

/-- The little-endian 64-bit word of bytes `8i` to `8i + 7` of a byte string, missing bytes `0`
(`u64::from_le_bytes`, `hash.rs:71-75`). -/
def littleEndianLane (bytes : List UInt8) (i : ℕ) : UInt64 :=
  (List.range 8).foldl (fun acc k ↦ acc ||| ((bytes.getD (8 * i + k) 0).toUInt64 <<<
      (8 * k).toUInt64)) 0

end KeccakHash
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters LeanVM.Semantics
namespace KeccakHash
section With
variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- Absorb one block of `136` bytes with the permutation `π`: XOR its `17` lanes into the rate,
then permute (`hash.rs:82-85`). -/
def absorbBlockWith (state : KeccakState) (block : List UInt8) : m KeccakState :=
  π (Vector.ofFn fun i ↦
    if i.val < 17 then Keccak.lane state i ^^^ littleEndianLane block i else Keccak.lane state i)

/-- The last block: the remaining `0` to `135` bytes, `PAD_FIRST` after them, zeros, and
`PAD_LAST` XORed into the block's last byte (one byte `0x81` when `135` bytes remain)
(`hash.rs:86-89`). -/
def padBlock (remainingBytes : List UInt8) : List UInt8 :=
  ((remainingBytes ++ List.replicate (rate - remainingBytes.length) 0).modify
      remainingBytes.length (· ^^^ padFirst)).modify (rate - 1) (· ^^^ padLast)

/-- Absorb `data` into `state` with `π`: `wholeBlockCount` whole blocks of `136` bytes, then the
padded last block, which holds the remaining `0` to `135` bytes. -/
def absorbWith : (wholeBlockCount : ℕ) → KeccakState → List UInt8 → m KeccakState
  | 0, state, data => absorbBlockWith π state (padBlock data)
  | wholeBlockCount + 1, state, data => do
    let state ← absorbBlockWith π state (data.take rate)
    absorbWith wholeBlockCount state (data.drop rate)

/-- **Keccak-256 over a permutation `π`**, in any monad (`keccak_hash`, `hash.rs:79-97`, with
`π` for Keccak-f[1600]): `⌊len/136⌋` whole blocks, then the padded last one, from the zero state;
the digest is the first four lanes. -/
def keccak256With (data : List UInt8) : m Digest := do
  let state ← absorbWith π (data.length / rate) (Vector.replicate 25 0) data
  pure #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2, Keccak.lane state 3]

end With
end KeccakHash
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters LeanVM.Semantics
namespace KeccakHash

/-- **Keccak-256 of a byte string** (`keccak_hash`): Keccak-256 over Keccak-f[1600]. -/
def keccak256 (data : List UInt8) : Digest :=
  Id.run (keccak256With (fun s ↦ pure (keccakF1600 s)) data)

end KeccakHash
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters LeanVM.Semantics

/-- The 32 bytes of a digest as a vector: Keccak-256's output as the model's oracle answers it. -/
def Digest.toBytes (digest : Digest) : Vector UInt8 32 :=
  ⟨(KeccakHash.digestBytes digest).toArray, by
    obtain ⟨⟨l⟩, hl⟩ := digest
    match l, hl with
    | [_, _, _, _], _ => rfl⟩

end LeanVM.Protocol
end
end

-- ===== from `LvmFields` =====

section
section
namespace LeanVM.Protocol.KeccakHash
open LeanVM.Parameters LeanVM.Semantics

/-- The eight little-endian bytes of a `K` word (`K::to_bytes`, `field.rs:60-62`). -/
def _root_.LeanVM.Parameters.K.toBytes (a : K) : List UInt8 := wordBytes a.lane

/-- The 24 bytes of an `E` word: its three limbs' bytes, `y^0` first. -/
def _root_.LeanVM.Parameters.E.toBytes (x : E) : List UInt8 :=
  K.toBytes (x.limb 0) ++ K.toBytes (x.limb 1) ++ K.toBytes (x.limb 2)

/-- A digest as the two field elements a transcript carries it in, its 128-bit halves
`E(w0, w1)`, `E(w2, w3)` (`Digest::halves`, `hash.rs:110-113`). -/
def digestHalves (digest : Digest) : E × E :=
  (E.ofLimbs (K.ofLane digest[0]) (K.ofLane digest[1]) 0,
    E.ofLimbs (K.ofLane digest[2]) (K.ofLane digest[3]) 0)

/-- The digest two field elements encode, or `none` if either has a nonzero top limb
(`Digest::from_halves`, `hash.rs:115-127`). -/
def digestFromHalves (halves : E × E) : Option Digest :=
  if IsCanonical128 halves.1 ∧ IsCanonical128 halves.2 then
    some #v[(halves.1.limb 0).lane, (halves.1.limb 1).lane, (halves.2.limb 0).lane,
      (halves.2.limb 1).lane]
  else none

end LeanVM.Protocol.KeccakHash
end
end

section
section
namespace LeanVM.Protocol.Compile
open LeanVM.Parameters LeanVM.Semantics

/-- `DS_OBSERVE`: the tag of a scalar the prover sent (`transcript.rs:17`). -/
def dsObserve : ℕ := 1

/-- `DS_POW_NONCE`: the tag of a proof-of-work nonce (`transcript.rs:18`). -/
def dsPowNonce : ℕ := 4

/-- `RATE_SCALARS`: the scalars that wait to be absorbed, four lanes each
(`transcript.rs:19-20`). -/
def rateScalars : ℕ := 4

/-- The duplex sponge: the Keccak state, and the scalars waiting to be absorbed (at most
`rateScalars`), each with its tag (`Sponge`'s `state` and `pending`, `transcript.rs:26-30`). -/
structure Sponge where
  /-- The Keccak state the last permutation left. -/
  state : KeccakState
  /-- The scalars waiting to be absorbed, each with its tag, in order. -/
  pending : List (E × ℕ)

/-- The rate lanes of the waiting scalars: each its three limbs, then its tag
(`transcript.rs:51-53`). -/
def pendingLanes (pending : List (E × ℕ)) : List UInt64 :=
  pending.flatMap fun (x, tag) ↦ [(x.limb 0).lane, (x.limb 1).lane, (x.limb 2).lane, tag.toUInt64]

/-- The input of a permutation: the waiting scalars' lanes, zeros up to lane `16`, then the
capacity, lanes `16..25` of the state (`Sponge::duplex`, `transcript.rs:49-53`). -/
def duplexInput (sponge : Sponge) : KeccakState :=
  Vector.ofFn fun i ↦
    if i.val < 16 then (pendingLanes sponge.pending).getD i 0 else Keccak.lane sponge.state i

/-- The challenge squeezed into a state: its first three lanes (`Sponge::sample`,
`transcript.rs:73`). -/
def challengeOf (state : KeccakState) : E :=
  E.ofLimbs (K.ofLane (Keccak.lane state 0)) (K.ofLane (Keccak.lane state 1))
    (K.ofLane (Keccak.lane state 2))

/-- The initial state's input: the IV's four words, the public input's four words, then zeros
(`Sponge::new`, `transcript.rs:35-37`). -/
def seedInput (iv publicInput : Digest) : KeccakState :=
  Vector.ofFn fun i ↦
    if h : i.val < 4 then iv[i.val] else if h' : i.val < 8 then publicInput[i.val - 4] else 0

end LeanVM.Protocol.Compile
end
end

section
section
namespace LeanVM.Protocol.Compile
open LeanVM.Parameters LeanVM.Semantics
section Duplex
variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- A permutation: the waiting scalars over the rate, the capacity kept, then `π`; the queue
empties (`Sponge::duplex`, `transcript.rs:48-57`). -/
def duplex (sponge : Sponge) : m Sponge := do
  let state ← π (duplexInput sponge)
  pure ⟨state, []⟩

/-- Absorb a scalar with a tag: a full queue is permuted first (`Sponge::absorb`,
`transcript.rs:59-65`). -/
def absorb (sponge : Sponge) (x : E) (tag : ℕ) : m Sponge := do
  let sponge ← if sponge.pending.length = rateScalars then duplex π sponge else pure sponge
  pure { sponge with pending := sponge.pending ++ [(x, tag)] }

/-- Squeeze a challenge: a permutation, then the new state's first three lanes (`Sponge::sample`,
`transcript.rs:71-74`). -/
def squeeze (sponge : Sponge) : m (E × Sponge) := do
  let sponge ← duplex π sponge
  pure (challengeOf sponge.state, sponge)

end Duplex
end LeanVM.Protocol.Compile
end
end

-- ===== from `LvmFieldFacts` =====

section
namespace LeanVM.Parameters
section
open CompPoly.Extension

/-- The canonical word of a two-limb cell, `c0 + c1·y`: the cell shape `KECCAK` reads and writes. -/
def E.ofCell (v : Vector K 2) : E := E.ofLimbs v[0] v[1] 0

end
end LeanVM.Parameters
end

section
namespace LeanVM.Parameters
section
open CompPoly.Extension

/-- `ofK a` is the word with limbs `(a, 0, 0)`. -/
theorem ofK_eq_ofLimbs (a : K) : ofK a = E.ofLimbs a 0 0 :=
  E.ext fun i ↦ by fin_cases i <;> simp

/-- A word with zero upper limbs lies in `K`. -/
theorem isInK_ofLimbs (c : K) : IsInK (E.ofLimbs c 0 0) := ⟨by simp, by simp⟩

/-- A word in `K` is its low limb with zeros above. -/
theorem ofLimbs_of_isInK {x : E} (h : IsInK x) : E.ofLimbs (x.limb 0) 0 0 = x :=
  calc E.ofLimbs (x.limb 0) 0 0 = E.ofLimbs (x.limb 0) (x.limb 1) (x.limb 2) := by rw [h.1, h.2]
    _ = x := ofLimbs_limb x

/-- A single-limb word is zero exactly when its limb is. -/
theorem ofLimbs_eq_zero_iff (c : K) : E.ofLimbs c 0 0 = 0 ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg (fun z : E ↦ z.limb 0) h
    simpa only [limb_ofLimbs, limb_zero, Matrix.cons_val_zero] using this
  · rintro rfl
    exact E.ext fun i ↦ by rw [limb_zero]; fin_cases i <;> simp

/-- The sum of two words, limb by limb: addition in `E` is bitwise `XOR` in each limb, never
integer addition with carries (the `XOR` table's result coordinates, specification §7.1). -/
theorem add_limbs (a0 a1 a2 b0 b1 b2 : K) :
    E.ofLimbs a0 a1 a2 + E.ofLimbs b0 b1 b2 = E.ofLimbs (a0 + b0) (a1 + b1) (a2 + b2) :=
  E.ext fun i ↦ by rw [limb_add]; fin_cases i <;> simp

/-- The product of two words, limb by limb: the twelve products over the nine limb pairs,
folded by `y^3 = y + 1` into three lanes (the `MUL_NATIVE` table's result coordinates,
specification §7.2; the pinned Rust's `TOWER_LANES`). -/
theorem mul_limbs (a0 a1 a2 b0 b1 b2 : K) :
    E.ofLimbs a0 a1 a2 * E.ofLimbs b0 b1 b2 =
      E.ofLimbs (a0 * b0 + a1 * b2 + a2 * b1)
        (a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2)
        (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) := by
  simp only [ofLimbs_eq, ofK_add, ofK_mul]
  -- The product is `p₀ + p₁·y + p₂·y² + p₃·y³ + p₄·y⁴`; `y³ = y + 1` folds `p₃` and `p₄`.
  linear_combination (ofK a1 * ofK b2 + ofK a2 * ofK b1 + ofK a2 * ofK b2 * y) * y_pow_three

end
end LeanVM.Parameters
end

-- ===== from `LvmProtoField` =====

section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly
section

/-- `K` as the `2^64` bit patterns, the `BitVec` view of `Fin (2^64)`. -/
def finEquivK : Fin (2 ^ 64) ≃ K where
  toFun := fun i ↦ BF64.ofBitVec (BitVec.ofFin i)
  invFun := fun x ↦ x.toBitVec.toFin
  left_inv _ := rfl
  right_inv _ := rfl

/-- `E` as its three limbs, CompPoly's carrier view. -/
def limbsEquiv : Vector K 3 ≃ E where
  toFun := fun v ↦ CompPoly.Extension.Ext.ofVector (P := BF64.ext3Params) v
  invFun := fun x ↦ CompPoly.Extension.Ext.coeffs (P := BF64.ext3Params) x
  left_inv _ := rfl
  right_inv _ := rfl

end
end LeanVM.Protocol
end

section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly
section

/-- The answer to the equality kernel at `p` is the column's extension at `p`. -/
theorem answer_eqWeight {n : ℕ} (q : Column n) (p : Vector E n) :
    (eqWeight p).pair (algebraMap K E) q.values =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) p :=
  Weight.pair_eqWeight (algebraMap K E) p q.values

end
end LeanVM.Protocol
end

-- ===== from `LvmSpineErrors` =====

section
namespace LeanVM.Protocol
open LeanVM.Parameters
open scoped NNReal
section

theorem overE_add (a b : ℕ) : overE (a + b) = overE a + overE b := by
  simp only [overE, Nat.cast_add, add_div]

theorem nat_mul_overE (n c : ℕ) : (n : ℝ≥0) * overE c = overE (n * c) := by
  simp only [overE, Nat.cast_mul]
  ring

/-- The unit `overE 1` is `1 / |E|` with `|E|` counted by `Nat.card`, the form of a generic
component's error. -/
theorem overE_one : overE 1 = (1 / Nat.card E : ℝ≥0) := by
  rw [overE, Nat.card_eq_fintype_card, Nat.cast_one]

/-- `k / |E|` with `|E|` counted by `Nat.card`, the form a generic component's error takes, is
`overE k`. -/
theorem natCast_div_card_eq_overE (k : ℕ) : ((k : ℝ≥0) / Nat.card E) = overE k := by
  rw [overE, Nat.card_eq_fintype_card]

end
end LeanVM.Protocol
end

-- ===== from `LvmBus` =====

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped ENNReal
section

/-- **Lemma 5.2**: the product polynomial determines the multiset of tuples. -/
theorem sideProduct_poly_eq_iff (P Q : Multiset (Vector K 16)) :
    grandProductPoly (n := 4) P = grandProductPoly (n := 4) Q ↔ P = Q :=
  ⟨fun h ↦ grandProductPoly_injective h, congrArg _⟩

end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped ENNReal
section

/-- **Theorem 5.1**: two different multisets of at most `N` tuples each have equal products at
a uniform challenge `(α, β)` with probability at most `4·N / |E|` (lvm: the probability of the
source, a VCVio uniform draw, restated as the fraction of the challenges in `(Fin 4 → E) × E`). -/
theorem sideProduct_collision {P Q : Multiset (Vector K 16)} (hne : P ≠ Q) {N : ℕ}
    (hP : P.card ≤ N) (hQ : Q.card ≤ N) :
    (Nat.card {ab : (Fin 4 → E) × E // sideProduct ab.1 ab.2 P = sideProduct ab.1 ab.2 Q} :
        ℝ≥0∞) / (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞) ≤
      (4 * N : ℕ) / (Fintype.card E : ℝ≥0∞) := by
  classical
  have hcard : Fintype.card ((Fin 4 → E) × E) = Fintype.card E * Fintype.card E ^ 4 := by
    simp [mul_comm]
  have hdiv : ((4 * N : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) =
      ((4 * N * Fintype.card E ^ 4 : ℕ) : ℝ≥0∞) / (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞) := by
    rw [hcard, Nat.cast_mul (4 * N), Nat.cast_mul (Fintype.card E),
      ENNReal.mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (pow_ne_zero _ Fintype.card_ne_zero))
        (ENNReal.natCast_ne_top _)]
  rw [hdiv]
  have h := card_sideProduct_collision_le hne hP hQ
  rw [Nat.card_eq_fintype_card (α := E)] at h
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr h) _

end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
section

/-- Reading through a renamed lift is reading the renamed column, cast to its height. -/
private theorem Layout.readWith_comap {μ : ℕ} {ι ι' : Type} {κ : ι → ℕ} {κ' : ι' → ℕ}
    (extend : (c : ι) → Vector E (κ c) → Vector E μ) (f : ι' → ι) (h : ∀ c, κ (f c) = κ' c)
    (q : Column μ) (c : ι') :
    Layout.readWith (fun c z ↦ extend (f c) (Vector.cast (h c).symm z)) q c =
      ⟨Vector.cast (congrArg (2 ^ ·) (h c)) (Layout.readWith extend q (f c)).values⟩ := by
  unfold Layout.readWith
  congr 1
  apply Vector.ext
  intro x hx
  simp only [Vector.getElem_cast, Vector.getElem_ofFn, boolVec_cast]
  rfl

/-- A layout read through a renaming of its columns that keeps their heights. -/
def Layout.comap {μ : ℕ} {ι ι' : Type} {κ : ι → ℕ} {κ' : ι' → ℕ} (L : Layout μ ι κ)
    (f : ι' → ι) (h : ∀ c, κ (f c) = κ' c) : Layout μ ι' κ' where
  extend := fun c z ↦ L.extend (f c) (Vector.cast (h c).symm z)
  read_eval := fun q c z ↦ by
    rw [Layout.readWith_comap L.extend f h]
    have hz : z = Vector.cast (h c) (Vector.cast (h c).symm z) := by simp
    conv_lhs => rw [hz]
    rw [eval₂Mle_cast, L.read_eval]

/-- The union of two layouts: a left column is read through `L₁`, a right column through
`L₂`. -/
def Layout.piecewise {μ : ℕ} {ι₁ ι₂ : Type} {κ₁ : ι₁ → ℕ} {κ₂ : ι₂ → ℕ} (L₁ : Layout μ ι₁ κ₁)
    (L₂ : Layout μ ι₂ κ₂) : Layout μ (ι₁ ⊕ ι₂) (Sum.elim κ₁ κ₂) where
  extend
    | .inl c => L₁.extend c
    | .inr c => L₂.extend c
  read_eval q
    | .inl c => L₁.read_eval q c
    | .inr c => L₂.read_eval q c

end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
section
namespace Blocks
section Columns
variable (B : Blocks) {μ : ℕ}

/-- The columns stacked on `μ` variables, zero past the last block: the witness stack (§4.1). -/
def stackColumn (t : B.Tables K) (μ : ℕ) : Column μ := ⟨B.stackAt t μ 0⟩

end Columns
end Blocks
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
section
namespace Blocks
section Columns
variable (B : Blocks) {μ : ℕ}

/-- The cell a cube point of block `b` lifts to: the point's index plus the block's offset. -/
theorem get_extendPoint (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n)
    (y : Fin (2 ^ B.size b)) :
    q.values.get (boolIndex (B.extendPoint hμ b (boolVec y : Vector E (B.size b)))) =
      q.values[y.val + B.offset b]'(by
        have := B.offset_add_pow_le_total b
        have := y.isLt
        omega) := by
  simp only [extendPoint, boolVec_append, boolIndex_cast, boolIndex_boolVec,
    Vector.get_eq_getElem, Fin.val_cast, cubeIndex_val, selector_val]
  congr 1
  exact congrArg (y.val + ·) (Nat.mul_div_cancel' (B.pow_size_dvd_offset b))

end Columns
end Blocks
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
section
namespace Blocks
section Columns
variable (B : Blocks) {μ : ℕ}

/-- A slice's cell `x` is the block's cell `x + slot · 2 ^ κ`, at the block's offset. -/
theorem get_sliceLayout (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (k : ℕ) {ι : Type}
    {κ : ι → ℕ} (slot : ι → Fin (2 ^ k)) (h : ∀ c, B.size b = κ c + k) (q : Column μ) (c : ι)
    (x : Fin (2 ^ κ c)) :
    q.values.get (boolIndex ((B.sliceLayout hμ b k slot h).extend c (boolVec x))) =
      q.values[(cubeIndex x (slot c)).val + B.offset b]'(by
        have := B.offset_add_pow_le_total b
        have h1 := (cubeIndex x (slot c)).isLt
        have h2 : 2 ^ (κ c + k) = 2 ^ B.size b := by rw [h c]
        omega) := by
  simp only [sliceLayout, boolVec_append, boolVec_cast, get_extendPoint, Fin.val_cast]

end Columns
end Blocks
end
end LeanVM.Protocol
end
end

section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal
noncomputable section

/-- The count side's leaf stack: the tables' count columns, padded with `1`. -/
abbrev countLeaves (I : M3Instance) (q : Column I.μ) : CMlPolynomialEval E I.μBus :=
  Bus.sideLeaves I 2 0 0 q

end
end LeanVM.Protocol
end

section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal
noncomputable section
namespace Bus
variable (I : M3Instance)
variable {I}
variable (I)
variable {I}
variable (I)
variable {I}

/-- With honest padding rows, every padding leaf is `1`. -/
theorem padProduct_of_honest {q : Column I.μ} (hp : I.PaddingHonest q) (α : Fin 4 → E)
    (s : Side) : padProduct α (sidePadTuples I q s) = 1 := by
  rw [padProduct, sidePadTuples, Multiset.map_coe, Multiset.prod_coe]
  refine List.prod_eq_one fun e he ↦ ?_
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
  obtain ⟨src, -, hu⟩ := List.mem_flatMap.mp hu
  cases src with
  | flush j f =>
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
    have hrow := hp j x (of_decide_eq_true (List.mem_filter.mp hx).2)
    rw [padDiff, fingerprint_one_sub_add]
    simp only [flushTuple, hrow, padTuple]
    ring
  | boundary b => cases hu
  | count j c => cases hu

end Bus
end
end LeanVM.Protocol
end

section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal
noncomputable section
namespace Bus
variable (I : M3Instance)
variable {I}
variable (I)
variable {I}
variable (I)
variable {I}

/-- With honest padding rows and nonzero executed counts, the count side's product is nonzero. -/
theorem prod_countLeaves_ne_zero (h : Conditions I) (α : Fin 4 → E) (β : E) {q : Column I.μ}
    (hp : I.PaddingHonest q) (hn : I.CountsNonzero q) :
    ∏ x : Fin (2 ^ I.μBus), (sideLeaves I 2 α β q)[x] ≠ 0 := by
  rw [prod_sideLeaves 2 α β q (h.fits 2)]
  refine List.prod_ne_zero fun h0 ↦ ?_
  obtain ⟨src, hs, h0⟩ := List.mem_map.mp h0
  change src ∈ countSources I at hs
  simp only [countSources, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
  obtain ⟨j, c, hc, rfl⟩ := hs
  obtain ⟨x, -, hx⟩ := Finset.prod_eq_zero_iff.mp h0
  change ofK ((I.column q ⟨j, c⟩).values.get x) + padInd j x * (1 - ofK (I.padRow j c)) = 0
    at hx
  by_cases hr : I.rows j ≤ x.val
  · have hcell : (I.column q ⟨j, c⟩).values.get x = I.padRow j c :=
      congrFun (hp j x hr) c
    have hi : padInd j x = 1 := by simp [padInd, hr]
    rw [hcell, hi, one_mul, add_sub_cancel] at hx
    exact one_ne_zero hx
  · have hi : padInd j x = 0 := by simp [padInd, hr]
    rw [hi, zero_mul, add_zero] at hx
    exact hn j c hc x (Nat.not_le.mp hr)
      ((map_eq_zero_iff (algebraMap K E) (algebraMap K E).injective).mp hx)

end Bus
end
end LeanVM.Protocol
end

section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal
noncomputable section
namespace Bus
variable (I : M3Instance)
variable {I}
variable (I)
variable {I}
variable (I)
variable {I}
variable (I)
variable {I}
variable (I)
variable {I}

/-- The honest prover's values: each boundary column's extension at its point. -/
def honestValues (h : Conditions I) (q : Column I.μ) (ζ : Vector E I.μBus) :
    Vector E I.busClaims :=
  Vector.ofFn fun i ↦ eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E)
    (columnPoint h ζ i)

end Bus
end
end LeanVM.Protocol
end

section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal
noncomputable section
namespace Bus
variable {I : M3Instance}
variable (I)
variable {I}

/-- On a balanced bus with honest padding rows the two products agree at every `(α, β)`, and the
count product is nonzero. -/
theorem challenge_honest (h : Conditions I) (s : I.Stmt) (o : ∀ i, TheOracle I i) (w : Unit)
    (hin : ((s, o), w) ∈ Seam.commitHonest I) :
    (fun _ ↦ true) s = true ∧ ∀ ab : (Fin 4 → E) × E, (((s, ab), o), w) ∈ afterChallenge I := by
  obtain ⟨⟨hc, hb, hn, hl, ha⟩, hp⟩ := hin
  refine ⟨rfl, fun ab ↦ ⟨?_, prod_countLeaves_ne_zero h _ _ hp hn, hc, hl, ha⟩⟩
  change ∏ x : Fin (2 ^ I.μBus), (pushLeaves I ab.1 ab.2 (theStack o))[x] =
    ∏ x : Fin (2 ^ I.μBus), (pullLeaves I ab.1 ab.2 (theStack o))[x]
  rw [prod_pushLeaves, prod_pullLeaves h, padProduct_of_honest hp, padProduct_of_honest hp,
    Multiset.coe_eq_coe.mpr hb]

/-- The honest roots are the products, the count root is nonzero, and every rider is zero. -/
theorem roots_honest (h : Conditions I) (x : Data I) (o : ∀ i, TheOracle I i) (w : Unit)
    (hin : ((x, o), w) ∈ afterChallenge I) :
    decide ((rootsHonest I ((x, o), w)).2 ≠ 0) = true ∧
      (((x, ![(rootsHonest I ((x, o), w)).1, (rootsHonest I ((x, o), w)).1,
        (rootsHonest I ((x, o), w)).2]), o), w) ∈ Gkr.relIn 3 I.μBus (leaves I) (riders I) := by
  obtain ⟨hp, hn, hc, hl, ha⟩ := hin
  refine ⟨decide_eq_true hn,
    (ridersZero_iff h x o).mpr ⟨hc, hl, ha⟩, fun s ↦ ?_⟩
  fin_cases s
  · rfl
  · exact hp
  · rfl

/-- The honest values are the boundary columns' extensions. -/
theorem honestValues_getElem (h : Conditions I) (q : Column I.μ) (ζ : Vector E I.μBus)
    (i : Fin I.busClaims) :
    (honestValues h q ζ)[i] =
      eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E) (columnPoint h ζ i) := by
  simp [honestValues]

/-- The honest values are the boundary columns' extensions: the leaf claims force the forms to
the totals, and the riders' vanishing gives the zerocheck clause. -/
theorem values_honest (h : Conditions I) (ℓ : Gkr.LayerStmt (Data I) E 3 I.μBus)
    (o : ∀ i, TheOracle I i) (w : Unit)
    (hout : ((ℓ, o), w) ∈ Gkr.relOut 3 I.μBus (leaves I) (riders I)) :
    (fun (_ : Gkr.LayerStmt (Data I) E 3 I.μBus) (_ : Vector E I.busClaims) ↦ true) ℓ
        (honestValues h (theStack o) ℓ.2.1) = true ∧
      (((ℓ.1.1, busOut h ℓ (honestValues h (theStack o) ℓ.2.1)), o), w) ∈ Seam.bus I := by
  obtain ⟨hleaf, hr⟩ := hout
  obtain ⟨hcons, hl, ha⟩ := (riders_vanish_iff ℓ.1 o ℓ.2.1).mp hr
  refine ⟨rfl, ?_, ?_, ?_, hl, ha⟩
  · intro j C hC
    rw [show (busOut h ℓ (honestValues h (theStack o) ℓ.2.1)).point = point h ℓ.2.1 from rfl,
      lowPoint_point]
    exact hcons j.1 ((I.τ_le_τmax j).trans h.τmax_le) C hC
  · intro side
    exact (sum_forms_eq_total_iff h side _ _ _ _ _ _
      (honestValues_getElem h (theStack o) ℓ.2.1)).mpr (hleaf side)
  · intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa [busOut] using hc)
    exact (honestValues_getElem h (theStack o) ℓ.2.1 i).symm

end Bus
end
end LeanVM.Protocol
end

-- ===== from `LvmM3Fid` =====

section
section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open CompPoly CMlPolynomialEval
open scoped NNReal ENNReal
section

/-- The deployed verifier computes the fixed polynomial's value (`Bytecode::evaluate`,
`crates/verifier/src/bytecode.rs:99-136`, the same value by a sparse sum). lvm (WP-2): restated
from `Statement.LeanVmVerifier` (the leanVM verifier proper, cut from `LvmVCore`). -/
def _root_.LeanVM.Protocol.Verifier.computedBytecodeValue (words : List K) (point : List E) :
    VerifierProgram E :=
  pure (multilinearEval (words.map ofK) point)

end
end LeanVM.Protocol.EndToEnd.Front
end
end

section
section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open CompPoly CMlPolynomialEval
open scoped NNReal ENNReal
section
variable {εmax : ℝ≥0∞}
section Phase

/-- The bus phase after the grand product, followed by `k`: the count root's check, the boundary
values, and `k` of what was read. -/
def busTailK {β : Type} (k : BusWit → VerifierProgram β) (alphas : List E) (beta : E)
    (r : E × List E × List E) : VerifierProgram β :=
  match r with
  | (countRoot, point, values) => do
    VerifierProgram.require (countRoot ≠ 0)
    let memory ← VerifierProgram.readScalars 3
    let mf ← VerifierProgram.readScalar
    let bf ← VerifierProgram.readScalar
    k ⟨alphas, beta, point, values, memory, mf, bf⟩

/-- **The bus phase followed by `f`** is the fingerprint challenges, the grand product at the push
side's depth, and the tail followed by `f` of the result. -/
theorem verifyBusBalance_bind_eq {β : Type} (tables : List Verifier.Table) (layout : Verifier.Layout) (f : BusResult →
    VerifierProgram β) :
    (verifyBusBalance tables computedBytecodeValue layout).bind f =
      abProg.bind fun ab ↦ (verifyGkrGrandProducts
        (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth).bind
        (busTailK (fun w ↦ f (w.result tables layout)) ab.1 ab.2) := by
  unfold verifyBusBalance computedBytecodeValue abProg busTailK BusWit.result
  simp only [VerifierProgram.bind_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind,
      VerifierProgram.pure_eq]
  rfl

end Phase
end
end LeanVM.Protocol.EndToEnd.Front
end
end

section
section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open CompPoly CMlPolynomialEval
open scoped NNReal ENNReal
section
variable {εmax : ℝ≥0∞}
section Phase
variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (tables : List Verifier.Table) (layout : Verifier.Layout)

/-- **The bus seam on the wire, at what was read**: no candidate puts the protocol's output on
those values in the bus seam. -/
def BusAt (w : BusWit) (h : List Ev) : Prop :=
  w.point.length = I.μBus ∧ w.values.length = 3 ∧ w.memory.length = 3 ∧
    HDoom cands (Seam.bus I) (input, Bus.busOut hI (w.layer I input) (w.vals I)) h

/-- **The bus seam on the wire**: the bus phase returns the verifier's leaf decomposition of what it
read, and the bus seam holds of no candidate at the protocol's output on it. -/
def BusPost (bus : BusResult) (h : List Ev) : Prop :=
  ∃ w : BusWit, bus = w.result tables layout ∧ BusAt I hI cands input w h

end Phase
end
end LeanVM.Protocol.EndToEnd.Front
end
end

section
section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open CompPoly CMlPolynomialEval
open scoped NNReal ENNReal
section
variable {εmax : ℝ≥0∞}
section Phase
variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (tables : List Verifier.Table) (layout : Verifier.Layout)
variable {εmax : ℝ≥0∞}

/-- **The bus phase's tail, then a continuation** specified from the bus seam at what was read:
the count root's check (which rejects the root `0`), the boundary values (the protocol's last
message), then `k`. -/
noncomputable def busTailSpec {β : Type} {k : BusWit → VerifierProgram β} {Q : β → List Ev → Prop}
    {Lk T : ℝ≥0∞} (hLk : Lk ≤ εmax) (K : ∀ w, Spec (k w) (BusAt I hI cands input w) Q εmax Lk T)
    (alphas : List E) (beta : E) (r : E × List E × List E) :
    Spec (busTailK k alphas beta r) (GkrPost I cands (input, (toAlpha alphas, beta)) r) Q
      εmax 0 T :=
  match r with
  | (countRoot, point, values) =>
    let P : List Ev → Prop := fun h ↦ point.length = I.μBus ∧ values.length = 3 ∧
      HDoom cands (Gkr.relOut 3 I.μBus (Bus.leaves I) (Bus.riders I))
        (layerStmtOf (input, (toAlpha alphas, beta)) I.μBus ⟨values, point⟩) h
    have hP : ∀ h x, P h → P (h ++ [Ev.read x]) := fun _ _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.append _⟩
    (Spec.require (Post := fun _ h ↦ P h) fun _ hp hc ↦ hp.resolve_left hc).bind' fun _ ↦
    (readNSuccSpec P hP zero_le 2).bind' fun memory ↦
    (Spec.readE (Post := fun _ h ↦ memory.length = 3 ∧ P h)
      (fun _ _ hp ↦ ⟨hp.1, hP _ _ hp.2⟩) zero_le).bind' fun mf ↦
    (Spec.readE (Post := fun bf h ↦ BusAt I hI cands input ⟨alphas, beta, point, values, memory,
        mf, bf⟩ h)
      (fun _ bf hp ↦ by
        obtain ⟨hm, hl, hv, W, hW, hR⟩ := hp
        exact ⟨hl, hv, hm, W, firstWord_append hW _, values_keep I hI hR _⟩) hLk).bind'
      fun bf ↦ K ⟨alphas, beta, point, values, memory, mf, bf⟩

/-- **The bus phase, then a continuation** (`verify_bus_balance`, `bus.rs:106-213`): from
the commitment's doom (no candidate satisfies `M3Holds`, `Seam.commit`) to the bus seam at what
was read, then `f` of the result, specified from there by `K`, at the depth `μ_bus` of the push
side. The fingerprint challenges are charged `L₀ · 4 · 2^{μ_bus} / |E|`; every later group of
challenges (a sumcheck round's, the descendants' combination challenges with the next combiner)
at most `L₀ · 4 / |E|`. -/
noncomputable def busThenSpec {β : Type} {f : BusResult → VerifierProgram β} {Q : β → List Ev
    → Prop}
    {Lk T : ℝ≥0∞} (hLk : Lk ≤ εmax)
    (K : ∀ w : BusWit, Spec (f (w.result tables layout)) (BusAt I hI cands input w) Q εmax Lk T)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) :
    Spec ((verifyBusBalance tables computedBytecodeValue layout).bind f) (HDoom cands (Seam.commit I)
        input) Q εmax
      (abError I L₀ + 0) T :=
  Spec.congr (verifyBusBalance_bind_eq tables layout f).symm
    ((abSpec I cands input hI hfin hcard hab (T := 0)).bind' fun ab ↦
      (Spec.congr (by rw [hdepth])
        (gkrSpec I cands (input, (toAlpha ab.1, ab.2)) hI hfin hcard hμ he hT hlam)).bind'
        fun r ↦ busTailSpec I hI cands input hLk K ab.1 ab.2 r)

/-- **The bus phase** alone: from the commitment's doom to the bus seam on the wire. -/
noncomputable def busPhaseSpec {T : ℝ≥0∞} (hTf : T ≤ εmax) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) :
    Spec (verifyBusBalance tables computedBytecodeValue layout) (HDoom cands (Seam.commit I) input)
      (BusPost I hI cands input tables layout) εmax (abError I L₀ + 0) T :=
  Spec.congr (VerifierProgram.bind_ret _)
    (busThenSpec I hI cands input tables layout hTf
      (fun w ↦ (Spec.ret (Post := BusPost I hI cands input tables layout) (w.result tables layout)).mono
        (fun _ hp ↦ ⟨w, rfl, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
      hfin hcard hμ hdepth hab he hT hlam)

end Phase
end
end LeanVM.Protocol.EndToEnd.Front
end
end

section
section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
open scoped Polynomial
section
namespace Sumcheck
section Def
variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type} {n m : ℕ}

/-- The weights `(1 - p_k, p_k)` of a point `p` of the public data: the sum against
`eq(p, ·)`. -/
def eqWeights (pt : X → Vector F n) : CoordWeights F X n := fun x k ↦ (1 - (pt x)[k], (pt x)[k])

end Def
end Sumcheck
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
open scoped Polynomial
section
namespace Sumcheck
section Def
variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type} {n m : ℕ}
variable [DecidableEq F]

/-- The default output: the final point, in coordinate order, and the values sent. -/
def finalOut (s : SumcheckRound.Stmt X F n) (v : Vector F m) : Out X F n m :=
  (s.1, (s.2.1.reverse, v))

end Def
end Sumcheck
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
open scoped Polynomial
section
namespace Sumcheck
section Complete
variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type} {n m : ℕ}
  (V : Virtual F X O W n m) (wt : CoordWeights F X n)
variable {d : ℕ} (nodes : Fin (d + 1) → F)
variable (side : SumcheckRound.Ctx X O W → Prop)

/-- The family's relation before the first round is the input relation. -/
theorem rel_zero : SumcheckRound.rel (family V wt nodes side) 0 = relIn V wt side := by
  ext p
  have hc : p.1.1.2.1 = #v[] := Vector.ext fun i hi ↦ absurd hi (Nat.not_lt_zero i)
  simp only [SumcheckRound.rel, family, relIn, Set.mem_ofPred_eq, hc]
  rw [claim_zero, and_comm]

/-- The family's relation after the last round: the side condition, and the running claim is the
summand at the challenges in coordinate order. -/
theorem mem_rel_self (p : (SumcheckRound.Stmt X F n × ∀ i, O i) × W) :
    p ∈ SumcheckRound.rel (family V wt nodes side) n ↔
      side (SumcheckRound.ctxOf p) ∧
        p.1.1.2.2 = V.summand (SumcheckRound.ctxOf p) p.1.1.2.1.reverse := by
  simp only [SumcheckRound.rel, family, Set.mem_ofPred_eq]
  rw [claim_self]

end Complete
end Sumcheck
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
open scoped Polynomial
section
namespace Sumcheck
section Complete
variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type} {n m : ℕ}
  (V : Virtual F X O W n m) (wt : CoordWeights F X n)
variable {d : ℕ} (nodes : Fin (d + 1) → F)
variable (side : SumcheckRound.Ctx X O W → Prop)
variable [DecidableEq F]

/-- The true values at the final point pass the final check and land in an output relation they
land in whenever the side condition holds. -/
theorem final_honest {T : Type} (out : SumcheckRound.Stmt X F n → Vector F m → T)
    {relOut' : Set ((T × ∀ i, O i) × W)}
    (h : ∀ s o w, side ((s.1, o), w) →
      ((out s (V.values ((s.1, o), w) s.2.1.reverse), o), w) ∈ relOut')
    (s : SumcheckRound.Stmt X F n) (o : ∀ i, O i) (w : W)
    (hin : ((s, o), w) ∈ SumcheckRound.rel (family V wt nodes side) n) :
    finalCheck V s (V.values ((s.1, o), w) s.2.1.reverse) = true ∧
      ((out s (V.values ((s.1, o), w) s.2.1.reverse), o), w) ∈ relOut' := by
  obtain ⟨hside, hclaim⟩ := (mem_rel_self V wt nodes side _).mp hin
  refine ⟨?_, h s o w hside⟩
  rw [finalCheck, decide_eq_true_eq, hclaim]
  rfl

end Complete
end Sumcheck
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
open scoped Polynomial
section
namespace Sumcheck
section Security
variable {F : Type} [Field F] [DecidableEq F]
  {X : Type} {ι : Type} {O : ι → Type} {W : Type}
  {n m : ℕ} (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
  (nodes : Fin (d + 1) → F) (side : SumcheckRound.Ctx X O W → Prop)

/-- Values that pass the final check, for an output relation from which they are the tables'
values at the final point and the side condition holds, make the running claim the summand at
the point. -/
theorem final_reflect {T : Type} (out : SumcheckRound.Stmt X F n → Vector F m → T)
    {relOut' : Set ((T × ∀ i, O i) × W)}
    (h : ∀ s o w v, ((out s v, o), w) ∈ relOut' →
      V.values ((s.1, o), w) s.2.1.reverse = v ∧ side ((s.1, o), w))
    (s : SumcheckRound.Stmt X F n) (o : ∀ i, O i) (w : W) (v : Vector F m)
    (hc : finalCheck V s v = true) (hout : ((out s v, o), w) ∈ relOut') :
    ((s, o), w) ∈ SumcheckRound.rel (family V wt nodes side) n := by
  obtain ⟨hv, hside⟩ := h s o w v hout
  rw [mem_rel_self V wt nodes side]
  rw [finalCheck, decide_eq_true_eq] at hc
  refine ⟨hside, ?_⟩
  rw [← hc]
  exact congrArg (V.formula s.1 s.2.1.reverse) hv.symm

omit [DecidableEq F] in
/-- The family is sound: its invariant, the side condition, is the same at every stage, so no
challenge restores it (lvm: the fact leanVM's cut `roundsSecurity` passes to
`SumcheckRound.roundsSecurity`; with `family_honest` it gives `SumcheckRound.card_badChallenge_le`
for each round). -/
theorem family_sound [Finite F] : (family V wt nodes side).Sound n :=
  fun _ _ _ _ h ↦ (Nat.card_eq_zero.mpr (Or.inl ⟨fun x ↦ h x.2⟩)).trans_le (Nat.zero_le d)

/-- The count behind the cut `roundsSecurity` (lvm, new): at each round `j < n` of the sumcheck of
a summand of degree at most `d` in each variable, a recorded polynomial that passes the check has
at most `d` bad challenges, among the `|F|` the verifier may draw. -/
theorem card_badChallenge_le [Finite F] [Subsingleton W]
    (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d) (hnodes : Function.Injective nodes)
    {j : ℕ} (hj : j < n) (p : SumcheckRound.MidStmt X F j d) (o : ∀ i, O i)
    (hc : SumcheckRound.check j (family V wt nodes side).weight p.1 p.2 = true) :
    Nat.card {x // SumcheckRound.badChallenge j (family V wt nodes side) p o x} ≤ d :=
  SumcheckRound.card_badChallenge_le j (family V wt nodes side)
    (family_honest V wt nodes side hV hnodes).toConsistent (family_sound V wt nodes side) hj p o hc

end Security
end Sumcheck
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
open scoped Polynomial
section
namespace Sumcheck
section Wire
variable {F : Type} [Field F] {d : ℕ}

/-- The weight of coefficient `i` in a round's check: `Σ_{(x, w)} w · x^i` over the domain. -/
def coeffWeight (dom : SumcheckRound.WeightedDomain F) (i : ℕ) : F :=
  (dom.map fun p ↦ p.2 * p.1 ^ i).sum

/-- The round's check is linear in the coefficients, coefficient `i` weighted by
`coeffWeight dom i`. -/
theorem weightedSum_eq_sum (dom : SumcheckRound.WeightedDomain F) (q : SumcheckRound.Message F d) :
    SumcheckRound.weightedSum d dom q = ∑ i : Fin (d + 1), q[i] * coeffWeight dom i := by
  simp only [SumcheckRound.weightedSum, SumcheckRound.evaluate, coeffWeight]
  induction dom with
  | nil => simp
  | cons p dom ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.mul_sum]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The message with coefficient `k` derived from the running claim: the value that makes the
round's check hold, whatever the message carried there. -/
def decodeRound (dom : SumcheckRound.WeightedDomain F) (k : Fin (d + 1)) (claim : F)
    (q : SumcheckRound.Message F d) : SumcheckRound.Message F d :=
  q.set k ((claim - ∑ i ∈ Finset.univ.erase k, q[i] * coeffWeight dom i) / coeffWeight dom k)

end Wire
end Sumcheck
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
open scoped Polynomial
section
namespace Sumcheck
section Wire
variable {F : Type} [Field F] {d : ℕ}
variable {X : Type} {ι : Type} {O : ι → Type}

/-- The wire's message: the coefficients but coefficient `k`, in order. -/
def encodeWire (k : Fin (d + 1)) (q : SumcheckRound.Message F d) : Vector F d :=
  Vector.ofFn fun i : Fin d ↦ if i.val < k.val then q[i.val] else q[i.val + 1]

/-- The coefficients read off the wire, with `0` in position `k`. -/
def expandWire (k : Fin (d + 1)) (w : Vector F d) : SumcheckRound.Message F d :=
  Vector.ofFn fun i : Fin (d + 1) ↦
    if h : i.val < k.val then w[i.val]'(by omega)
    else if h' : i.val = k.val then 0 else w[i.val - 1]'(by omega)

/-- The round message decoded from the wire: coefficient `k` derived from the running claim. -/
def decodeWire (dom : SumcheckRound.WeightedDomain F) (k : Fin (d + 1)) (claim : F)
    (w : Vector F d) : SumcheckRound.Message F d :=
  decodeRound dom k claim (expandWire k w)

end Wire
end Sumcheck
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal
noncomputable section
namespace TableSumcheck
variable (I : M3Instance)

/-- The true values at the final point land in the table seam whenever the side condition holds:
the bus phase's claims carried forward hold, and so do the final claims. -/
theorem tableOut_mem_table (s : SumcheckRound.Stmt (Data I) E I.τmax) (o : ∀ i, TheOracle I i)
    (hside : side I ((s.1, o), ())) :
    ((tableOut I s ((tableSummand I).values ((s.1, o), ()) s.2.1.reverse), o), ()) ∈
      Seam.table I := by
  refine ⟨fun c hc ↦ ?_, hside.2.1, I.auxAt_of_aux hside.2.2 _⟩
  simp only [tableOut, Vector.toList_append, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hside.1 c hc
  · exact (finalClaims_holds_iff I ((s.1, o), ()) _ _).mpr rfl c hc

/-- From the bus seam, the combined claimed values are the combination of the true ones at every
challenge, and the side condition holds. -/
theorem batch_complete (s : I.Stmt × BusOut I) (o : ∀ i, TheOracle I i) (w : Unit)
    (hin : ((s, o), w) ∈ Seam.bus I) (ρ : E) :
    ((start I s ρ (powerBatch (claimed I s) ρ), o), w) ∈
      Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I) := by
  cases w
  simp only [Seam.bus, Seam.of, Set.mem_ofPred_eq] at hin
  refine ⟨?_, hin.2.2⟩
  show powerBatch (claimed I s) ρ = Sumcheck.weightedSum _ _ (((s, ρ), o), ())
  rw [sum_tableSummand, (trueValues_eq_claimed_iff I s (theStack o)).mpr ⟨hin.1, hin.2.1⟩]

end TableSumcheck
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal
noncomputable section
namespace TableSumcheck
variable (I : M3Instance)

/-- **A round of the table sumcheck** (the content of the cut `roundsSecurity`): with the Keccak
predicate carried as the invariant `inv`, a recorded polynomial that passes the check has at most
`3` bad challenges, the round polynomial's agreements with the honest one or the zero test's
escape. -/
theorem card_round_badChallenge_le (hd : I.d ≤ 2) {j : ℕ} (hj : j < I.τmax)
    (p : SumcheckRound.MidStmt (Data I) E j 3) (o : ∀ i, TheOracle I i)
    (hc : SumcheckRound.check j
      (Sumcheck.familyInv (tableSummand I) Sumcheck.unitWeights nodes (inv I)).weight p.1 p.2 =
        true) :
    Nat.card {x // SumcheckRound.badChallenge j
      (Sumcheck.familyInv (tableSummand I) Sumcheck.unitWeights nodes (inv I)) p o x} ≤ 3 :=
  SumcheckRound.card_badChallenge_le j _
    (Sumcheck.familyInv_consistent (tableSummand I) Sumcheck.unitWeights nodes
      (tableSummand_degree I hd) nodes_injective (inv I))
    (fun ctx j c hj hne ↦ inv_sound I ctx j c hj hne) hj p o hc

end TableSumcheck
end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.TableSumcheck
open CompPoly CMlPolynomialEval
open scoped NNReal ENNReal
section
variable (tables : List Table)
variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (layout : Verifier.Layout)
variable {εmax : ℝ≥0∞}

open Classical in
/-- **The table sumcheck** (`tablePhase`, `lib.rs:242-266`, `bus.rs:218-259`) after the bus phase
read `w`: from the bus seam at `w` to the table seam on the wire. `ξ` is charged
`L₀ · (B + 2) / |E|`, each round `L₀ · 3 / |E|`. -/
noncomputable def tablePhaseSpec (colOf : I.ColumnId → ℕ) (w : BusWit)
    (fid : TableFid tables I hI input layout colOf w) (htw : ∀ t ∈ tables, 0 < t.width)
    (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) :
    Spec (tablePhaseClaims tables layout (w.result tables layout)) (BusAt I hI cands input w)
      (TablePost I cands input colOf) εmax
      (xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T)
      T :=
  let s := busStmt I hI input w
  (Spec.sampleE (xiError I L₀) (Post := fun ξ h ↦ HDoom cands
      (SumcheckRound.rel (tableFamily I) 0)
      ((s, ξ), (#v[], dot (fpsOf tables ξ) (w.result tables layout).totals)) h)
    (fun h₀ hp ↦ by
      obtain ⟨-, -, -, W, hW, hR⟩ := hp
      refine le_trans ?_ (xi_escape I (hfin W) (hcard W) s hR)
      gcongr with ξ _
      intro hD
      refine ⟨W, firstWord_append hW _, ?_⟩
      rw [fid.target ξ, tableFamily_rel_zero]
      exact hD)).bind' fun ξ ↦
  (tableSumcheckSpec tables I hI cands input layout colOf w fid htw hd hfin hcard he hT ξ).bind'
    fun tableClaims ↦
  (Spec.ret (Post := TablePost I cands input colOf) ((w.result tables layout).claims ++ tableClaims)).mono
    (fun _ hp ↦ by
      obtain ⟨ch, claim, evs, hs, hl, rfl, W, hW, hR⟩ := hp
      exact ⟨W, _, hW, hR, rfl, fid.claims ξ ch claim evs hl hs, _, _, rfl⟩) (fun _ _ h ↦ h)
      le_rfl le_rfl
    le_rfl

end
end LeanVM.Protocol.EndToEnd.Front
end
end

section
section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier
open scoped NNReal ENNReal
section
variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (tables : List Table) (layout : Verifier.Layout) {εmax : ℝ≥0∞}

/-- **The bus phase, then the table sumcheck**: from the commitment's doom to the table seam on
the wire. -/
noncomputable def busTableSpec (colOf : I.ColumnId → ℕ)
    (fid : ∀ w : BusWit, w.Shaped I → TableFid tables I hI input layout colOf w)
    (htw : ∀ t ∈ tables, 0 < t.width) (hd : I.d ≤ 2)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none)
      T ≤ εmax) :
    Spec ((verifyBusBalance tables computedBytecodeValue layout).bind (tablePhaseClaims tables layout))
      (HDoom cands (Seam.commit I) input)
      (TablePost I cands input colOf) εmax (abError I L₀ + 0) T :=
  busThenSpec I hI cands input tables layout hxi
    (fun w ↦ if hw : w.Shaped I then
      tablePhaseSpec tables I hI cands input layout colOf w (fid w hw) htw hd hfin hcard he3 hTf
    else specOfFalse fun _ hp ↦ hw ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    hfin hcard hμ hdepth hab he4 hT hlam

end
end LeanVM.Protocol.EndToEnd.Front
end
end

section
section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front CompPoly CMlPolynomialEval
open scoped NNReal ENNReal
section Bus
variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt)
variable {εmax : ℝ≥0∞}

/-- **The lvm bus phase, specified** (leanVM's `busThenSpec` without the framework blocks): from
the commitment's doom to doom on the bus seam at the protocol's output on what was read; `Lk` is the
follower's lead. -/
noncomputable def lvmBusSpec (vals : Vector E I.busClaims) {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {Lk : ℝ≥0∞} (hLk : Lk ≤ εmax) :
    Spec (lvmBusProg I.μBus) (HDoom cands (Seam.commit I) input) (LBusAt I hI cands input vals) εmax
      (abError I L₀ + 0) Lk :=
  (abSpec I cands input hI hfin hcard hab (T := 0)).bind' fun ab ↦
    (gkrSpec I cands (input, (toAlpha ab.1, ab.2)) hI hfin hcard hμ he hT hlam).bind' fun r ↦
      let P : List Ev → Prop := fun h ↦ r.2.1.length = I.μBus ∧ r.2.2.length = 3 ∧
          HDoom cands (Seam.bus I) (lbusStmt I hI input ⟨ab.1, ab.2, r.2.1, r.2.2⟩ vals) h
      (Spec.require (T := 0) (Post := fun _ h ↦ P h)
        fun _ hp hc ↦ by
          obtain ⟨hl, hv, W, hW, hR⟩ := hp.resolve_left hc
          exact ⟨hl, hv, W, hW, values_keep I hI hR vals⟩).bind' fun _ ↦
      (Spec.readE (Post := fun _ h ↦ P h)
        (fun _ _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.append _⟩) hLk).bind' fun _ ↦
      (Spec.require (Post := fun _ h ↦ P h) fun _ hp _ ↦ hp).bind' fun _ ↦
      (Spec.ret (Post := LBusAt I hI cands input vals) _).mono (fun _ hp ↦ hp)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Bus
end Lvm.M3
end
end

section
section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front CompPoly CMlPolynomialEval
open scoped NNReal ENNReal
section Compose
variable (tables : List Verifier.Table) (I : M3Instance) (hI : Bus.Conditions I)
  (cands : Word → Set (∀ i, TheOracle I i)) (input : I.Stmt) (layout : Verifier.Layout)
  {εmax : ℝ≥0∞}

/-- **`M3Holds` from the phase specs** (leanVM's `busTableSpec` for the lvm instance): from the
commitment's doom (no candidate satisfies `M3Holds`) to the table seam on the wire, given, for every
read of the right shape, the identities between the program's computations and the protocol's
(`TableFidG`, as leanVM's `busTableSpec` takes `TableFid`). Errors: `abError L₀ + 0` lead (the
fingerprint challenges), `roundError L₀ 4`, `lambdaError L₀` in the grand product, `xiError L₀`
and `roundError L₀ 3` per round in the table sumcheck. -/
noncomputable def lvmBusTableSpec (colOf : I.ColumnId → ℕ) (vals : Vector E I.busClaims)
    (busRes : LBus → BusResult)
    (fid : ∀ b : LBus, b.point.length = I.μBus → b.values.length = 3 →
      TableFidG tables I layout colOf (lbusStmt I hI input b vals) (busRes b))
    (htw : ∀ t ∈ tables, 0 < t.width) (hd : I.d ≤ 2)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : I.μBus ≠ 0) (hab : abError I L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none)
      T ≤ εmax) :
    Spec (lvmBusTableProg tables layout I.μBus busRes) (HDoom cands (Seam.commit I) input)
      (TablePost I cands input colOf) εmax (abError I L₀ + 0) T :=
  (lvmBusSpec I hI cands input vals hfin hcard hμ hab he4 hT hlam hxi).bind
    (fun b ↦ if hb : b.point.length = I.μBus ∧ b.values.length = 3 then
      (tablePhaseSpecG tables I cands layout colOf (lbusStmt I hI input b vals) (busRes b)
        (fid b hb.1 hb.2) htw hd hfin hcard he3 hTf).mono
        (fun _ hp ↦ hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else specOfFalse fun _ hp ↦ hb ⟨hp.1, hp.2.1⟩)

end Compose
end Lvm.M3
end
end

section
section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front CompPoly CMlPolynomialEval
open scoped NNReal ENNReal
section Errors

theorem natDivCard_le {a b : ℕ} (h : a ≤ b) :
    ((((a : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞)) ≤ (((b : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  gcongr

/-- **Bus fingerprint**: `abError ≤ 2^24/|E|` (§3.2's row "bus fingerprint …") when `μ_bus ≤ 22`
(P20: 21; P8: 20). -/
theorem abError_le (I : M3Instance) (hμ : I.μBus ≤ 22) :
    abError I 1 ≤ ((overE (2 ^ 24) : ℝ≥0) : ℝ≥0∞) := by
  unfold abError
  rw [Nat.cast_one, one_mul]
  have : 4 * 2 ^ I.μBus ≤ 2 ^ 24 := by
    calc 4 * 2 ^ I.μBus ≤ 4 * 2 ^ 22 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hμ)
      _ = 2 ^ 24 := by norm_num
  unfold overE
  rw [← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le this

/-- **Table sumcheck batching**: `xiError ≤ 2^24/|E|` when the tables have at most `2^24 − 2`
constraints. -/
theorem xiError_le (I : M3Instance) (hB : I.B + 2 ≤ 2 ^ 24) :
    xiError I 1 ≤ ((overE (2 ^ 24) : ℝ≥0) : ℝ≥0∞) := by
  unfold xiError overE
  rw [Nat.cast_one, one_mul, ← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le (by omega)

/-- **Sumcheck rounds** (grand product degree 3 with `4` coefficients, table sumcheck degree 3) and the
grand product's combiners: at most `4/|E|`. -/
theorem roundError_le (d : ℕ) (hd : d ≤ 4) :
    roundError 1 d ≤ ((overE 4 : ℝ≥0) : ℝ≥0∞) := by
  unfold roundError overE
  rw [Nat.cast_one, one_mul, ← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le hd

theorem lambdaError_le : lambdaError 1 ≤ ((overE 4 : ℝ≥0) : ℝ≥0∞) := by
  unfold lambdaError overE
  rw [Nat.cast_one, one_mul, ← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le (by norm_num)

end Errors
end Lvm.M3
end
end

-- ===== from `LvmM3Mid` =====

section
section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval
section
variable {α : Type} (L : List α) (κ : α → ℕ)

/-- The verifier's order of the indices: `stack_offsets`' stable sort by size. -/
def ordL : List ℕ :=
  (List.range L.length).mergeSort fun i j ↦ decide ((L.map κ).getD j 0 ≤ (L.map κ).getD i 0)

theorem ordL_perm : (ordL L κ).Perm (List.range L.length) := List.mergeSort_perm _ _

theorem length_ordL : (ordL L κ).length = L.length := by
  rw [(ordL_perm L κ).length_eq, List.length_range]

theorem length_sortedL : (sortedL L κ).length = L.length := List.length_mergeSort _

theorem ordL_lt {i : ℕ} (hi : i ∈ ordL L κ) : i < L.length :=
  List.mem_range.mp ((ordL_perm L κ).mem_iff.mp hi)

/-- **The sorted blocks are `L` in the verifier's order.** -/
theorem sortedL_eq_map_ordL (x₀ : α) : sortedL L κ = (ordL L κ).map fun i ↦ L.getD i x₀ := by
  rw [ordL, List.map_mergeSort (s := fun a b ↦ decide (κ b ≤ κ a))]
  · congr 1
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getElem?_eq_getElem h1]
  · intro a ha b hb
    rw [List.mem_range] at ha hb
    simp [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]

/-- The `b`-th sorted block. -/
theorem getElem_sortedL (x₀ : α) (b : ℕ) (hb : b < (sortedL L κ).length) :
    (sortedL L κ)[b] = L.getD ((ordL L κ)[b]'(by rw [length_ordL]; rwa [length_sortedL] at hb))
      x₀ := by
  simp only [sortedL_eq_map_ordL L κ x₀, List.getElem_map]

/-- **The verifier's offsets are prefix sums in the sorted order.** -/
theorem stackOffsets_getD_ordL (x₀ : α) (b : ℕ) (hb : b < L.length) :
    (stackOffsets (L.map κ)).1.getD ((ordL L κ)[b]'(by rwa [length_ordL])) 0 =
      (((sortedL L κ).take b).map fun a ↦ 2 ^ κ a).sum := by
  have hnd : (ordL L κ).Nodup := (ordL_perm L κ).nodup_iff.mpr List.nodup_range
  rw [stackOffsets_eq]
  simp only [List.length_map]
  change ((ordL L κ).foldl (placeStep fun i ↦ 2 ^ (L.map κ).getD i 0)
    (List.replicate L.length 0, 0)).1.getD _ 0 = _
  have hfold := placeFold_getElem? (fun i ↦ 2 ^ (L.map κ).getD i 0) (ordL L κ) hnd
    (List.replicate L.length 0, 0) (fun i hi ↦ by simpa using ordL_lt L κ hi) b
    (by rwa [length_ordL])
  rw [List.getD_eq_getElem?_getD, hfold, Option.getD_some, zero_add,
    sortedL_eq_map_ordL L κ x₀, ← List.map_take, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
  have hi' := ordL_lt L κ (List.mem_of_mem_take hi)
  simp [List.getElem?_eq_getElem hi']

end
end LeanVM.Protocol.EndToEnd.Front
end
end

section
section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval
section
variable {α : Type} (L : List α) (κ : α → ℕ)

/-- The verifier's placements of the blocks of sizes `sizes` (`bus_layout`). -/
def refPlacements (sizes : List ℕ) : List Placement :=
  List.zipWith (fun size offset ↦ ({ variableCount := size, index := offset } : Placement)) sizes
    (stackOffsets sizes).1

theorem length_stackOffsets_fst (sizes : List ℕ) :
    (stackOffsets sizes).1.length = sizes.length := by
  rw [stackOffsets_eq]
  simp only
  rw [placeFold_length, List.length_replicate]

theorem length_pyPlacements (sizes : List ℕ) : (refPlacements sizes).length = sizes.length := by
  simp [refPlacements, length_stackOffsets_fst]

/-- The placement of the block at sorted position `b`. -/
theorem refPlacements_getElem_ordL (x₀ : α) (b : ℕ) (hb : b < L.length) :
    (refPlacements (L.map κ))[(ordL L κ)[b]'(by rwa [length_ordL])]'(by
        rw [length_pyPlacements, List.length_map]
        exact ordL_lt L κ (List.getElem_mem _)) =
      { variableCount := κ ((sortedL L κ)[b]'(by rwa [length_sortedL])),
        index := (((sortedL L κ).take b).map fun a ↦ 2 ^ κ a).sum } := by
  have hi := ordL_lt L κ (List.getElem_mem (l := ordL L κ) (n := b) (by rwa [length_ordL]))
  simp only [refPlacements, List.getElem_zipWith, List.getElem_map]
  rw [← stackOffsets_getD_ordL L κ x₀ b hb, List.getD_eq_getElem _ _ (by
    rw [length_stackOffsets_fst, List.length_map]; exact hi), getElem_sortedL L κ x₀,
    List.getD_eq_getElem _ _ hi]

end
end LeanVM.Protocol.EndToEnd.Front
end
end

section
section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval
section
variable {α : Type} (L : List α) (κ : α → ℕ)

/-- The verifier's order as a bijection of the sorted positions onto the indices. -/
theorem ordL_bijective (hn : (ordL L κ).length = L.length) :
    Function.Bijective fun b : Fin L.length ↦
      (⟨(ordL L κ)[b.val]'(by rw [hn]; exact b.isLt),
        ordL_lt L κ (List.getElem_mem _)⟩ : Fin L.length) := by
  have hnd : (ordL L κ).Nodup := (ordL_perm L κ).nodup_iff.mpr List.nodup_range
  constructor
  · intro a b hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext ((hnd.getElem_inj_iff).mp hab)
  · intro i
    have hi : i.val ∈ ordL L κ := (ordL_perm L κ).mem_iff.mpr (List.mem_range.mpr i.isLt)
    obtain ⟨b, hb, hbi⟩ := List.mem_iff_getElem.mp hi
    exact ⟨⟨b, by rwa [← hn]⟩, Fin.ext hbi⟩

/-- **A sum over the protocol's blocks is a sum over the verifier's placements**: the selector
weight of block `b` times a quantity of the `b`-th sorted block, summed over the blocks, is
`eq_above` of placement `i` times the quantity of block `i` of `L`, summed over the indices. -/
theorem sum_selectorWeight_eq (x₀ : α) (B : Blocks) (hn : B.n = (sortedL L κ).length)
    (hs : ∀ b : Fin B.n, B.size b = κ ((sortedL L κ)[b.val]'(hn ▸ b.isLt))) {μ : ℕ}
    (hμ : B.total ≤ 2 ^ μ) (z : Vector E μ) (F : α → E) :
    ∑ b : Fin B.n, B.selectorWeight hμ b z * F ((sortedL L κ)[b.val]'(hn ▸ b.isLt)) =
      ∑ i : Fin L.length, ((refPlacements (L.map κ))[i.val]'(by
        rw [length_pyPlacements, List.length_map]; exact i.isLt)).eqAbove z.toList * F L[i] := by
  have hn' : B.n = L.length := by rw [hn, length_sortedL]
  rw [← (Equiv.ofBijective _ (ordL_bijective L κ (length_ordL L κ))).sum_comp]
  rw [← (finCongr hn').sum_comp]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [Equiv.ofBijective_apply, finCongr_apply, Fin.val_cast]
  have hb : b.val < L.length := by rw [← hn']; exact b.isLt
  congr 1
  · rw [refPlacements_getElem_ordL L κ x₀ b hb, ← eqAbove_eq_selectorWeight B hμ b z, hs b,
      Blocks.offset, offsetNat_sortedL L κ B hn hs b b.isLt.le]
  · rw [getElem_sortedL L κ x₀, List.getD_eq_getElem _ _ (ordL_lt L κ (List.getElem_mem _))]
    rfl

end
end LeanVM.Protocol.EndToEnd.Front
end
end

section
section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Compile LeanVM.Protocol.TableSumcheck CompPoly CMlPolynomialEval
open Finset
open scoped NNReal ENNReal

/-- The low coordinates of a list read as a vector. -/
theorem ofFn_vecOf (p : List E) {μ m : ℕ} (hm : m ≤ μ) (hp : p.length = μ) :
    (List.ofFn fun j : Fin m ↦ (vecOf μ p)[j.val]'(by omega)) = p.take m := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_ofFn, vecOf, Vector.getElem_ofFn, List.getElem_take]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

end Lvm.M3
end
end

section
section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Compile LeanVM.Protocol.TableSumcheck CompPoly CMlPolynomialEval
open Finset
open scoped NNReal ENNReal

/-- A one-row table seeding one cell (an input array's shape). -/
def seedTab : Tab where
  τ := 0
  cols := [.com false 0, .com false 1]
  cons := []
  reads := []
  seeds := [(⟨0, CPoly.var 1, [CPoly.var 0]⟩, 0)]
  deg := by
    refine ⟨fun C hC ↦ by simp at hC, fun r hr ↦ by simp at hr, fun s hs ↦ ?_⟩
    simp only [List.mem_singleton] at hs; subst hs
    refine ⟨fun m hm ↦ by simp [CPoly.var] at hm; subst hm; simp, fun P hP ↦ ?_⟩
    simp only [List.mem_singleton] at hP; subst hP
    intro m hm; simp [CPoly.var] at hm; subst hm; simp

/-- **Non-vacuity of `lbusTableSpec`'s side conditions**: a seeding table meets them. -/
theorem seedTab_conditions : AllSc [seedTab] ∧ KeysOk [seedTab] ∧ ∀ t ∈ [seedTab], 0 < t.w := by
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩ <;> simp only [List.mem_singleton] at ht <;>
    subst ht
  · exact Or.inr (by simp [seedTab])
  · exact ⟨fun r hr ↦ by simp [seedTab] at hr, fun s hs ↦ by simp [seedTab] at hs; subst hs; simp⟩
  · simp [seedTab, Tab.w]

end Lvm.M3
end
end
