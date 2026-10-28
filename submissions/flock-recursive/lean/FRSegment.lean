-- New for `flock-recursive` (BLUEPRINT revision 4.0, B-11, B-12; stage S-0′).
import FRShape4
import FRLeafCircuit
import RecursionFast.Library.Fast

/-!
# Segments: variable-length leaves with a secret or a public start (B-12)

A step's chain of `n ∈ [2^17, 2^20]` compressions is proved as `k = ⌈n/2^18⌉ ≤ 4` **segments**
(B-11). A segment of kind `κ ∈ {L30, L31, L32}` (revision 4.1's ladder) is the leaf circuit with a **variable length**
`1 ≤ n ≤ cap κ = 2^(m − 14)`: its blocks `i < n` are chain blocks with the public target, linked;
the blocks `≥ n` are `free` (no constraint); the last block is `n − 1`, read from the statement
(INT-4's `bnd`). **`pubStart`**: segment 1's start is the leaf witness (secret); a segment `i ≥ 2`
starts at the public `s_i = e_{i−1}`.

* `SegStmt`: start, end, length, `pubStart`. `SegHolds κ st z`: the circuit's content on the table
  `z` (the range of `n`, Booleanity, the block R1CS with its target and the links on the used
  blocks). **`seg_sound`**: it proves `chainEnd st.start st.n = st.h` (from `Leaf.leaf_sound` at
  `n`; the free blocks are never read). **`seg_complete`**: the honest table meets it.
* **`segs_compose`**: chained segments (`Chained`: the first secret, the others public with
  `s_{i+1} = e_i`) prove the whole chain: `chainEnd s₁ (Σ nᵢ) = e_k` (`chainEnd_add`).
* The proof format of a segment is 3.x's (`FRShape4.segHdr`, `stmtLeafBytes n h`): `segView`
  reads its kind, start (`hdr.pub`), end and length; its statement digest is the contract's
  `leafStmt e n` (`segC`). `pubStart` is the segment's **position** in the aggregate leaf, checked
  by `V_A` (`FRAgg`): it is not a byte of the proof (S-0′ issue I-2).
* Controls: `seg_bad_n` (`n = 0` and `n = cap + 1` are rejected by the circuit), `seg_wrong_end`
  (no table proves the one-step chain from `0` back to `0`: a wrong start or end is rejected),
  `segs_compose_ctrl` (a break in the chaining is not composed).
-/

namespace FR
namespace Rev4
open RecursionFast ProductCircuit Blake2sCircuit Block Chain Leaf

/-! ## Specification -/

/-- A segment's statement: its start, its end, its length, and whether the start is public. -/
structure SegStmt where
  start : Digest
  h : Digest
  n : ℕ
  pubStart : Bool

/-- The length is in the kind's range. -/
def SegStmt.InRange (κ : SegKind) (st : SegStmt) : Prop := 1 ≤ st.n ∧ st.n ≤ κ.cap

instance (κ : SegKind) (st : SegStmt) : Decidable (st.InRange κ) := by
  unfold SegStmt.InRange; infer_instance

/-- **The segment circuit's content** on a table `z` (block `i`, position `k`): the length in
range; on the used blocks `i < n` Booleanity and the chain block's R1CS with its public target; the
links from `start` (block 0's `h_in`, the gated pin when `pubStart`) to `h` (block `n − 1`'s
output). Blocks `i ≥ n` are free. -/
def SegHolds {R : Type*} [CommRing R] [DecidableEq R] (κ : SegKind) (st : SegStmt)
    (z : ℕ → Pos → R) : Prop :=
  st.InRange κ ∧ (∀ i < st.n, ∀ k, BlockR1CS.IsBool (z i k)) ∧
    (∀ i < st.n, HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (z i)) ∧
    ChainLinks st.n z st.start st.h

/-- **Segment soundness**: a table meeting the segment circuit proves the segment's chain. -/
theorem seg_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] [DecidableEq R]
    {κ : SegKind} {st : SegStmt} {z : ℕ → Pos → R} (h : SegHolds κ st z) :
    chainEnd st.start st.n = st.h :=
  leaf_sound h.1.1 z st.start st.h h.2.1 h.2.2.1 h.2.2.2

/-- **Segment completeness**: the honest table of a length in range meets the circuit. -/
theorem seg_complete {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] [DecidableEq R]
    (κ : SegKind) (s : Digest) {n : ℕ} (hn : 1 ≤ n ∧ n ≤ κ.cap) (b : Bool) :
    SegHolds κ ⟨s, chainEnd s n, n, b⟩ (fun i ↦ liftBlock R (leafWitness s i)) :=
  ⟨hn, leaf_complete s hn.1⟩

/-- **3.x's leaf is the `L32` segment at `n = 2^18`**: `SegHolds .L32` with a secret start is
`leaf_sound`'s hypothesis set at `leafN .L32`. -/
theorem segHolds_L32 {R : Type*} [CommRing R] [DecidableEq R] (s h : Digest) (z : ℕ → Pos → R) :
    SegHolds .L32 ⟨s, h, leafN .L32, false⟩ z ↔
      (∀ i < leafN .L32, ∀ k, BlockR1CS.IsBool (z i k)) ∧
        (∀ i < leafN .L32, HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (z i)) ∧
        ChainLinks (leafN .L32) z s h := by
  simp [SegHolds, SegStmt.InRange, SegKind.cap, SegKind.m, leafN, Kind.m]

/-! ## Composition of chained segments -/

/-- The tail of a chain after `a`: every segment public, starting at its predecessor's end. -/
def ChainedTail : SegStmt → List SegStmt → Prop
  | _, [] => True
  | a, b :: l => b.start = a.h ∧ b.pubStart = true ∧ ChainedTail b l

/-- **Chained segments**: the first has a secret start, every later one a public start equal to
its predecessor's end. -/
def Chained : List SegStmt → Prop
  | [] => False
  | a :: l => a.pubStart = false ∧ ChainedTail a l

/-- `chainEnd` composes (`chainEnd s n = chainEnd (chainEnd s n₁) n₂` for `n = n₁ + n₂`). -/
theorem chainEnd_add (s : Digest) (a b : ℕ) : chainEnd s (a + b) = chainEnd (chainEnd s a) b := by
  rw [chainEnd, chainEnd, chainEnd, Nat.add_comm, Function.iterate_add_apply]

/-- The total length. -/
def totalN (l : List SegStmt) : ℕ := (l.map SegStmt.n).sum

private theorem compose_tail (a : SegStmt) : ∀ (l : List SegStmt), ChainedTail a l →
    (∀ st ∈ l, chainEnd st.start st.n = st.h) →
    chainEnd a.h (totalN l) = ((a :: l).getLast (List.cons_ne_nil _ _)).h
  | [], _, _ => by simp [totalN, chainEnd]
  | b :: l, ⟨hb, _, ht⟩, hs => by
    simp only [totalN, List.map_cons, List.sum_cons] at *
    rw [chainEnd_add, ← hb, hs b (by simp), List.getLast_cons (List.cons_ne_nil _ _)]
    exact compose_tail b l ht fun st h => hs st (List.mem_cons_of_mem _ h)

/-- **Chained segments prove the whole chain**: if every segment proves its piece, the first
segment's start reaches the last segment's end in `Σ nᵢ` steps. -/
theorem segs_compose (a : SegStmt) (l : List SegStmt) (hc : ChainedTail a l)
    (hs : ∀ st ∈ a :: l, chainEnd st.start st.n = st.h) :
    chainEnd a.start (totalN (a :: l)) = ((a :: l).getLast (List.cons_ne_nil _ _)).h := by
  simp only [totalN, List.map_cons, List.sum_cons]
  rw [chainEnd_add, hs a (by simp)]
  exact compose_tail a l hc fun st h => hs st (List.mem_cons_of_mem _ h)

/-! ## The proof format's view (3.x's leaf format) -/

/-- The little-endian number of the 8 bytes at `o`. -/
def rdLE64 (π : Proof) (o : ℕ) : ℕ := ((List.range 8).map fun i => (byteAt π (o + i)).toNat * 256 ^ i).sum

/-- What `V_A` reads of a segment proof: its kind, start (`hdr.pub`), end (`stmt` bytes 1–32) and
length (`stmt` bytes 33–40). -/
structure SegView where
  kind : SegKind
  start : Digest
  h : Digest
  n : ℕ
  deriving DecidableEq

/-- **The view of a segment proof** (`none` unless byte 0 is a segment kind byte). -/
def segView (π : Proof) : Option SegView :=
  (SegKind.ofByte? (byteAt π 0)).map fun κ => ⟨κ, bytesAt π 16 32, bytesAt π 49 32, rdLE64 π 81⟩

/-- The statement of a view at a position (`pubStart` iff not the first). -/
def SegView.stmt (v : SegView) (pub : Bool) : SegStmt := ⟨v.start, v.h, v.n, pub⟩

/-- **A segment's statement digest** `cᵢ = leafStmt eᵢ nᵢ` (the 3.x leaf statement, what the
segment program's `hashStmt` checks). -/
def segC (v : SegView) : Digest := leafStmtF v.h v.n

/-! ## Controls -/

/-- Negative: lengths `0` and `cap + 1` are rejected by the circuit. -/
theorem seg_bad_n {R : Type*} [CommRing R] [DecidableEq R] (κ : SegKind) (s h : Digest) (b : Bool)
    (z : ℕ → Pos → R) : ¬ SegHolds κ ⟨s, h, 0, b⟩ z ∧ ¬ SegHolds κ ⟨s, h, κ.cap + 1, b⟩ z :=
  ⟨fun hs => absurd hs.1.1 (by simp), fun hs => absurd hs.1.2 (by simp)⟩

/-- Negative (wrong start or end): no table over `GF(2)` proves the one-step chain from `0` to `0`,
for either kind and either start mode (`chainEnd 0 1 ≠ 0`, the BLAKE2s KAT). -/
theorem seg_wrong_end (κ : SegKind) (b : Bool) (z : ℕ → Pos → ZMod 2) :
    ¬ SegHolds κ ⟨Vector.replicate 32 0, Vector.replicate 32 0, 1, b⟩ z := fun hs =>
  (zero_table_control (R := ZMod 2)).2.2.2.1 (seg_sound hs)

/-- Positive: the honest one-step segment from `0` meets the circuit (either kind, either mode). -/
theorem seg_ctrl_pos (κ : SegKind) (b : Bool) :
    SegHolds κ ⟨Vector.replicate 32 0, chainEnd (Vector.replicate 32 0) 1, 1, b⟩
      (fun i ↦ liftBlock (ZMod 2) (leafWitness (Vector.replicate 32 0) i)) :=
  seg_complete κ _ ⟨le_rfl, by cases κ <;> decide⟩ b

/-- Negative (composition): a chain whose second segment starts elsewhere is not `Chained'`. -/
theorem segs_compose_ctrl (a b : SegStmt) (h : b.start ≠ a.h) : ¬ ChainedTail a [b] :=
  fun hc => h hc.1

end Rev4
end FR
