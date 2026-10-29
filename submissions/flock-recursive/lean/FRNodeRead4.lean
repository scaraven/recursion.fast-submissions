-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.3, A.5, A.7; R-4-m2; stage S-N2: S-E12a's D6,
-- the concrete `N4c.Read4`). The 3.x analogue is `FRNodeRead` (`readTrace`, `readSig`, `readSigned`).
import FRNodeSound4
import FRNodeReadCore

/-!
# The revision 4.1 node's reader: its children read off `f⁽⁰⁾`

`rd4 pf : N4c.Read4` reads a node's signed children and its verifier slots' inputs from the
committed witness `w`:

* **Each aggregate's segment count** `kAct κ a w` is the circuit's: the number of its sub-slots
  whose activity `S_σ = Σ_ι s′_ι` is `1`, counted up to the first inactive one (`Nat.find`). With
  the activity rows (S-E12c) this is S-E12c's `ActK` (`actK_kAct`): exactly the sub-slots `i < k`
  are active.
* **The traces** are read off H, as 3.x's `readTrace`: signed child `σ`'s chain hashes the stream
  `chainBytes4 κ σ k w` (S-E12a), and segment `i`'s trace is the item sequence `itemsOf seq4` read
  from stream offset `1 + i·(segB − 1)` (`segTr`). A previous node's is segment 0 of its stream.
  An aggregate's trace is its active sub-slots' traces in order.
* **The proofs.** A slot's proof is `pf` of its trace (`pf`: the child proof its trace carries,
  A.5; for `seq4` this is S-H4's reassembly, a parameter here), fitted to `piSizeOf seq4` bytes.
  An aggregate's `π_A` is `hdrA = 'A' ‖ k ‖ 0⁶ ‖ enc64 n ‖ e` followed by its active sub-slots'
  proofs, with `(e, n)` read off its statement block `hashA` (`tagLeaf ‖ e ‖ enc64 n`, D2).
* **The signatures** are read off L as 3.x's `readSig`, at signed child `σ`'s `2^14` stride.

The reader fixes the format of what it reads (`π_A`'s header, the slot proofs' size), so
`NodeResid4`'s `aggFmt`, `aggTr`, `kOk` and `slotP` hold of it by construction
(`FRNodeSound4R`). What it does *not* fix (the children's kind bytes, that the stream is a trace's
encoding, the aggregate checks, the signature) is what the circuit must bind.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## The segment counts -/

/-- **Aggregate `a`'s segment count**: its first inactive sub-slot (or `maxK`). -/
noncomputable def kAct (κ : NodeKind) (a : ℕ) (w : Asg) : ℕ :=
  open Classical in
  Nat.find (⟨κ.maxK, Or.inl rfl⟩ : ∃ i, i = κ.maxK ∨ (selSum κ (N4c.sub κ a i)).ev w ≠ 1)

theorem kAct_le (κ : NodeKind) (a : ℕ) (w : Asg) : kAct κ a w ≤ κ.maxK := by
  classical
  exact Nat.find_min' _ (Or.inl rfl)

/-! ## The traces, proofs and signatures -/

/-- Segment `i`'s trace in signed child `σ`'s stream (`k` segments): `seq4`'s items from offset
`1 + i·(segB − 1)`. -/
noncomputable def segTr (κ : NodeKind) (σ k i : ℕ) (w : Asg) : Trace :=
  Read.readItems (N4c.chainBytes4 κ σ k w) (1 + i * (N4c.segB - 1)) (itemsOf seq4)

/-- The aggregate a segment slot belongs to. -/
def slotA (κ : NodeKind) (v : ℕ) : ℕ := if κ.hasPrev then 0 else v / 4

/-- **Slot `v`'s trace**: the previous node's stream, or its sub-slot's segment of its aggregate's. -/
noncomputable def slotTr4 (κ : NodeKind) (v : ℕ) (w : Asg) : Trace :=
  if isPrevSlot κ v then segTr κ 0 0 0 w
  else segTr κ (N4c.aggChild κ (slotA κ v)) (kAct κ (slotA κ v) w) (subIx κ v) w

/-- `b` padded with zeros or cut to `n` bytes. -/
def fitL (n : ℕ) (b : List UInt8) : List UInt8 := (b ++ List.replicate n 0).take n

theorem fitL_length (n : ℕ) (b : List UInt8) : (fitL n b).length = n := by
  simp [fitL]

/-- **Slot `v`'s proof bytes**: the proof its trace carries (`pf`), at `piSizeOf seq4` bytes. -/
noncomputable def slotPf (pf : Trace → Proof) (κ : NodeKind) (v : ℕ) (w : Asg) : List UInt8 :=
  fitL (piSizeOf seq4) (pf (slotTr4 κ v w)).data.toList

/-- Aggregate `a`'s statement block's message (`tagLeaf ‖ e ‖ enc64 n`, 41 bytes). -/
noncomputable def hA (κ : NodeKind) (a : ℕ) (w : Asg) : List UInt8 :=
  Stream.streamBytes (fun _ => N4c.bitsB4 w (N4c.cAB κ a)) 41

/-- The chain end `e` and the length `n` that aggregate `a`'s statement block hashes. -/
noncomputable def hAe (κ : NodeKind) (a : ℕ) (w : Asg) : Digest := Vector.ofFn fun i : Fin 32 => (hA κ a w).getD (1 + i) 0
noncomputable def hAn (κ : NodeKind) (a : ℕ) (w : Asg) : ℕ :=
  ((List.range 8).map fun i => ((hA κ a w).getD (33 + i) 0).toNat * 256 ^ i).sum

/-- **`π_A`**: `hdrA` with the circuit's `k`, then the active sub-slots' proofs. -/
noncomputable def aggPf (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) : Proof :=
  ⟨(aggHdr (kAct κ a w) (hAn κ a w) (hAe κ a w) ++
    ((List.range (kAct κ a w)).map fun i => slotPf pf κ (N4c.sub κ a i) w).flatten).toArray⟩

/-- Signed child `σ`'s L element `j` (its `2^14` stride, A.7). -/
def sigCell (κ : NodeKind) (σ j : ℕ) : ℕ := κ.lBase * 128 + σ * 2 ^ 14 + j

/-- **Signed child `σ`'s signature** (3.x's `readSig` at its stride: `idx`, the chain values, the
path). -/
def readSig4 (κ : NodeKind) (σ : ℕ) (w : Asg) : Sig where
  idx := (w (sigCell κ σ 0)).c₀.val.toNat
  ots := (List.range wotsLen).map fun j => Read.digestOf w (sigCell κ σ (1 + 2 * j)) (sigCell κ σ (2 + 2 * j))
  path := (List.range sigHeight).map fun t =>
    Read.digestOf w (sigCell κ σ (1 + 2 * wotsLen + 2 * t)) (sigCell κ σ (2 + 2 * wotsLen + 2 * t))

/-- **Signed child `σ`**: an aggregate's `π_A`, its sub-slots' traces in order; a previous node's
slot-0 proof and trace; the signature. -/
noncomputable def sgn4 (pf : Trace → Proof) (κ : NodeKind) (σ : ℕ) (w : Asg) : Signed :=
  if N4c.isAgg κ σ then
    ⟨aggPf pf κ (N4c.aggOf κ σ) w,
      ((List.range (kAct κ (N4c.aggOf κ σ) w)).map fun i => slotTr4 κ (N4c.sub κ (N4c.aggOf κ σ) i) w).flatten,
      readSig4 κ σ w⟩
  else ⟨⟨(slotPf pf κ 0 w).toArray⟩, slotTr4 κ 0 w, readSig4 κ σ w⟩

/-- **The reader** (S-E12a's D6) with the proof decoder `pf`. -/
noncomputable def rd4 (pf : Trace → Proof) : N4c.Read4 where
  sgn := sgn4 pf
  slotπ κ v w := ⟨(slotPf pf κ v w).toArray⟩
  slotTr := slotTr4

/-! ## Facts -/

theorem byteAt_mk (l : List UInt8) (i : ℕ) : byteAt ⟨l.toArray⟩ i = l.getD i 0 := by
  unfold byteAt
  split_ifs with h
  · simp only [ByteArray.size, List.size_toArray] at h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    rfl
  · simp only [ByteArray.size, List.size_toArray, not_lt] at h
    simp [List.getElem?_eq_none h]

theorem aggHdr_length (k n : ℕ) (e : Digest) : (aggHdr k n e).length = 48 := by
  simp [aggHdr, enc64_length]

theorem sgn4_agg (pf : Trace → Proof) (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) (w : Asg) :
    sgn4 pf κ (N4c.aggChild κ a) w =
      ⟨aggPf pf κ a w, ((List.range (kAct κ a w)).map fun i => slotTr4 κ (N4c.sub κ a i) w).flatten,
        readSig4 κ (N4c.aggChild κ a) w⟩ := by
  rw [sgn4, if_pos (N4c.isAgg_aggChild κ a), N4c.aggOf_aggChild κ ha]

/-- **The header's `k` is the circuit's.** -/
theorem kA_rd4 (pf : Trace → Proof) (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) (w : Asg) :
    N4c.kA (rd4 pf) κ w a = kAct κ a w := by
  have hk : kAct κ a w < 256 := lt_of_le_of_lt (kAct_le κ a w) (by cases κ <;> decide)
  simp only [N4c.kA, rd4, sgn4_agg pf κ ha, aggPf, byteAt_mk, aggHdr, List.cons_append,
    List.getD_cons_succ, List.getD_cons_zero]
  simp [Nat.toUInt8, UInt8.toNat_ofNat, Nat.mod_eq_of_lt hk]

end N4s
end FR
