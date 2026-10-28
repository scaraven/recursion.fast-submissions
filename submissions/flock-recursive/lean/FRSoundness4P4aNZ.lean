-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.6/A.7 per node kind, A.10 Z1/L3β; stage P4a
-- pass 5 (P4e)): the node half's Z and kind factor at S-E12a's maps (`FRNodeKinds4`,
-- `FRNodeCircuit4`). 3.x templates: `FRSoundnessFrZM` (`zlmFR_bits`, `zHolds_iff_truthZN`),
-- `FRSoundnessFrLN` (`kfT_node`).
import FRSoundness4P4aRS
import FRNodeCircuit4

/-!
# The node's matrices at revision 4.1: bits, the kind factor, Z's statement

`M := zlm4 indN4 etN4` (S-E12a's indicators `indN4` and targets `etN4`, from `nodeLayout4`):

* **`zlm4_bits4`** (`ZLM4.Bits`), with S-E12a's `zlm4_indKinds` (`IndKinds`) and P4d's
  `zlm4_etLocal` (`EtLocal`): `Front4a.OK`'s matrix fields.
* **`kfInd4`**: S-E12a's kind factor `kf4` is the node's indicators batched by `β` (`KfInd`), so
  `PendLcN` is RS claim 2's doom (`pendLcN4_pendBad4`).
* **`zHolds_iff_truthZ4`**: on a node, `ZHolds` is S-E12a's `truthZ4` on `f⁽⁰⁾` (every non-free
  block meets its kind's R1CS with its target; the free blocks' rows `z² = z` hold on bits).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## Bits and the kind factor -/

/-- **`zlm4`'s matrices, indicators and targets are bits** when the node maps are. -/
theorem zlm4_bits {indN : Rev4.NodeKind → Fin 9 → ℕ → F} {etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F}
    (hI : ∀ ν j t, IsBitF (indN ν j t)) (hE : ∀ ν t p, IsBitF (etN ν t p)) :
    (zlm4 indN etN).Bits := by
  refine ⟨kMat_bit _, kMat_bit _, fun κ j t => ?_, fun κ es t p => ?_⟩
  · cases κ with
    | seg σ => simp only [zlm4]; split_ifs <;> simp [IsBitF]
    | node ν => exact hI ν j t
  · cases κ with
    | seg σ =>
      simp only [zlm4, EtSeg, chainE]
      split_ifs <;> simp [IsBitF]
    | node ν => exact hE ν t p

/-- **S-E12a's maps give bits.** -/
theorem zlm4_bits4 : (zlm4 N4c.indN4 N4c.etN4).Bits :=
  zlm4_bits (fun ν j t => (N4c.indN4_etN4_bits ν j t 0).1) (fun ν t p => (N4c.indN4_etN4_bits ν 0 t p).2)

/-- **S-E12a's kind factor is the batched indicators** (`kf4` sums over `blockKinds.tail`, the
indicators of kinds `1 … 8`). -/
theorem kfInd4 : KfInd (zlm4 N4c.indN4 N4c.etN4) N4c.kf4 := fun ν β t => by
  rw [N4c.kf4, Finset.sum_range (fun i => β ^ i * _)]
  refine sum_congr rfl fun i _ => ?_
  congr 1

/-! ## Z's statement on a node -/

theorem bkIdx4_eq (b : BlockKind) : N4c.bkIdx4 b = bkIdx b := by cases b <;> rfl

/-- **A target of a kind's form pins exactly the kind's rows** (3.x's `pins_*`). -/
theorem kindTgt_pins {b : BlockKind} {t : Block.Target} (h : N4c.KindTgt b t) (p : Block.Pos) :
    (t p).isNone = !isZeroRow b p.val := by
  match b, h with
  | .stream, ⟨L, i, h⟩ => rw [h]; exact pins_stream L i p
  | .streamStart, h => rw [h]; exact pins_streamStart p
  | .streamEnd41, h => rw [h]; exact pins_streamEnd41 p
  | .hashA, h => rw [h]; exact pins_hashA p
  | .hashB1, ⟨tag, h⟩ => rw [h]; exact pins_hashB1 tag p
  | .hashB2, h => rw [h]; exact pins_hashB2 p
  | .w43, ⟨i, s, h⟩ => rw [h]; exact pins_w43 i s p

/-- **`ZHolds` from the blocks' rows** (the converse of `zHolds_blocks`). -/
theorem zHolds_of_blocks4 {M : ZLM4} {zw : Wit} {L es : Log}
    (h : ∀ t < 2 ^ qL (kindOfC es), ∀ p : Fin (2 ^ 14),
      mvZ M zw M.Ak (kindOfC es) L es t p * mvZ M zw M.Bk (kindOfC es) L es t p =
        zBk zw (kindOfC es) L es t p + M.Et (kindOfC es) es t p) : ZHolds M zw L es := by
  intro σ u
  have h8 : 2 ^ mC 6 (kindOfC es) = 256 * 2 ^ qL (kindOfC es) := by
    rw [mC6_q, pow_add]; norm_num
  have hu : u.val / 256 < 2 ^ qL (kindOfC es) := by
    have := lt_of_lt_of_eq u.isLt h8; omega
  exact h _ hu (pAt σ u.val)

/-- A node's block rows read the block's kind only (`indN4_eq`). -/
theorem mvZ_node4 (ν : Rev4.NodeKind) (zw : Wit) (C : Block.Pos → Block.Pos → Bool) (L es : Log)
    (t : ℕ) (p : Fin (2 ^ 14)) :
    mvZ (zlm4 N4c.indN4 N4c.etN4) zw (kMat C) (.node ν) L es t p =
      ∑ k, kMat C (bkIdx (N4c.nodeBK4 ν t)) p k * zBk zw (.node ν) L es t k := by
  unfold mvZ
  rw [sum_eq_single (bkIdx (N4c.nodeBK4 ν t)) (fun j _ hj => by
      rw [show (zlm4 N4c.indN4 N4c.etN4).Ind (.node ν) j t = N4c.indN4 ν j t from rfl,
        N4c.indN4_eq, bkIdx4_eq, if_neg hj, zero_mul])
    (fun h => absurd (mem_univ _) h)]
  rw [show (zlm4 N4c.indN4 N4c.etN4).Ind (.node ν) _ t = N4c.indN4 ν _ t from rfl,
    N4c.indN4_eq, bkIdx4_eq, if_pos rfl, one_mul]

/-- The node's witness blocks are `f⁽⁰⁾`'s (`WitOf`). -/
theorem zBk_zB4 {R : P4b.FSrc} {zw : Wit} (hzw : WitOf R zw) {ν : Rev4.NodeKind} {L es : Log}
    (hν : kindOfC es = .node ν) (t : ℕ) (k : Fin (2 ^ 14)) :
    zBk zw (.node ν) L es t k = N4c.zB4 (R.fz L es) t k := by
  have := hzw L es (t * 2 ^ 14 + k.val)
  rw [hν] at this
  simp only [zBk, N4c.zB4, N4c.zW4]
  rw [mul_comm, this]

/-- **On a node, Z's statement is S-E12a's `truthZ4`** on `f⁽⁰⁾` (3.x's `zHolds_iff_truthZN`). -/
theorem zHolds_iff_truthZ4 {R : P4b.FSrc} {zw : Wit} (hzw : WitOf R zw) (hb : WitBits zw)
    {ν : Rev4.NodeKind} {L es : Log} (hν : kindOfC es = .node ν) :
    ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es ↔ N4c.truthZ4 ν (R.fz L es) := by
  have hq : 2 ^ qL (kindOfC es) = ν.blocks := by rw [hν]; rfl
  have hA : (zlm4 N4c.indN4 N4c.etN4).Ak = kMat Block.circuitR1CS.A := rfl
  have hB : (zlm4 N4c.indN4 N4c.etN4).Bk = kMat Block.circuitR1CS.B := rfl
  have hE : ∀ t p, (zlm4 N4c.indN4 N4c.etN4).Et (.node ν) es t p = N4c.etN4 ν t p := fun _ _ => rfl
  have hz : ∀ t, zBk zw (.node ν) L es t = N4c.zB4 (R.fz L es) t := fun t =>
    funext (zBk_zB4 hzw hν t)
  constructor
  · intro h blk hblk tgt ht k
    have hbf : N4c.nodeBK4 ν blk ≠ .free := fun e => by
      rw [← N4c.nodeKind4_none_iff ν hblk, ht] at e; cases e
    have e := zHolds_blocks h blk (by rw [hq]; exact hblk) k
    rw [hν, hA, hB, mvZ_node4, mvZ_node4, hE,
      kMat_mulVec _ hbf (kindTgt_pins (N4c.nodeKind4_kind ht)),
      kMat_mulVec _ hbf (kindTgt_pins (N4c.nodeKind4_kind ht))] at e
    simp only [N4c.etN4, ht, tgtE_eq, hz] at e
    exact e
  · intro h
    refine zHolds_of_blocks4 fun t ht p => ?_
    rw [hq] at ht
    rw [hν, hA, hB, mvZ_node4, mvZ_node4, hE]
    rcases hk : N4c.nodeKind4 ν t with _ | tgt
    · have hbf : N4c.nodeBK4 ν t = .free := (N4c.nodeKind4_none_iff ν ht).mp hk
      rw [hbf, kMat_free, kMat_free, N4c.etN4, hk]
      exact bit_sq (hb _ _ _ _)
    · have hbf : N4c.nodeBK4 ν t ≠ .free := fun e => by
        rw [← N4c.nodeKind4_none_iff ν ht, hk] at e; cases e
      rw [kMat_mulVec _ hbf (kindTgt_pins (N4c.nodeKind4_kind hk)),
        kMat_mulVec _ hbf (kindTgt_pins (N4c.nodeKind4_kind hk))]
      simp only [N4c.etN4, hk, tgtE_eq, hz]
      exact h t ht tgt hk p

end FR.Snd.P4a
