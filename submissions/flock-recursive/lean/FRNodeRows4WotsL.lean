-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2; stage S-E13b, track L-circ). 3.x:
-- `FRBlockStream.stream_sound`, `FRWots.path_node`, `sigRoot_bits`.
import FRNodeRows4WotsT

/-!
# The WOTS key leaf of a 4.1 node

**`leaf_out`**: the key leaf's 67 blocks (`hashB1 tagWotsLeaf`, 65 `stream`, `streamEnd41`), linked
by the leaf rows, hash `tagWotsLeaf ‖ enc64 idx ‖ e₀ ‖ … ‖ e₁₃₂`, the ends read off their mirrors
(`end9` for an even end, `end41lo`/`end41hi` for an odd one, which crosses a block boundary): the
contract's `wotsLeaf idx ends`.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block ProductCircuit Blake2sCircuit Kinds Stream

/-! ## Lists of digests -/

theorem flat_get : ∀ (l : List Digest) (q : ℕ) (hq : q < 32 * l.length),
    (l.flatMap Vector.toList).getD q 0 = (l.getD (q / 32) default).toList.getD (q % 32) 0
  | [], q, hq => by simp at hq
  | e :: l, q, hq => by
    rw [List.flatMap_cons]
    by_cases h : q < 32
    · rw [List.getD_append _ _ _ _ (by simpa using h)]
      simp [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [Vector.length_toList]
      rw [flat_get l (q - 32) (by simp at hq; omega)]
      have e1 : q / 32 = (q - 32) / 32 + 1 := by omega
      have e2 : q % 32 = (q - 32) % 32 := by omega
      simp only [e1, e2, List.getD_cons_succ]

/-- Byte `q` of a digest (`0` past 32). -/
def fb' (d : Digest) (q : ℕ) : UInt8 := d.toList.getD q 0

theorem fb'_eq (d : Digest) {q : ℕ} (hq : q < 32) : fb' d q = d[q] := by
  simp [fb', List.getD_eq_getElem?_getD, hq]

/-! ## The leaf -/

/-- The key leaf's blocks as a stream. -/
noncomputable def leafW (κ : NodeKind) (σ : ℕ) (w : Asg) : ℕ → Pos → Bool := fun u => bitsB4 w (wb κ σ (399 + u))

/-- The chain ends, read off their mirrors. -/
noncomputable def endsD (κ : NodeKind) (σ : ℕ) (w : Asg) : List Digest := (List.range wotsLen).map fun i => md κ σ (endG i) w

theorem nB4265 : nBlocks 4265 = 67 := by decide

/-- The leaf message's byte `p`. -/
theorem leafMsg_get (j : ℕ) (ends : List Digest) (hl : ends.length = wotsLen) {p : ℕ} (hp : p < 4265) :
    (tagWotsLeaf :: enc64 j ++ ends.flatMap Vector.toList).getD p 0 =
      if p = 0 then tagWotsLeaf else if p < 9 then (enc64 j).getD (p - 1) 0
      else fb' (ends.getD ((p - 9) / 32) default) ((p - 9) % 32) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rfl
  rw [if_neg (by omega), show p = (p - 1) + 1 by omega, List.cons_append, List.getD_cons_succ]
  by_cases h9 : p - 1 + 1 < 9
  · rw [if_pos h9, List.getD_append _ _ _ _ (by simp [enc64]; omega), Nat.add_sub_cancel]
  · rw [if_neg h9, List.getD_append_right _ _ _ _ (by simp [enc64]; omega), enc64_length,
      flat_get _ _ (by rw [hl]; unfold wotsLen; omega)]
    simp only [fb', show p - 1 - 8 = p - 1 + 1 - 9 by omega]

/-- The key leaf's message bytes. -/
theorem leaf_bytes {κ : NodeKind} {w : Asg} (hZ : truthZ4 κ w) (hS : truthS4 κ w) {σ : ℕ} (hσ : σ < 2)
    (hj : w (mc κ σ 399 0) = w (Lc κ σ 0)) :
    Stream.streamBytes (leafW κ σ w) 4265 = tagWotsLeaf :: enc64 (idxOf κ σ w) ++ (endsD κ σ w).flatMap Vector.toList := by
  have hlen : (tagWotsLeaf :: enc64 (idxOf κ σ w) ++ (endsD κ σ w).flatMap Vector.toList).length = 4265 := by
    simp [endsD, enc64, List.length_flatMap, wotsLen, Function.comp_def, List.map_const', List.sum_replicate]
  have hel : (endsD κ σ w).length = wotsLen := by simp [endsD]
  refine List.ext_getElem (by rw [Stream.streamBytes_length, hlen]) fun p h1 h2 => ?_
  rw [Stream.streamBytes_length] at h1
  have hL : ∀ (l : List UInt8) (h : p < l.length), l[p] = l.getD p 0 := fun l h => by
    simp [List.getD_eq_getElem?_getD, h]
  rw [hL _ h2, leafMsg_get _ _ hel h1]
  simp only [Stream.streamBytes, List.getElem_map, List.getElem_range]
  rw [← msgBytes_getD _ (Nat.mod_lt _ (by norm_num)), leafW]
  have hu67 : p / 64 < 67 := by omega
  have hw := holds_wots hZ hσ (o := 399 + p / 64) (by unfold wotsSlot4; omega)
  have hend : ∀ i (hi : i < wotsLen) (q : ℕ), q < 32 →
      fb' ((endsD κ σ w).getD i default) q = fb (w (mc κ σ (endG i) (q / 16))) (q % 16) :=
    fun i hi q hq => by
      rw [fb'_eq _ hq, List.getD_eq_getElem _ _ (by rw [hel]; exact hi)]
      simp only [endsD, List.getElem_map, List.getElem_range]; exact md_get _ _ _ _ hq
  rcases (by omega : p = 0 ∨ (1 ≤ p ∧ p < 9) ∨ (64 ≤ p ∧ p % 64 < 9) ∨ (9 ≤ p % 64 ∧ p % 64 < 41) ∨
    (41 ≤ p % 64 ∧ p / 64 < 66)) with rfl | ⟨h1p, h9⟩ | ⟨h1u, h9⟩ | ⟨h9, h41⟩ | ⟨h41, h66⟩
  · -- the tag
    rw [if_pos rfl, msgBytes_getD _ (by norm_num)]
    rw [show 399 + 0 / 64 = 399 from rfl, NodeT.wotsTgt, if_neg (by norm_num), if_pos rfl] at hw
    exact (hashB1 tagWotsLeaf).msgByte_eq (p := 0) (by norm_num) (u := tagWotsLeaf) (by simp [hashB1]) hw
  · -- `j`
    rw [if_neg (by omega), if_pos h9, show p / 64 = 0 by omega, show p % 64 = 1 + (p - 1) by omega]
    exact j_byte hS hσ (t := 399 + 0) (by omega) (k := p - 1) (by omega) hj
  · -- `end41hi` of end `2(u − 1) + 1`
    rw [if_neg (by omega), if_neg (by omega)]
    have := fam_byte (f := 4) hS hσ (by decide) (t := p / 64 - 1) (by simp [NodeT.fam]; omega) (k := p % 64)
      (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
    simp only [NodeT.fam, Nat.zero_add, show 400 + (p / 64 - 1) = 399 + p / 64 by omega] at this
    rw [this, hend _ (by unfold wotsLen; omega) _ (Nat.mod_lt _ (by norm_num)),
      show (p - 9) % 32 = 184 / 8 + p % 64 by omega, show (p - 9) / 32 = 2 * (p / 64 - 1) + 1 by omega]
    simp only [endG, show (2 * (p / 64 - 1) + 1) % 2 ≠ 0 by omega, if_false,
      show (2 * (p / 64 - 1) + 1) / 2 = p / 64 - 1 by omega]
  · -- `end9` of end `2u`
    rw [if_neg (by omega), if_neg (by omega)]
    have := fam_byte (f := 2) hS hσ (by decide) (t := p / 64) (by simp [NodeT.fam]; omega) (k := p % 64 - 9)
      (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
    simp only [NodeT.fam, Nat.zero_div, Nat.zero_add, show 9 + (p % 64 - 9) = p % 64 by omega] at this
    rw [this, hend _ (by unfold wotsLen; omega) _ (Nat.mod_lt _ (by norm_num)),
      show (p - 9) % 32 = p % 64 - 9 by omega, show (p - 9) / 32 = 2 * (p / 64) by omega]
    simp only [endG, show 2 * (p / 64) % 2 = 0 by omega, if_true, show 2 * (p / 64) / 2 = p / 64 by omega]
  · -- `end41lo` of end `2u + 1`
    rw [if_neg (by omega), if_neg (by omega)]
    have := fam_byte (f := 3) hS hσ (by decide) (t := p / 64) (by simp [NodeT.fam]; omega) (k := p % 64 - 41)
      (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
    simp only [NodeT.fam, Nat.zero_div, Nat.zero_add, show 41 + (p % 64 - 41) = p % 64 by omega] at this
    rw [this, hend _ (by unfold wotsLen; omega) _ (Nat.mod_lt _ (by norm_num)),
      show (p - 9) % 32 = p % 64 - 41 by omega, show (p - 9) / 32 = 2 * (p / 64) + 1 by omega]
    simp only [endG, show (2 * (p / 64) + 1) % 2 ≠ 0 by omega, if_false,
      show (2 * (p / 64) + 1) / 2 = p / 64 by omega]

/-- **The key leaf** outputs `wotsLeaf idx ends`. -/
theorem leaf_out {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hZ : truthZ4 κ w) (hS : truthS4 κ w)
    {σ : ℕ} (hσ : σ < 2) (hj : w (mc κ σ 399 0) = w (Lc κ σ 0)) (hlf : ∀ r ∈ leafRows κ σ, r.Holds w) :
    Read.digestOf w (hc (wb κ σ 465) 2) (hc (wb κ σ 465) 3) = wotsLeaf (idxOf κ σ w) (endsD κ σ w) := by
  have hw := fun u (hu : u < 67) => holds_wots hZ hσ (o := 399 + u) (by unfold wotsSlot4; omega)
  have key := chain_digest 4265 (leafW κ σ w) ?_ ?_ ?_ ?_
  · rw [nB4265, leaf_bytes hZ hS hσ hj] at key
    rw [← readDigest_digestOf]
    exact key
  · -- `h_in = h0`
    have h0 := hw 0 (by norm_num)
    rw [show 399 + 0 = 399 from rfl, NodeT.wotsTgt, if_neg (by norm_num), if_pos rfl] at h0
    exact (hashB1 tagWotsLeaf).hIn_eq_h0 rfl h0
  · intro u hu
    rw [nB4265] at hu
    have h := hw u hu
    rcases (by omega : u = 0 ∨ (1 ≤ u ∧ u < 66) ∨ u = 66) with rfl | ⟨h1, h2⟩ | rfl
    · rw [show 399 + 0 = 399 from rfl, NodeT.wotsTgt, if_neg (by norm_num), if_pos rfl] at h
      rw [leafW, (hashB1 tagWotsLeaf).block_sound h]
      simp [ctrAt, flagAt, nB4265, hashB1, Stream.flagOf]
    · rw [NodeT.wotsTgt, if_neg (by omega), if_neg (by omega), if_pos (by omega),
        show 399 + u - 399 = u by omega] at h
      exact block_sound h
    · rw [show 399 + 66 = 465 from rfl, NodeT.wotsTgt, if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_pos rfl] at h
      rw [leafW, streamEnd41.block_sound h]
      simp [ctrAt, flagAt, nB4265, streamEnd41, Stream.flagOf]
  · intro u hu j hj
    rw [nB4265] at hu
    have e := fun h (hh : h < 2) => eqR_val hone (hlf _ (List.mem_flatMap.2 ⟨u, List.mem_range.2 (by omega),
      List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩⟩))
    simp only [Lin.ev_cell] at e
    simp only [leafW]
    rw [bitsB4_bit _ _ (by omega), bitsB4_bit _ _ (by omega)]
    have := e (j / 128) (by omega)
    unfold hc at this
    rw [show wb κ σ (399 + (u + 1)) = wb κ σ (400 + u) by unfold wb; omega, this,
      show wb κ σ (399 + u) * 128 + (256 + j) / 128 = wb κ σ (399 + u) * 128 + (2 + j / 128) by omega,
      bitN_mod _ (256 + j), bitN_mod _ j, show (256 + j) % 128 = j % 128 by omega]
  · intro p hp hp'
    rw [nB4265] at hp'
    have h := hw 66 (by norm_num)
    rw [show 399 + 66 = 465 from rfl, NodeT.wotsTgt, if_neg (by norm_num), if_neg (by norm_num),
      if_neg (by norm_num), if_pos rfl] at h
    rw [show p / 64 = 66 by omega, leafW]
    exact streamEnd41.msgByte_eq (by omega) (by simp [streamEnd41]; omega) h

end W4
end FR
