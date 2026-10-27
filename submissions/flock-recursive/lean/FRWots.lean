-- New for `flock-recursive` (BLUEPRINT §4.2, §7, stage S-E2; A.6).
import FRBlockKinds

/-!
# WOTS and the statement hash in the node circuit: `wots_sound`, `hashStmt_sound`

BLUEPRINT §4.2 (revision 3.5). The node checks `SigOk vk (traceDigest trᵢ) σᵢ` (the contract's
`RecursionFast.SigOk`) with BLAKE2s blocks of A.6's kinds, and the slot's statement with three
blocks (`hashStmt`). This module proves what the blocks and the selections compute:

* **one chain step** (`w43_step`): a `w43 i s` block whose message is `tagWots ‖ enc64 j ‖ i ‖ s ‖
  x` outputs the contract's `wotsStep j i s x`;
* **one chain** (`wots_chain_sound`): three steps whose inputs are selected by the selector bits
  `[d < 1]`, `[d < 2]` (steps 2, 3) and whose end is selected by `[d < 3]` give
  `wotsChain j i d (3 − d) ots` — three selector bits per chain (A.7's 399 per slot);
* **one path node** (`path_node`): a `hashB1 tagSigNode` block linked to a `hashB2` block with
  message `tagSigNode ‖ l ‖ r` outputs `sigNode l r`; the walk with the index bits is `sigRoot`
  (`sigRoot_bits`);
* **`wots_sound`**: chain ends, the leaf and the walk as above give `SigOk vk m σ`;
* **`hashStmt_sound`**: block A gives `leafStmt` of `stmt`'s fields, blocks B1–B2 `nodeStmt`. The
  two halves have **separate** message hypotheses: block A pins byte 0 to `tagLeaf`, block B1 to
  `tagNode`, so equating both messages with the same `stmt` is unsatisfiable
  (`hashStmt_ungated_vacuous`); the 8 `stmt` equalities of §4.2 must be gated by the kind
  (A's four by `s_L + s_P`, B1's and B2's by `s_N`; RESULT, finding F-1).

The key leaf's 67 blocks (`hashB1 tagWotsLeaf`, 65 `stream`, `streamEnd41`) are a stream whose
digest `FRBlockStream` computes; `wots_sound` takes the leaf as the contract's `wotsLeaf` of the
ends.
-/

namespace FR
open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit Block FR.Stream FR.Kinds

namespace Wots

/-! ## Selections (digest level) -/

/-- **One chain** (§4.2): steps `s = 1, 2, 3` from position `s − 1`; step `s`'s input is the
previous step's output when `d < s − 1`, else the signed value `ots`; the end is step 3's output
when `d < 3`, else `ots`. The end is the contract's chain from `ots` at position `d` to `3`. -/
theorem wots_chain_sound {j i d : ℕ} (hd : d ≤ 3) {ots e : Digest} {a out : ℕ → Digest}
    (hstep : ∀ s, 1 ≤ s → s ≤ 3 → out s = wotsStep j i (s - 1) (a s))
    (hsel : ∀ s, 1 ≤ s → s ≤ 3 → a s = if d + 1 < s then out (s - 1) else ots)
    (hend : e = if d < 3 then out 3 else ots) :
    e = wotsChain j i d (3 - d) ots := by
  have o1 := hstep 1 le_rfl (by omega); have o2 := hstep 2 (by omega) (by omega)
  have o3 := hstep 3 (by omega) le_rfl
  have a1 := hsel 1 le_rfl (by omega); have a2 := hsel 2 (by omega) (by omega)
  have a3 := hsel 3 (by omega) le_rfl
  interval_cases d <;> simp_all [wotsChain]

/-- **The path walk** (§4.2): `cur (t + 1) = sigNode l r` with `(l, r)` ordered by bit `t` of the
index is the contract's `sigRoot`. -/
theorem sigRoot_bits (cur : ℕ → Digest) : ∀ (path : List Digest) (j t0 : ℕ),
    (∀ t (ht : t < path.length), cur (t0 + t + 1) =
      if j / 2 ^ t % 2 = 0 then sigNode (cur (t0 + t)) path[t] else sigNode path[t] (cur (t0 + t))) →
    sigRoot j (cur t0) path = cur (t0 + path.length)
  | [], _, _, _ => rfl
  | s :: p, j, t0, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_zero, List.getElem_cons_zero] at h0
    rw [sigRoot, ← h0, sigRoot_bits cur p (j / 2) (t0 + 1) fun t ht => ?_]
    · simp [Nat.add_assoc, Nat.add_comm 1]
    · have := h (t + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, Nat.pow_succ, ← Nat.div_div_eq_div_mul] at this
      rw [show t0 + 1 + t + 1 = t0 + (t + 1) + 1 by omega, this,
        show t0 + (t + 1) = t0 + 1 + t by omega, Nat.div_div_eq_div_mul, Nat.mul_comm,
        ← Nat.div_div_eq_div_mul]

theorem msgDigits_length (m : Digest) : (msgDigits m).length = 128 := by
  simp [msgDigits, List.length_flatMap]

theorem wotsDigits_length (m : Digest) : (wotsDigits m).length = wotsLen := by
  simp [wotsDigits, msgDigits_length, wotsLen]

/-- **`wots_sound`** (§4.2): chain ends that are the contract's chains from the signed values at
the message's digits, the leaf of those ends, and a walk along the path with the index's bits that
reaches `vk`, give the contract's `SigOk`. -/
theorem wots_sound {vk m : Digest} {σ : Sig} (hidx : σ.idx < 2 ^ sigHeight)
    (hots : σ.ots.length = wotsLen) (hpath : σ.path.length = sigHeight) {ends : List Digest}
    (hlen : ends.length = wotsLen)
    (hends : ∀ i (hi : i < wotsLen), ends[i]'(hlen ▸ hi) =
      wotsChain σ.idx i ((wotsDigits m)[i]'(by rw [wotsDigits_length]; exact hi))
        (3 - (wotsDigits m)[i]'(by rw [wotsDigits_length]; exact hi)) (σ.ots[i]'(hots ▸ hi)))
    {cur : ℕ → Digest} (hleaf : cur 0 = wotsLeaf σ.idx ends)
    (hwalk : ∀ t (ht : t < σ.path.length), cur (t + 1) = if σ.idx / 2 ^ t % 2 = 0
      then sigNode (cur t) σ.path[t] else sigNode σ.path[t] (cur t))
    (hroot : cur sigHeight = vk) : SigOk vk m σ = true := by
  have hE : wotsEnds σ.idx m σ.ots = ends := by
    apply List.ext_getElem (by simp [wotsEnds, wotsDigits_length, hots, hlen])
    intro i h1 h2
    simp only [wotsEnds, List.getElem_mapIdx, List.getElem_zip]
    exact (hends i (hlen ▸ h2)).symm
  have hr := sigRoot_bits cur σ.path σ.idx 0 fun t ht => by simpa using hwalk t ht
  simp only [SigOk, hidx, hots, hpath, decide_true, Bool.true_and, decide_eq_true_eq, hE,
    ← hleaf, hr, Nat.zero_add, hroot]

/-! ## Blocks -/

section Blocks

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- **A chain step block** (A.6 `w43`): with message `tagWots ‖ enc64 j ‖ i ‖ s ‖ x` it outputs
`wotsStep j i s x`. -/
theorem w43_step {i s : ℕ} {w : Pos → Bool}
    (h : HoldsE (blockR1CS (w43 i.toUInt8 s.toUInt8).target)
      (targetVal R (w43 i.toUInt8 s.toUInt8).target) (liftBlock R w))
    {j : ℕ} {x : Digest}
    (hm : (msgBytes w).take 43 = tagWots :: enc64 j ++ [i.toUInt8, s.toUInt8] ++ x.toList) :
    readDigest w 256 = wotsStep j i s x := by
  rw [one_block_sound (w43 _ _) (L := 43) (by omega) rfl rfl rfl (fun p hp hp' => by
    simp [w43, show p ≠ 0 by omega, show p ≠ 9 by omega, show p ≠ 10 by omega, hp]) h, hm]
  rfl

/-- **A path node** (A.6 `hashB1 tagSigNode` linked to `hashB2`): with message `tagSigNode ‖ l ‖
r` it outputs `sigNode l r`. -/
theorem path_node {w₁ w₂ : Pos → Bool}
    (h₁ : HoldsE (blockR1CS (hashB1 tagSigNode).target) (targetVal R (hashB1 tagSigNode).target)
      (liftBlock R w₁))
    (h₂ : HoldsE (blockR1CS hashB2.target) (targetVal R hashB2.target) (liftBlock R w₂))
    (hl : ∀ j < 256, w₂ (pos j) = w₁ (pos (256 + j))) {l r : Digest}
    (hm : msgBytes w₁ ++ (msgBytes w₂).take 1 = tagSigNode :: l.toList ++ r.toList) :
    readDigest w₂ 256 = sigNode l r := by
  rw [(hashB_sound h₁ h₂ hl).1, hm]
  rfl

/-- **`hashStmt_sound`** (§4.2): block A with message `stmt[0, 64)` gives `leafStmt` of `stmt`'s
`h` and `n`; blocks B1–B2 linked, with messages `stmt[0, 64)` and `stmt[64, 128)`, give `nodeStmt`
of `stmt`'s `c₁`, `c₂`. -/
theorem hashStmt_sound {stmt : List UInt8} {wA w₁ w₂ : Pos → Bool}
    (hA : HoldsE (blockR1CS hashA.target) (targetVal R hashA.target) (liftBlock R wA))
    (h₁ : HoldsE (blockR1CS (hashB1 tagNode).target) (targetVal R (hashB1 tagNode).target)
      (liftBlock R w₁))
    (h₂ : HoldsE (blockR1CS hashB2.target) (targetVal R hashB2.target) (liftBlock R w₂))
    (hl : ∀ j < 256, w₂ (pos j) = w₁ (pos (256 + j))) :
    (msgBytes wA = stmt.take 64 → ∀ {h : Digest} {n : ℕ},
      stmt.take 41 = tagLeaf :: h.toList ++ enc64 n → readDigest wA 256 = leafStmt h n) ∧
    (msgBytes w₁ = stmt.take 64 → msgBytes w₂ = (stmt.drop 64).take 64 → ∀ {c₁ c₂ : Digest},
      stmt.take 65 = tagNode :: c₁.toList ++ c₂.toList → readDigest w₂ 256 = nodeStmt c₁ c₂) := by
  refine ⟨fun hm h n hs => hashA_leafStmt hA ?_, fun hm₁ hm₂ c₁ c₂ hs => hashB_nodeStmt h₁ h₂ hl ?_⟩
  · rw [hm, List.take_take, show min 41 64 = 41 from rfl, hs]
  · rw [hm₁, hm₂, List.take_take, show min 1 64 = 1 from rfl, ← List.take_add]; exact hs

/-- **Negative control (finding F-1)**: the ungated wiring — blocks A and B1 with the same
message — is unsatisfiable, so §4.2's `hashStmt_sound` with both message hypotheses at once is
vacuous; the `stmt` equalities must be gated by the kind. -/
theorem hashStmt_ungated_vacuous {wA w₁ : Pos → Bool}
    (hA : HoldsE (blockR1CS hashA.target) (targetVal R hashA.target) (liftBlock R wA))
    (h₁ : HoldsE (blockR1CS (hashB1 tagNode).target) (targetVal R (hashB1 tagNode).target)
      (liftBlock R w₁))
    (hm : msgBytes wA = msgBytes w₁) : False := by
  have a := hashA.msgByte_eq (p := 0) (by omega) rfl hA
  have b := (hashB1 tagNode).msgByte_eq (p := 0) (by omega) rfl h₁
  have e : (msgBytes wA)[0]? = (msgBytes w₁)[0]? := by rw [hm]
  simp only [msgBytes, List.getElem?_ofFn] at e
  simp only [Nat.mul_zero, Nat.add_zero, show (0 : ℕ) < 64 by omega, dite_true,
    Option.some.injEq] at a b e
  rw [← e, a] at b
  exact absurd b (by decide)

end Blocks

end Wots
end FR
