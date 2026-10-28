-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8/A.9 `finSh` on a node, A.10 S1/S2; stage P4a
-- pass 5 (P4e)): the node's S2 law at S-E12a's layout (`chainLk4`, `srcB4`/`mirB4`). 3.x templates:
-- `FRSoundnessFrSh` (`wNode`, `resNode`, `sh_sum_node`, `res_ne_node`).
import FRSoundness4P4aNZ

/-!
# The node's S2 law at revision 4.1: `SNode` for `truthS4`

A node's S truth (S-E12a's `truthS4` on `f⁽⁰⁾`, **`truthS4_iff`**) is **`ShHoldsN4`**: block `y`'s
`h_out` is block `y + 1`'s `h_in` on the chain mask `chainLk4` (both signed children's main
chains), and each WOTS link family's field equals its mirror (`srcB4`/`mirB4`, 3.x's families
rebased).

* **`wNode4`**: S2's weight on a node (A.9 `finSh` (ii), 3.x's `wNode` at the 4.1 layout and
  `nb = m − 14` block coordinates): `Out` at `[lk y] eq(τ, y)`, `In` at the shifted mask plus the
  start term `κ_s ([y = 0] + [y = chLen₀])`, the eight families batched by `κ_s^(f+2)`.
* **`resNode4`** (`J = 10`), **`sh_sum_node4`**: the true sum is the batched residual (the target is
  `0`: `c0S_node4`). **`res_ne_node4`**: a failed `ShHoldsN4` leaves a nonzero residual.
* **`sNode4`**: P4c's `SNode wN4 (truthSN4 zw) zw`; **`wNLocal4`**; **`wNS4`**, `hNS4` (the
  weight's extension at S2's point, `pendS4_pendBad4`'s `hNS`).

What the node verifier computes in `finSh` (ii) is `implN κ`'s (`VnodeC`; parametric): that it is
`wNS4` is the node ops' specification, not proved here.
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## The layout's bounds -/

section Bounds
variable {ν : Rev4.NodeKind}

theorem nodeBK4_lt {blk : ℕ} (h : N4c.nodeBK4 ν blk ≠ .free) : blk < 2 ^ nbC (.node ν) := by
  unfold N4c.nodeBK4 at h
  rcases e : N4c.ivAt (N4c.nodeLayout4 ν) blk with _ | iv
  · rw [e] at h; exact absurd rfl h
  · have hm := List.mem_of_find?_eq_some e
    have hk : iv.mem blk = true := by simpa using List.find?_some e
    have := N4c.layout_bounds ν hm
    simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hk
    show blk < ν.blocks
    omega

theorem chainLk4_lt {y : ℕ} (h : N4c.chainLk4 ν y = true) : y + 1 < 2 ^ nbC (.node ν) :=
  nodeBK4_lt (by rw [N4c.chainLk4_stream h]; exact fun e => by cases e)

theorem chLen0_lt (ν : Rev4.NodeKind) : N4c.chLen ν 0 < 2 ^ nbC (.node ν) := by
  refine nodeBK4_lt (ν := ν) ?_
  rw [N4c.bk_of_mem (iv := ⟨.streamStart, N4c.chBase ν 1, N4c.chBase ν 1 + 1,
      fun _ => some Kinds.streamStart.target⟩)
    (N4c.chainIvs_mem ν (σ := 1) (by norm_num) _ (by simp [N4c.chainIvs]))
    (by simp [N4c.TIv.mem, N4c.chBase])]
  exact fun e => by cases e

theorem hUsedN_lt (ν : Rev4.NodeKind) : N4c.hUsedN ν < 2 ^ nbC (.node ν) := by
  obtain ⟨h1, h2⟩ := N4c.hEnd_le ν
  obtain ⟨-, h3, h4, -⟩ := Rev4.regions_fit ν
  have h5 : 1 ≤ N4c.nAgg ν * ν.maxK := by cases ν <;> decide
  show _ < ν.blocks
  omega

theorem fam_mir_lt {f t : ℕ} (ht : t < (NodeT.fam f).n) : (NodeT.fam f).mir t < Layout.mirSources := by
  have hm : Layout.mirSources = 581 := rfl
  rw [hm]
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp only [NodeT.fam, id] at ht ⊢ <;> omega

theorem srcB4_lt {σ f t : ℕ} (hσ : σ < 2) (ht : t < (NodeT.fam f).n) :
    N4c.srcB4 ν σ f t < 2 ^ nbC (.node ν) := by
  have hs : (NodeT.fam f).src t < Rev4.wotsSlot4 := fam_src_lt ht
  refine nodeBK4_lt ?_
  rw [N4c.srcB4, N4c.nodeBK4_wots ν hσ hs]
  exact N4c.wotsKindAt_ne_free _

theorem mirB4_lt {σ f t : ℕ} (hσ : σ < 2) (ht : t < (NodeT.fam f).n) :
    N4c.mirB4 ν σ f t < 2 ^ nbC (.node ν) :=
  lt_trans (N4c.mir4_fits ν hσ (fam_mir_lt ht)).2.1 (hUsedN_lt ν)

/-- Distinct sources of a family lie in distinct blocks (3.x's `srcB_inj`). -/
theorem srcB4_inj {f σ σ' t t' : ℕ} (hσ : σ < 2) (hσ' : σ' < 2) (ht : t < (NodeT.fam f).n)
    (ht' : t' < (NodeT.fam f).n) (h : N4c.srcB4 ν σ' f t' = N4c.srcB4 ν σ f t) : σ' = σ ∧ t' = t := by
  have h1 := fam_src_lt ht
  have h2 := fam_src_lt ht'
  have hw : Layout.wotsSlot = 498 := rfl
  have hw4 : Rev4.wotsSlot4 = 498 := rfl
  unfold N4c.srcB4 N4c.wotsB at h
  rw [hw4] at h
  rw [hw] at h1 h2
  have hs : σ' = σ := by
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;>
      rcases (by omega : σ' = 0 ∨ σ' = 1) with rfl | rfl <;> omega
  subst hs
  exact ⟨rfl, fam_src_inj (f := f) (by omega)⟩

end Bounds

/-! ## The truth -/

/-- **A node's S truth** on the witness's blocks (S-E12a's `truthS4`). -/
def ShHoldsN4 (ν : Rev4.NodeKind) (z : ℕ → ℕ → F) : Prop :=
  (∀ y, N4c.chainLk4 ν y = true → ∀ j < 256, z (y + 1) j = z y (256 + j)) ∧
    ∀ f < nLinkFam, ∀ σ < 2, ∀ t < (NodeT.fam f).n, ∀ s < NodeT.fbits f,
      z (N4c.srcB4 ν σ f t) (NodeT.fpos f s) = z (N4c.mirB4 ν σ f t) (NodeT.mpos f t s)

/-- **The node's S truth by kind** (`Front4a.truthSN`; a segment's is `truthS`'s own branch). -/
def truthSN4 (zw : Wit) : CKind → Log → Log → Prop
  | .node ν, L, es => ShHoldsN4 ν (zNodeC zw (.node ν) L es)
  | .seg _, _, _ => True

theorem zNodeC_zN4 {R : P4b.FSrc} {zw : Wit} (hzw : WitOf R zw) {ν : Rev4.NodeKind} {L es : Log}
    (hν : kindOfC es = .node ν) : zNodeC zw (.node ν) L es = N4c.zN4 (R.fz L es) := by
  funext blk p
  have := hzw L es (blk * 2 ^ 14 + p)
  rw [hν] at this
  simp only [zNodeC, N4c.zN4, N4c.zW4, this]

/-- **`truthSN4` is S-E12a's `truthS4`** on `f⁽⁰⁾`. -/
theorem truthS4_iff {R : P4b.FSrc} {zw : Wit} (hzw : WitOf R zw) {ν : Rev4.NodeKind} {L es : Log}
    (hν : kindOfC es = .node ν) : N4c.truthS4 ν (R.fz L es) ↔ truthSN4 zw (kindOfC es) L es := by
  rw [hν]
  simp only [truthSN4, zNodeC_zN4 hzw hν]
  rfl

/-! ## The weight and the residual -/

section Weight
variable (ν : Rev4.NodeKind)

/-- The `Out` weight `[lk y] eq(τ, y)`. -/
def lkW4 {n : ℕ} (τ : Fin n → F) (y : ℕ) : F := if N4c.chainLk4 ν y then eqAtR τ y else 0

/-- The `In` weight: `[lk (y−1)] eq(τ, y − 1) + κ_s ([y = 0] + [y = chLen₀])`. -/
def shN4 {n : ℕ} (τ : Fin n → F) (κ : F) (y : ℕ) : F :=
  (if 1 ≤ y ∧ N4c.chainLk4 ν (y - 1) then eqAtR τ (y - 1) else 0) +
    κ * ((if y = 0 then 1 else 0) + if y = N4c.chLen ν 0 then 1 else 0)

/-- Family `f`'s weight at cell `(y, q)`: `Σ_σ Σ_t Σ_s eq(τ, src) eq(θ, s)` times the
source-minus-mirror indicator (3.x's `famW` through `linkInd_sum`). -/
def famW4 (f : ℕ) {n : ℕ} (τ : Fin n → F) (θ : Fin 10 → F) (y q : ℕ) : F :=
  ∑ σ ∈ range 2, ∑ t ∈ range (NodeT.fam f).n, ∑ s ∈ range (NodeT.fbits f),
    eqAtR τ (N4c.srcB4 ν σ f t) * eqAtR θ s *
      ((if y = N4c.srcB4 ν σ f t ∧ q = NodeT.fpos f s then 1 else 0) -
        (if y = N4c.mirB4 ν σ f t ∧ q = NodeT.mpos f t s then 1 else 0))

/-- **A node's S2 weight** (A.9 `finSh` (ii)). -/
def wNode4 {n : ℕ} (τ : Fin n → F) (θ : Fin 10 → F) (κ : F) (y q : ℕ) : F :=
  lkW4 ν τ y * slotT θ 256 q + shN4 ν τ κ y * slotT θ 0 q +
    ∑ f ∈ range nLinkFam, κ ^ (f + 2) * famW4 ν f τ θ y q

/-- **A node's residuals** (`J = 10`): the masked links, the starts, the families' differences
(table `f + 2` at a source block and a field bit). -/
def resNode4 (z : ℕ → ℕ → F) (j u q : ℕ) : F :=
  if j = 0 then (if q < 256 ∧ N4c.chainLk4 ν u then z u (256 + q) + z (u + 1) q else 0)
  else if j = 1 then (if q < 256 then z 0 q + z (N4c.chLen ν 0) q else 0)
  else ∑ σ ∈ range 2, ∑ t ∈ range (NodeT.fam (j - 2)).n,
    if u = N4c.srcB4 ν σ (j - 2) t ∧ q < NodeT.fbits (j - 2) then
      z u (NodeT.fpos (j - 2) q) - z (N4c.mirB4 ν σ (j - 2) t) (NodeT.mpos (j - 2) t q) else 0

end Weight

section Sum
variable {ν : Rev4.NodeKind}

/-- Two outer and two inner sums swap. -/
theorem sum_swap22 (A B C D : Finset ℕ) (g : ℕ → ℕ → ℕ → ℕ → F) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, g a b c d =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, g a b c d :=
  calc _ = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D, g a b c d := sum_congr rfl fun _ _ => sum_comm
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ d ∈ D, ∑ b ∈ B, g a b c d :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, g a b c d := sum_comm
    _ = _ := sum_congr rfl fun _ _ => sum_comm

theorem sum_delta2 {A B a b : ℕ} (ha : a < A) (hb : b < B) (z : ℕ → ℕ → F) :
    ∑ q ∈ range B, ∑ y ∈ range A, (if y = a ∧ q = b then (1 : F) else 0) * z y q = z a b := by
  rw [sum_eq_single b, sum_eq_single a]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (mem_range.2 ha) h
  · intro q _ hq
    exact sum_eq_zero fun y _ => by simp [hq]
  · intro h; exact absurd (mem_range.2 hb) h

/-- Family `f`'s part of the true sum: the weighted source-minus-mirror differences. -/
theorem sum_famW4 {f : ℕ} (τ : Fin (nbC (.node ν)) → F) (θ : Fin 10 → F) (z : ℕ → ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)), famW4 ν f τ θ y q * z y q =
      ∑ σ ∈ range 2, ∑ t ∈ range (NodeT.fam f).n, ∑ s ∈ range (NodeT.fbits f),
        eqAtR τ (N4c.srcB4 ν σ f t) * eqAtR θ s *
          (z (N4c.srcB4 ν σ f t) (NodeT.fpos f s) -
            z (N4c.mirB4 ν σ f t) (NodeT.mpos f t s)) := by
  simp only [famW4, sum_mul]
  rw [sum_comm (s := range (2 ^ 10))]
  simp only [sum_comm (s := range (2 ^ 10)) (t := range 2), sum_comm (s := range (2 ^ 10))
    (t := range (NodeT.fam f).n), sum_comm (s := range (2 ^ 10)) (t := range (NodeT.fbits f))]
  rw [sum_comm (s := range (2 ^ nbC (.node ν))) (t := range 2)]
  refine sum_congr rfl fun σ hσ => ?_
  rw [sum_comm (s := range (2 ^ nbC (.node ν))) (t := range (NodeT.fam f).n)]
  refine sum_congr rfl fun t ht => ?_
  rw [sum_comm (s := range (2 ^ nbC (.node ν))) (t := range (NodeT.fbits f))]
  refine sum_congr rfl fun s hs => ?_
  have hσ' := mem_range.1 hσ
  have ht' := mem_range.1 ht
  have hb := (NodeT.fam_bounds (s := s) hσ' ht').2.2 (mem_range.1 hs)
  rw [sum_comm]
  simp only [mul_assoc, ← mul_sum, sub_mul, sum_sub_distrib]
  rw [sum_delta2 (srcB4_lt hσ' ht') hb.1, sum_delta2 (mirB4_lt hσ' ht') hb.2]

/-- Family `f`'s residual table, batched at `(τ, θ)`. -/
theorem sum_resF4 {f : ℕ} (τ : Fin (nbC (.node ν)) → F) (θ : Fin 10 → F) (z : ℕ → ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ u ∈ range (2 ^ nbC (.node ν)), eqAtR τ u * eqAtR θ q *
      resNode4 ν z (f + 2) u q =
      ∑ σ ∈ range 2, ∑ t ∈ range (NodeT.fam f).n, ∑ s ∈ range (NodeT.fbits f),
        eqAtR τ (N4c.srcB4 ν σ f t) * eqAtR θ s *
          (z (N4c.srcB4 ν σ f t) (NodeT.fpos f s) -
            z (N4c.mirB4 ν σ f t) (NodeT.mpos f t s)) := by
  simp only [resNode4, show f + 2 ≠ 0 by omega, show f + 2 ≠ 1 by omega, if_false,
    Nat.add_sub_cancel, mul_sum]
  rw [sum_swap22]
  refine sum_congr rfl fun σ hσ => sum_congr rfl fun t ht => ?_
  have hσ' := mem_range.1 hσ
  have ht' := mem_range.1 ht
  rw [sum_comm, sum_eq_single (N4c.srcB4 ν σ f t)]
  · simp only [true_and, mul_ite, mul_zero]
    rw [sum_range_ite_lt (NodeT.fbits_le f)]
  · intro u _ hu; exact sum_eq_zero fun q _ => by simp [hu]
  · intro h; exact absurd (mem_range.2 (srcB4_lt hσ' ht')) h

theorem chainLk4_top (ν : Rev4.NodeKind) : N4c.chainLk4 ν (2 ^ nbC (.node ν) - 1) = false := by
  by_contra h
  have := chainLk4_lt (Bool.not_eq_false _ ▸ h)
  have := Nat.two_pow_pos (nbC (.node ν))
  omega

/-- **The node's true S2 sum is its residual** (3.x's `sh_sum_node`; the target is `0`). -/
theorem sh_sum_node4 (τ : Fin (nbC (.node ν)) → F) (θ : Fin 10 → F) (κ : F) (z : ℕ → ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)), wNode4 ν τ θ κ y q * z y q =
      resSum (nbC (.node ν)) 10 (resNode4 ν z) τ θ κ := by
  set O : ℕ → F := fun y => thS θ fun σ => z y (256 + σ)
  set I : ℕ → F := fun y => thS θ fun σ => z y σ
  set G : ℕ → F := fun f => ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)), famW4 ν f τ θ y q * z y q
  have hL : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)), wNode4 ν τ θ κ y q * z y q =
      ∑ y ∈ range (2 ^ nbC (.node ν)), (lkW4 ν τ y * O y + shN4 ν τ κ y * I y) +
        ∑ f ∈ range nLinkFam, κ ^ (f + 2) * G f := by
    have e1 : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)),
        (lkW4 ν τ y * slotT θ 256 q + shN4 ν τ κ y * slotT θ 0 q) * z y q =
        ∑ y ∈ range (2 ^ nbC (.node ν)), (lkW4 ν τ y * O y + shN4 ν τ κ y * I y) := by
      rw [sum_comm]
      refine sum_congr rfl fun y _ => ?_
      simp only [add_mul, sum_add_distrib, mul_assoc]
      rw [← mul_sum, ← mul_sum, sum_slotT θ (by norm_num), sum_slotT θ (by norm_num)]
      simp only [O, I, thS, zero_add]
    have e2 : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)),
        (∑ f ∈ range nLinkFam, κ ^ (f + 2) * famW4 ν f τ θ y q) * z y q =
        ∑ f ∈ range nLinkFam, κ ^ (f + 2) * G f := by
      simp only [G, sum_mul, mul_sum, mul_assoc]
      rw [sum_congr rfl fun q _ => sum_comm, sum_comm]
    simp only [wNode4, add_mul (lkW4 ν τ _ * _ + _), sum_add_distrib]
    rw [e1, e2, sum_add_distrib]
  have hN : N4c.chLen ν 0 < 2 ^ nbC (.node ν) := chLen0_lt ν
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ nbC (.node ν) = M + 1 := ⟨2 ^ nbC (.node ν) - 1, by have := Nat.two_pow_pos (nbC (.node ν)); omega⟩
  have hS : ∑ y ∈ range (2 ^ nbC (.node ν)), shN4 ν τ κ y * I y =
      ∑ u ∈ range (2 ^ nbC (.node ν)), lkW4 ν τ u * I (u + 1) + κ * (I 0 + I (N4c.chLen ν 0)) := by
    have e1 : ∑ y ∈ range (2 ^ nbC (.node ν)), shN4 ν τ κ y * I y =
        ∑ y ∈ range (2 ^ nbC (.node ν)), (if 1 ≤ y ∧ N4c.chainLk4 ν (y - 1) then eqAtR τ (y - 1) * I y else 0) +
          κ * (I 0 + I (N4c.chLen ν 0)) := by
      simp only [shN4, add_mul, sum_add_distrib, ite_mul, zero_mul, mul_ite, mul_one, mul_zero,
        one_mul, mul_assoc, ← mul_sum, sum_ite_eq', mem_range, hN, Nat.two_pow_pos, if_true]
    have hl : N4c.chainLk4 ν M = false := by
      have := chainLk4_top ν; rw [hM, Nat.add_sub_cancel] at this; exact this
    rw [e1, hM, sum_range_succ', sum_range_succ]
    simp only [show ¬ (1 ≤ 0 ∧ N4c.chainLk4 ν (0 - 1) = true) from fun h => absurd h.1 (by omega),
      if_false, add_zero, Nat.add_sub_cancel, show ∀ u, 1 ≤ u + 1 from fun u => by omega, true_and]
    simp only [lkW4, hl, Bool.false_eq_true, if_false, zero_mul, add_zero, ite_mul, zero_mul]
  have hR0 : ∀ u, ∑ q ∈ range (2 ^ 10), eqAtR θ q * resNode4 ν z 0 u q =
      if N4c.chainLk4 ν u then O u + I (u + 1) else 0 := by
    intro u
    simp only [resNode4, if_true, ite_and, mul_ite, mul_zero]
    rw [sum_range_ite_lt (by norm_num)]
    by_cases h : N4c.chainLk4 ν u <;> simp only [h, if_true, if_false, sum_const_zero, O, I, thS,
      mul_add, sum_add_distrib, Bool.false_eq_true]
  have hR1 : ∀ u, ∑ q ∈ range (2 ^ 10), eqAtR θ q * resNode4 ν z 1 u q =
      I 0 + I (N4c.chLen ν 0) := by
    intro u
    simp only [resNode4, one_ne_zero, if_false, if_true, mul_ite, mul_zero]
    rw [sum_range_ite_lt (by norm_num)]
    simp only [I, thS, mul_add, sum_add_distrib]
  have hRf : ∀ f, ∑ q ∈ range (2 ^ 10), ∑ u ∈ range (2 ^ nbC (.node ν)), eqAtR τ u * eqAtR θ q *
      resNode4 ν z (f + 2) u q = G f := fun f => by
    simp only [G]; rw [sum_resF4, sum_famW4]
  have hres : resSum (nbC (.node ν)) 10 (resNode4 ν z) τ θ κ =
      ∑ u ∈ range (2 ^ nbC (.node ν)), lkW4 ν τ u * (O u + I (u + 1)) + κ * (I 0 + I (N4c.chLen ν 0)) +
        ∑ f ∈ range nLinkFam, κ ^ (f + 2) * G f := by
    unfold resSum
    rw [show range 10 = range (nLinkFam + 1 + 1) from rfl, sum_range_succ', sum_range_succ']
    simp only [hRf, pow_zero, one_mul, zero_add, pow_one]
    rw [sum_comm (s := range (2 ^ 10)), sum_comm (s := range (2 ^ 10))]
    simp only [mul_assoc, ← mul_sum, hR0, hR1, ← sum_mul, sum_eqAtR_one, one_mul]
    simp only [lkW4, mul_ite, mul_zero, ite_mul, zero_mul]
    ring
  rw [hL, hres, sum_add_distrib, hS]
  simp only [lkW4, mul_add, sum_add_distrib, ite_mul, zero_mul]
  ring

/-! ## A failed truth leaves a nonzero residual -/

/-- **A family residual at a source's field bit** is the source-minus-mirror difference. -/
theorem resNode4_src (z : ℕ → ℕ → F) {f σ t s : ℕ} (hσ : σ < 2) (ht : t < (NodeT.fam f).n)
    (hs : s < NodeT.fbits f) :
    resNode4 ν z (f + 2) (N4c.srcB4 ν σ f t) s =
      z (N4c.srcB4 ν σ f t) (NodeT.fpos f s) - z (N4c.mirB4 ν σ f t) (NodeT.mpos f t s) := by
  simp only [resNode4, show f + 2 ≠ 0 by omega, show f + 2 ≠ 1 by omega, if_false,
    Nat.add_sub_cancel]
  rw [sum_eq_single σ, sum_eq_single t]
  · simp only [hs, and_true, if_true]
  · intro t' ht' hne
    rw [if_neg fun he => hne (srcB4_inj hσ hσ ht (mem_range.1 ht') he.1.symm).2]
  · intro h; exact absurd (mem_range.2 ht) h
  · intro σ' hσ' hne
    refine sum_eq_zero fun t' ht' => ?_
    rw [if_neg fun he => hne (srcB4_inj hσ (mem_range.1 hσ') ht (mem_range.1 ht') he.1.symm).1]
  · intro h; exact absurd (mem_range.2 hσ) h

theorem shHoldsN4_of_res {z : ℕ → ℕ → F}
    (h : ∀ j < 10, ∀ u < 2 ^ nbC (.node ν), ∀ q < 2 ^ 10, resNode4 ν z j u q = 0) :
    ShHoldsN4 ν z := by
  refine ⟨fun y hy j hj => ?_, fun f hf σ hσ t ht s hs => ?_⟩
  · have e := h 0 (by norm_num) y (by have := chainLk4_lt hy; omega) j (by omega)
    simp only [resNode4, if_true, hj, hy, and_self] at e
    exact (CharTwo.add_eq_zero.mp e).symm
  · have hb := (NodeT.fam_bounds (s := s) hσ ht).2.2 hs
    have e := h (f + 2) (by unfold nLinkFam at hf; omega) _ (srcB4_lt hσ ht) s
      (lt_of_lt_of_le hs (NodeT.fbits_le f))
    rw [resNode4_src z hσ ht hs] at e
    exact sub_eq_zero.mp e

/-- **Some node residual table is nonzero** when the node's S truth fails. -/
theorem res_ne_node4 {z : ℕ → ℕ → F} (h : ¬ ShHoldsN4 ν z) :
    ∃ j < 10, ∃ u < 2 ^ nbC (.node ν), ∃ q < 2 ^ 10, resNode4 ν z j u q ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (shHoldsN4_of_res hc)

end Sum

/-! ## `SNode` at revision 4.1 -/

/-- **A node's S2 weight on the log** (S1's `τ`, `θ`, `κ_s`); `0` on a segment (`wS` reads the
segment's own). -/
def wN4 : CKind → Log → ℕ → ℕ → F
  | .node ν, es => wNode4 ν (ptOf (nbC (.node ν)) (tauL (.node ν) es)) (ptOf 10 (thL es)) (ksL es)
  | .seg _, _ => fun _ _ => 0

/-- The residual tables by kind. -/
def resN4 (zw : Wit) : CKind → Log → Log → ℕ → ℕ → ℕ → F
  | .node ν, L, es => resNode4 ν (zNodeC zw (.node ν) L es)
  | .seg _, _, _ => fun _ _ _ => 0

/-- **The weight's extension at S2's point** (`hNS` of `pendS4_pendBad4`, by definition). -/
def wNS4 (κ : CKind) (es : Log) : F :=
  ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC κ),
    eqAtR (ptOf (nbC κ) (rbL κ es)) y * eqAtR (ptOf 10 (rpL κ es)) q * wN4 κ es y q

theorem hNS4 {es : Log} : (kindOfC es).isNode = true → wNS4 (kindOfC es) es =
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
      eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
        eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * wN4 (kindOfC es) es y q := fun _ => rfl

/-- **A node's S2 weight reads S1's challenges only** (before 114). -/
theorem wNLocal4 : WNLocal wN4 := fun κ es es' h => by
  obtain ⟨h1, h2, h3⟩ := s1_congr4 h le_rfl κ
  cases κ with
  | node ν => simp only [wN4, h1, h2, h3]
  | seg σ => rfl

/-- **A node's S2 initial claim is `0`** (the boundary values are zeros). -/
theorem c0S_node4 {es : Log} (hn : (kindOfC es).isNode = true) : c0S es = 0 := by
  rw [c0S, pad18, shiftTargetS, shiftTargetAt, ptA_toArray, ptA_toArray, mle_digTbl, mle_digTbl]
  generalize kindOfC es = κ at hn ⊢
  have hb : (bndL κ es).length = 4 := by unfold bndL; split_ifs <;> rfl
  have hg : ∀ j < 4, (bndL κ es ++ endBits κ es).toArray.getD j 0 = (bndL κ es).getD j 0 :=
    fun j hj => by
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show j < (bndL κ es).length by omega)]
  rw [hg 0 (by norm_num), hg 1 (by norm_num), hg 2 (by norm_num), hg 3 (by norm_num)]
  simp only [bndL, hn, if_true, List.getD_cons_zero, List.getD_cons_succ, digBit_zero,
    Bool.false_eq_true, if_false, thS, mul_zero, sum_const_zero, add_zero]

section Inst
variable {zw : Wit} (hz : ZwSame zw)

theorem sum_wS_node {L es : Log} {ν : Rev4.NodeKind} (hν : kindOfC es = .node ν) :
    trueSum innerExpr (TS wN4 zw L es) (nrS (kindOfC es)) =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        wN4 (kindOfC es) es y q * zNodeC zw (kindOfC es) L es y q := by
  rw [sum_TS]
  refine sum_congr rfl fun q _ => sum_congr rfl fun y _ => ?_
  simp only [wS, hν, CKind.isNode, if_true]

include hz in
/-- **The node's S2 law** (P4c's `SNode`) at S-E12a's layout. -/
def sNode4 : SNode wN4 (truthSN4 zw) zw where
  nJ _ := 10
  res := resN4 zw
  nJ_pos _ := by norm_num
  nJ_le κ := by have := nbC_le κ; omega
  sum L es hn := by
    obtain ⟨ν, hν⟩ : ∃ ν, kindOfC es = .node ν := by
      cases h : kindOfC es with
      | seg σ => rw [h] at hn; cases hn
      | node ν => exact ⟨ν, rfl⟩
    rw [sum_wS_node hν, c0S_node4 hn, zero_add]
    have e := sh_sum_node4 (ν := ν) (ptOf (nbC (.node ν)) (tauL (.node ν) es)) (ptOf 10 (thL es))
      (ksL es) (zNodeC zw (.node ν) L es)
    rw [hν]
    exact e
  ne κ L es hn hS := by
    cases κ with
    | seg σ => cases hn
    | node ν => exact res_ne_node4 hS
  same κ L es L' es' p h hp := by
    cases κ with
    | seg σ => rfl
    | node ν => simp only [resN4, zNodeC_same hz h (by omega)]
  truth_same κ L es L' es' p h hp := by
    cases κ with
    | seg σ => exact Iff.rfl
    | node ν => simp only [truthSN4, zNodeC_same hz h hp]

end Inst

end FR.Snd.P4a
