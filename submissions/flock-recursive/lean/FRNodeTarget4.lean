-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8 `targetS`/`shiftMask`/`slotW`/`linkWAll`,
-- A.9 `finSh` on a node; stage S-CN4). 3.x templates: `FRNodeTarget` (`targetSNodeS`, `shiftMaskS`,
-- `linkWS`/`linkWAllS`).
import FRNodeKinds4

/-!
# The node's verifier ops at the revision 4.1 layout: specifications (`N2`/`N4`/`N8`)

`VnodeC implN` runs a node program under `implN κ`; four of its ops read the node's layout. Their
specifications at S-E12a's layout (`FRNodeKinds4`), `nb = m − 14` block coordinates (`nbN`: 17 for
`N2`, 18 for `N4`/`N8`):

* **`targetSNode4S ν r`** (Z2's `P^e`): 3.x's `targetSNodeS` over `8 + nb` variables with the block
  targets of `nodeLayout4 ν` (`nodeE4`: `NodeT.tgtE` of `nodeKind4`, `0` on `free`; the same bits as
  `N4c.etN4`). The operand is Z1's point: `zLo r`, then `r[1 … nb]`.
* **`shiftMask4S ν τ r`** (A.9 `finSh`'s chain-masked weights): over the chain mask `chainLk4`
  (both main chains, `chLen ν 0` and `chLen ν 1` blocks) `Σ [lk y] eq(τ,y) eq(r,y)`,
  `Σ [lk y] eq(τ,y) eq(r,y+1)`, and the two starts' weight `eq(r,0) + eq(r,chLen₀)` (ruling D10: the
  start term is kept). The operands are read at their first `nb` entries (`finSh` pads them to 18).
* **`slotW`**: unchanged. The node's chain blocks keep 3.x's slot map (`h_in` at positions
  `0 … 255`, slot map 2; `h_out` at `256 … 511`, slot map 0), so `Impl.slotWS` is the specification
  (`slotBase_node4`).
* **`linkWAll4S ν tt rr`**: the eight WOTS link families at `srcB4`/`mirB4` (3.x's `linkWS` rebased),
  on the packed points `tt = τ ‖ θ`, `rr = r_blk ‖ r_pos` (`nb + 10` entries each, `gShCore`'s).

Also the layout bounds the computed forms need (`chLen_facts`, `chainLk4_iff`, `srcB4_lt'`,
`mirB4_lt'`), proved from the interval list's numbers without the soundness modules.
-/

namespace FR
namespace NT4
open Finset RecursionFast Rev4 Impl

/-- **The node's block coordinates** `nb = m − 14`. -/
def nbN (ν : NodeKind) : ℕ := ν.m - 14

theorem nbN_eq : nbN .N2 = 17 ∧ nbN .N4 = 18 ∧ nbN .N8 = 18 := ⟨rfl, rfl, rfl⟩

theorem nbN_bounds (ν : NodeKind) : 9 ≤ nbN ν ∧ nbN ν ≤ 18 := by cases ν <;> decide

/-! ## `targetS` -/

/-- **`E(blk, p)`** of a revision 4.1 node: block `blk`'s public target bit at position `p` (`0` on a
`free` block). -/
def nodeE4 (ν : NodeKind) (blk p : ℕ) : F :=
  match N4c.nodeKind4 ν blk with
  | some tgt => NodeT.tgtE tgt p
  | none => 0

/-- The `nb` block coordinates of `targetS`'s operand (`r[1 … nb]`). -/
def rbOf4 (ν : NodeKind) (r : Array F) : Fin (nbN ν) → F := fun l => r.getD (1 + l) 0

/-- **The node's `targetS` specification** (`FRPubTarget.targetS` over `8 + nb` variables, the
position's 8 high bits low, the block high: `E(σ, (hi, blk)) = E(blk, σ + 64 hi)`). -/
def targetSNode4S (ν : NodeKind) (r : Array F) : Array F :=
  Array.ofFn (n := 64) fun σ => FR.targetS (ℓ := 8 + nbN ν) (Fin.append (zLo r) (rbOf4 ν r))
    (fun σ u => nodeE4 ν (u.val / 256) (σ + 64 * (u.val % 256))) σ

/-- `nodeE4` is `etN4`'s bit (the PIOP's node target, `zlm4`'s `etN`). -/
theorem nodeE4_etN4 (ν : NodeKind) (blk : ℕ) (p : Fin (2 ^ 14)) : nodeE4 ν blk p.val = N4c.etN4 ν blk p := by
  unfold nodeE4 N4c.etN4; cases N4c.nodeKind4 ν blk <;> rfl

/-! ## `shiftMask` -/

section Mask
variable (ν : NodeKind) {n : ℕ}

/-- `Σ_{y ∈ Lk} eq(τ, y) eq(r, y)` (the `Out` weight's block part). -/
def lkE (τ r : Fin n → F) : F :=
  ∑ y ∈ range (2 ^ n), if N4c.chainLk4 ν y then eqAtR τ y * eqAtR r y else 0

/-- `Σ_{y ∈ Lk} eq(τ, y) eq(r, y + 1)` (the `In` weight's linked part). -/
def lkSh (τ r : Fin n → F) : F :=
  ∑ y ∈ range (2 ^ n), if N4c.chainLk4 ν y then eqAtR τ y * eqAtR r (y + 1) else 0

/-- `eq(r, 0) + eq(r, chLen₀)` (the two chain starts). -/
def lkE0 (r : Fin n → F) : F := eqAtR r 0 + eqAtR r (N4c.chLen ν 0)

end Mask

/-- **The node's `shiftMask` specification** at the 4.1 chain mask (operands read at `nb` entries). -/
def shiftMask4S (ν : NodeKind) (τ r : Array F) : F × F × F :=
  (lkE ν (ptA (nbN ν) τ) (ptA (nbN ν) r), lkSh ν (ptA (nbN ν) τ) (ptA (nbN ν) r),
    lkE0 ν (ptA (nbN ν) r))

/-! ## `slotW` -/

/-- **The node's slot maps are 3.x's**: `w_out` reads `h_out` at `256 + σ` (map 0), `w_in` reads
`h_in` at `σ` (map 2), so `slotWS` specifies the node's `slotW` unchanged. -/
theorem slotBase_node4 : slotBase 0 = 256 ∧ slotBase 2 = 0 := ⟨rfl, rfl⟩

/-! ## `linkWAll` -/

/-- **Family `f`'s weight** (A.8; 3.x's `linkWS` at `srcB4`/`mirB4`): `Σ_σ Σ_t eq(τ, src) ·
(eq(r_blk, src) · slotW(field) − eq(r_blk, mirBlk) · slotW(mirPos))`. -/
def linkW4S (ν : NodeKind) (f : ℕ) {n : ℕ} (τ : Fin n → F) (θ : Fin 10 → F) (rb : Fin n → F)
    (rp : Fin 10 → F) : F :=
  ∑ σ ∈ range 2, ∑ t ∈ range (NodeT.fam f).n, eqAtR τ (N4c.srcB4 ν σ f t) *
    (eqAtR rb (N4c.srcB4 ν σ f t) * NodeT.slotWL (NodeT.fpos f) (NodeT.fbits f) θ rp -
      eqAtR rb (N4c.mirB4 ν σ f t) * NodeT.slotWL (NodeT.mpos f t) (NodeT.fbits f) θ rp)

/-- **The node's `linkWAll` specification** on the packed points `tt = τ ‖ θ`, `rr = r_blk ‖ r_pos`
(`nb`, then 10 entries). -/
def linkWAll4S (ν : NodeKind) (tt rr : Array F) : Array F :=
  Array.ofFn (n := nLinkFam) fun f => linkW4S ν f (ptA (nbN ν) tt) (fun l => tt.getD (nbN ν + l) 0)
    (ptA (nbN ν) rr) (fun l => rr.getD (nbN ν + l) 0)

/-! ## The layout's numbers -/

/-- The chains are nonempty and both fit below the node's top block, with the WOTS runs and their
mirrors (`hUsedN`). -/
theorem chLen_facts (ν : NodeKind) : 1 ≤ N4c.chLen ν 0 ∧ 1 ≤ N4c.chLen ν 1 ∧
    N4c.chLen ν 0 + N4c.chLen ν 1 ≤ N4c.wotsB ν 0 ∧ N4c.hUsedN ν < 2 ^ nbN ν := by
  cases ν <;> decide

/-- **The chain mask is two intervals**: `y` is linked iff `y < chLen₀ + chLen₁ − 1` and `y` is not
chain 0's last block. -/
theorem chainLk4_iff (ν : NodeKind) (y : ℕ) : N4c.chainLk4 ν y = true ↔
    y < N4c.chLen ν 0 + N4c.chLen ν 1 - 1 ∧ y ≠ N4c.chLen ν 0 - 1 := by
  have := chLen_facts ν
  simp only [N4c.chainLk4, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem fam_src_lt4 {f t : ℕ} (ht : t < (NodeT.fam f).n) : (NodeT.fam f).src t < 498 := by
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp only [NodeT.fam, id] at ht ⊢ <;> omega

theorem fam_mir_lt4 {f t : ℕ} (ht : t < (NodeT.fam f).n) : (NodeT.fam f).mir t < 581 := by
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp only [NodeT.fam, id] at ht ⊢ <;> omega

theorem wotsB_hUsed (ν : NodeKind) {σ : ℕ} (hσ : σ < 2) :
    N4c.wotsB ν σ + 498 ≤ N4c.wmB ν 0 ∧ N4c.wmB ν σ + 146 ≤ N4c.hUsedN ν := by
  have h2 : 2 ≤ ν.vslots := by cases ν <;> decide
  simp only [N4c.wotsB, N4c.wmB, N4c.hUsedN, wotsSlot4, wmSlot4]
  constructor <;> nlinarith

/-- Every source block is below the node's top block. -/
theorem srcB4_lt' (ν : NodeKind) {σ f t : ℕ} (hσ : σ < 2) (ht : t < (NodeT.fam f).n) :
    N4c.srcB4 ν σ f t < 2 ^ nbN ν := by
  have := fam_src_lt4 ht; have := wotsB_hUsed ν hσ; have := wotsB_hUsed ν (σ := 0) (by norm_num)
  have := (chLen_facts ν).2.2.2
  unfold N4c.srcB4; omega

/-- Every mirror block is below the node's top block. -/
theorem mirB4_lt' (ν : NodeKind) {σ f t : ℕ} (hσ : σ < 2) (ht : t < (NodeT.fam f).n) :
    N4c.mirB4 ν σ f t < 2 ^ nbN ν := by
  have := fam_mir_lt4 ht; have := wotsB_hUsed ν hσ; have := (chLen_facts ν).2.2.2
  unfold N4c.mirB4; omega

/-! ## Controls -/

/-- (+) Chain 0's first link and chain 1's last link are masked in; (−) chain 0's last block is not
linked to chain 1's start, nor is chain 1's last block linked onward. -/
theorem chainLk4_ctrl : N4c.chainLk4 .N4 0 = true ∧
    N4c.chainLk4 .N4 (N4c.chLen .N4 0 + N4c.chLen .N4 1 - 2) = true ∧
    N4c.chainLk4 .N4 (N4c.chLen .N4 0 - 1) = false ∧
    N4c.chainLk4 .N4 (N4c.chLen .N4 0 + N4c.chLen .N4 1 - 1) = false := by
  decide

end NT4
end FR
