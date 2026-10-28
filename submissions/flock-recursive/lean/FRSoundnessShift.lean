-- New for `flock-recursive` (BLUEPRINT §4.2, A.10 S1/S2, revision 3.14; stage INT-3 for S-G).
import FRSoundnessPIOP
import FRNodeTarget
import FRShift

/-!
# The node's S truth: the chain-masked links and the 8 link families (revision 3.14)

* **`ShHoldsN z`** (A.10 S1's `ShHolds` for a node, the `WM` ruling): on a table `z blk p`
  (block, position):
  - the **chain part** `ChainPartN`: inside each of the two digest chains `[0, N)`, `[N, 2N)`
    (`N = chainN`), block `y + 1`'s `h_in` (positions `0 … 255`) is block `y`'s `h_out`
    (`256 … 511`), and the two chains' first `h_in` agree (the start term `κ_s(eq(0,·) +
    eq(N,·))` against `κ_s(h̃0 + h̃0) = 0`; the value `h0` itself is `streamStart`'s pin, a Z truth);
  - the **family part** `FamPartN`: each of the 8 families' source fields equals its mirror
    bits (A.6's `WM` map, `FRNodeTarget.fam`/`srcB`/`mirB`/`fpos`/`mpos`).
* **`truthS1N κ L es`**: `ShHoldsN` on the decoded word's bits (`zW`).
* **`chainPartN_iff`**: the chain part is `FRShift.ChainLinksM` with the node's mask `lkN`
  (`NodeT.chainLk`'s blocks), starts `{0, N}`, `Out = h_out`, `In = h_in`, `sV = 0`; so
  **`shift_sound_masked`** applies to it.
* **`sh_reads_chain_only`**: the chain part reads no block `≥ 2·chainN = 46,292`;
  **`fam_blocks_ge`**: every family source and mirror block is `≥ 2·chainN` (WOTS and `WM`), so
  the two parts read disjoint blocks, and a `WM` block is read only at its mirror positions.
* Controls: `shHoldsN_zero` (+), `not_chainPartN_one` (−), `chainPartN_ignores_wm` (a `WM` block's
  `h_in` is not read by the chain part).
-/

namespace FR.Snd
open RecursionFast Finset FR.NodeT

/-- **The node's in-chain successor relation**: `y + 1` is in `y`'s digest chain. -/
def chainLk (y : ℕ) : Prop :=
  y + 1 < Layout.chainN ∨ (Layout.chainN ≤ y ∧ y + 1 < 2 * Layout.chainN)

instance : DecidablePred chainLk := fun _ => by unfold chainLk; infer_instance

/-- **The chain part** of the node's `ShHolds`. -/
def ChainPartN (z : ℕ → ℕ → F) : Prop :=
  (∀ y, chainLk y → ∀ j < 256, z (y + 1) j = z y (256 + j)) ∧
    ∀ j < 256, z 0 j = z Layout.chainN j

/-- **The family part**: every source field bit equals its mirror bit. -/
def FamPartN (z : ℕ → ℕ → F) : Prop :=
  ∀ f < nLinkFam, ∀ σ < 2, ∀ t < (fam f).n, ∀ s < fbits f,
    z (srcB σ f t) (fpos f s) = z (mirB σ f t) (mpos f t s)

/-- **A.10 S1's `ShHolds` for a node** (revision 3.14): the chain-masked links and the 8 families. -/
def ShHoldsN (z : ℕ → ℕ → F) : Prop := ChainPartN z ∧ FamPartN z

/-- The decoded word's bits by block and position. -/
noncomputable def zNode (κ : Kind) (L es : Log) (blk p : ℕ) : F := zW κ L es (blk * 2 ^ 14 + p)

/-- **The node's S1 truth** (A.10 S1, revision 3.14). -/
def truthS1N (κ : Kind) (L es : Log) : Prop := ShHoldsN (zNode κ L es)

/-! ## The chain part is `FRShift`'s masked links -/

/-- The mask on `Fin (2^16)`. -/
def lkN (y : Fin (2 ^ 16)) : Prop := chainLk y.val

instance : DecidablePred lkN := fun _ => by unfold lkN; infer_instance

/-- The starts `{0, N}`. -/
def stN : Finset (Fin (2 ^ 16)) := {⟨0, by norm_num⟩, ⟨Layout.chainN, by simp [Layout.chainN]⟩}

/-- `h_out` and `h_in` as `FRShift`'s tables (slot `σ < 256` low, block high). -/
def outN (z : ℕ → ℕ → F) (w : Fin (2 ^ (8 + 16))) : F := z (w.val / 256) (256 + w.val % 256)
def inN (z : ℕ → ℕ → F) (w : Fin (2 ^ (8 + 16))) : F := z (w.val / 256) (w.val % 256)

theorem lkN_succ (y : Fin (2 ^ 16)) (h : lkN y) : y.val + 1 < 2 ^ 16 := by
  unfold lkN chainLk Layout.chainN at h; omega

private theorem join_div (σ : Fin (2 ^ 8)) (y : ℕ) (hy : y < 2 ^ 16) :
    (join σ (⟨y, hy⟩ : Fin (2 ^ 16))).val / 256 = y ∧
      (join σ (⟨y, hy⟩ : Fin (2 ^ 16))).val % 256 = σ.val := by
  simp only [join]; have := σ.isLt; constructor <;> omega

/-- **The chain part is the masked links** (`ChainLinksM`, `sV = 0`). -/
theorem chainPartN_iff (z : ℕ → ℕ → F) :
    ChainPartN z ↔ ChainLinksM lkN stN (outN z) (inN z) (fun _ => (0 : F)) := by
  have hst : (⟨0, by norm_num⟩ : Fin (2 ^ 16)) ∉ ({⟨Layout.chainN, by simp [Layout.chainN]⟩} :
      Finset (Fin (2 ^ 16))) := by simp [Fin.ext_iff, Layout.chainN]
  unfold ChainPartN ChainLinksM stN
  simp only [Finset.sum_insert hst, Finset.sum_singleton, add_zero]
  constructor
  · rintro ⟨hl, hs⟩
    refine ⟨fun σ y h hy => ?_, fun σ => ?_⟩
    · obtain ⟨a1, b1⟩ := join_div σ (y.val + 1) h
      obtain ⟨a2, b2⟩ := join_div σ y.val y.isLt
      simp only [inN, outN, a1, b1]
      rw [show join σ y = join σ ⟨y.val, y.isLt⟩ from rfl, a2, b2]
      exact hl y.val hy σ.val σ.isLt
    · obtain ⟨a1, b1⟩ := join_div σ 0 (by norm_num)
      obtain ⟨a2, b2⟩ := join_div σ Layout.chainN (by simp [Layout.chainN])
      simp only [inN, a1, b1, a2, b2, hs σ.val σ.isLt, CharTwo.add_self_eq_zero]
  · rintro ⟨hl, hs⟩
    refine ⟨fun y hy j hj => ?_, fun j hj => ?_⟩
    · have hy' : y < 2 ^ 16 := by unfold chainLk Layout.chainN at hy; omega
      have := hl ⟨j, by norm_num; omega⟩ ⟨y, hy'⟩ (lkN_succ ⟨y, hy'⟩ hy) hy
      obtain ⟨a1, b1⟩ := join_div ⟨j, by norm_num; omega⟩ (y + 1) (lkN_succ ⟨y, hy'⟩ hy)
      obtain ⟨a2, b2⟩ := join_div ⟨j, by norm_num; omega⟩ y hy'
      simpa only [inN, outN, a1, b1, a2, b2] using this
    · have := hs ⟨j, by norm_num; omega⟩
      obtain ⟨a1, b1⟩ := join_div ⟨j, by norm_num; omega⟩ 0 (by norm_num)
      obtain ⟨a2, b2⟩ := join_div ⟨j, by norm_num; omega⟩ Layout.chainN (by simp [Layout.chainN])
      simp only [inN, a1, b1, a2, b2] at this
      exact CharTwo.add_eq_zero.mp this

/-- **Broken node links leave a nonzero masked residual** (`shift_sound_masked` at the node). -/
theorem shift_sound_node {z : ℕ → ℕ → F} (h : ¬ChainPartN z) :
    chainDM lkN (outN z) (inN z) ≠ 0 ∨ chainD0M stN (inN z) (fun _ => (0 : F)) ≠ 0 :=
  shift_sound_masked lkN stN lkN_succ (by rwa [chainPartN_iff] at h)

/-! ## What the truth reads -/

/-- **`sh_reads_chain_only`**: the chain part of the node's S truth reads no block `≥ 2·chainN`
(46,292: `hashStmt`, WOTS, `WM`, L, M). -/
theorem sh_reads_chain_only {z z' : ℕ → ℕ → F}
    (h : ∀ blk < 2 * Layout.chainN, ∀ p, z blk p = z' blk p) : ChainPartN z ↔ ChainPartN z' := by
  have hN : (0 : ℕ) < Layout.chainN := by simp [Layout.chainN]
  have hy : ∀ y, chainLk y → y < 2 * Layout.chainN ∧ y + 1 < 2 * Layout.chainN := fun y hy => by
    unfold chainLk at hy; omega
  unfold ChainPartN
  constructor <;> rintro ⟨hl, hs⟩ <;> refine ⟨fun y hl' j hj => ?_, fun j hj => ?_⟩
  · rw [← h _ (hy y hl').2, ← h _ (hy y hl').1]; exact hl y hl' j hj
  · rw [← h 0 (by omega), ← h _ (by omega)]; exact hs j hj
  · rw [h _ (hy y hl').2, h _ (hy y hl').1]; exact hl y hl' j hj
  · rw [h 0 (by omega), h _ (by omega)]; exact hs j hj

/-- **Every family source and mirror block lies past the chains** (WOTS blocks from
`wotsBase = 2·chainN + 6`, mirrors from `wmBase`), so the two parts read disjoint blocks. -/
theorem fam_blocks_ge {f σ t : ℕ} (hf : f < nLinkFam) (hσ : σ < 2) (ht : t < (fam f).n) :
    2 * Layout.chainN ≤ srcB σ f t ∧ Layout.wmBase ≤ mirB σ f t := by
  have _ := hf; have _ := ht; have _ := hσ
  unfold srcB mirB wmB wb
  simp only [Layout.wmBase, Layout.wotsBase, Layout.wotsSlot, Layout.stmtBase]
  omega

/-! ## Controls -/

/-- (+) The zero table satisfies the node's S truth. -/
theorem shHoldsN_zero : ShHoldsN (fun _ _ => (0 : F)) :=
  ⟨⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩, fun _ _ _ _ _ _ _ _ => rfl⟩

/-- (−) A table whose block 1 `h_in` bit 0 is `1` and every other entry `0` breaks the chain part
(block 0 links to block 1). -/
theorem not_chainPartN_one :
    ¬ChainPartN (fun blk p => if blk = 1 ∧ p = 0 then (1 : F) else 0) := by
  rintro ⟨hl, -⟩
  have := hl 0 (Or.inl (by simp [Layout.chainN])) 0 (by norm_num)
  simp at this

/-- (+) The chain part ignores a `WM` block's `h_in`/`h_out` positions (the `WM` ruling: the mirrors
may use positions `0 … 1023` of `free` blocks). -/
theorem chainPartN_ignores_wm (z : ℕ → ℕ → F) (q : F) :
    ChainPartN z ↔ ChainPartN (fun blk p => if blk = Layout.wmBase then q else z blk p) :=
  sh_reads_chain_only fun blk hb p => by
    have hne : blk ≠ Layout.wmBase := by
      simp only [Layout.wmBase, Layout.wotsBase, Layout.wotsSlot, Layout.stmtBase] at hb ⊢; omega
    simp only [hne, if_false]

end FR.Snd
