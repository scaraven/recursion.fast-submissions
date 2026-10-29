-- New for `flock-recursive` (BLUEPRINT revision 3.13: A.8 `targetS` and `linkW` node forms, A.6
-- `WM`, §4.2 link families; stage-review changes 20, gap 3; track S-CN, the S-C part).
-- RET-3: the declarations revision 4 reads moved to `FRNodeTargetCore`.
import FRVerifierImplOps
import FRNodeLayout
import FRBlockKinds
import FRNodeTargetCore

/-!
# The node's public target on the skip set (`targetSNodeS`) and its link weights (`linkWS`)

**`targetS` of a node** (A.8, revision 3.13). The zerocheck's Z2 rebuilds `P^e(σ) = Σ_{x′} eq(r,
x′) E(x′, σ)` from the public target `E`. A node's `E` is block-dependent: **`nodeTgt blk`** is the
public target of node block `blk` (A.6 per region: the two digest chains, `hashStmt`'s A/B1/B2, the
WOTS runs with the key leaf and the path; `none` for the `free` blocks). It is S-G's
`Snd.nodeKind` (`FRSoundnessPIOP`) verbatim; this module does not import the soundness modules.
**`targetSNodeS`** is `FRPubTarget.targetS` with that `E` on the `8 + 16` variables of the quirky
point (the leaf's convention, `targetSLeafS`).

* **`targetSNode_blk`**: `P^e(σ) = Σ_hi eq(r_lo, hi) · G(σ + 64 hi)` with the block sum
  `G(p) = Σ_blk eq(r_blk, blk) · E(blk, p)` (`blkW`).
* **`targetS_node_eq`**: `G` in closed form (`Gc`): per region, the constant bits of a kind times a
  range sum of `eq(r_blk, ·)` (`streamStart`, the stream body with its counter removed, a chain's
  last block, `hashA`, `hashB1` with its three tags, `hashB2`, `w43` with `i`, `s` removed,
  `streamEnd41`); the stream counter `t_lo = 64 (k + 1)` as the bits of `k + 1` against `eq(r_blk,
  ·)` over the body (`tgtE_ctr`); `w43`'s `i = ⌊o/3⌋`, `s = o mod 3` as a 399-term sum
  (`tgtE_w43`).

**`linkW` of a node** (A.8, §4.2). Per slot, the link families tie an unaligned message field of a
source block to its aligned mirror cell in `WM`. A family (`Fam`) has `n` sources at blocks
`wb_σ + src t`, the field `[off, off + len)` of the message, and the mirror source `mir t` of the
`WM` map. **`linkWS`** is A.8's closed form `Σ_σ Σ_t eq(τ, src)·[eq(r_blk, src)·slotW(field, r_pos)
− eq(r_blk, mirBlk)·slotW(mirPos, r_pos)]` with `slotW(base) = Σ_{s<8 len} eq(θ, s) eq(r_pos, base +
s)`; **`linkW_mle`**: it is the multilinear extension, at `(τ, θ, r_blk, r_pos)`, of the
source-minus-mirror indicator `linkInd`; **`linkInd_apply`**: against a table `z`, the indicator
gives `Σ_σ Σ_t eq(τ, src) Σ_s eq(θ, s) (z(src, field s) − z(mirBlk, mirPos s))`, the family's
residual.

**Deviations from the blueprint's text** (the RESULT's D-1 … D-3; the counterexamples are there):
* **8 families, not 7.** End `2u+1` of the key leaf sits at byte `41` of block `u` and is 32 bytes
  long, so it crosses into block `u + 1` (`41 + 32 = 73 > 64`): A.8's `end41` (offset 41, 32 B) is
  split into `end41lo` (block `u`, bytes 41–63) and `end41hi` (block `u + 1`, bytes 0–8, mirror
  bits 184–255), `u < 66` (end 133 does not exist). `nLinkFam = 8` already.
* **The mirror cells sit in elements 0–7 of their `WM` block.** Sh's claim reads elements 0–7 of a
  block only (`FRVIRFinalsSG.shSrc`: three element coordinates, then four zeros; §2 step 4: 10
  collapse rounds over the positions `< 1024`), so A.6's map `WMbase_σ·128 + 2(off_f + t) + p`
  (elements up to 127 of a block) puts most mirror cells where no link family can read them. Here
  mirror source `g` of slot `σ` is block `wmB σ + ⌊g/4⌋`, elements `2(g mod 4)` and `2(g mod 4)+1`
  (positions `256 (g mod 4) + [0, 256)`), `wmB σ = wmBase + 146 σ` (581 sources, 146 blocks per
  slot; pinned by A.6 at revision 3.14, with `g = off_f + t`).
* `j`'s 400 sources are the 399 `w43` blocks and key-leaf block 0 (`src t = t`), one mirror.
-/

namespace FR
namespace NodeT
open Finset RecursionFast Impl Kinds Stream

/-! ## The node's public target -/

/-! ## The kinds' bits: counter and step fields split off -/

section Bits

end Bits

/-! ## The closed form of the block sum -/

section Closed
variable (rb : Fin 16 → F)

end Closed

section Proof

variable (rb : Fin 16 → F)

end Proof

/-! ## The link families (§4.2, A.8 `linkW`) -/

/-- **The source-minus-mirror indicator** of family `f`: at block point `u` (`τ`), field bit `s`
(`θ`), cell `(y, q)` (block, position): `1` at the source's field bit, `−1` at its mirror bit. -/
def linkInd (f u s y q : ℕ) : F :=
  ∑ σ ∈ range 2, ∑ t ∈ range (fam f).n,
    if u = srcB σ f t ∧ s < fbits f then
      (if y = srcB σ f t ∧ q = fpos f s then 1 else 0) -
        (if y = mirB σ f t ∧ q = mpos f t s then 1 else 0)
    else 0

section LinkProof

private theorem col {n a : ℕ} (h : a < n) (g : ℕ → F) :
    ∑ x ∈ range n, (if x = a then g x else 0) = g a := by
  rw [Finset.sum_ite_eq']; simp [h]

private theorem sum_lt {n L : ℕ} (h : L ≤ n) (g : ℕ → F) :
    ∑ x ∈ range n, (if x < L then g x else 0) = ∑ x ∈ range L, g x := by
  rw [← Finset.sum_range_add_sum_Ico _ h]
  rw [Finset.sum_eq_zero (s := Ico L n) fun x hx => by simp [(Finset.mem_Ico.1 hx).1]]
  rw [add_zero]
  exact Finset.sum_congr rfl fun x hx => by simp [Finset.mem_range.1 hx]

/-- Four nested sums and an inner one commute. -/
private theorem sum_pull {α : Type*} (S₁ S₂ S₃ S₄ : Finset ℕ) (T : Finset α)
    (g : ℕ → ℕ → ℕ → ℕ → α → F) :
    ∑ u ∈ S₁, ∑ s ∈ S₂, ∑ y ∈ S₃, ∑ q ∈ S₄, ∑ j ∈ T, g u s y q j =
      ∑ j ∈ T, ∑ u ∈ S₁, ∑ s ∈ S₂, ∑ y ∈ S₃, ∑ q ∈ S₄, g u s y q j := by
  calc _ = ∑ u ∈ S₁, ∑ s ∈ S₂, ∑ y ∈ S₃, ∑ j ∈ T, ∑ q ∈ S₄, g u s y q j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ u ∈ S₁, ∑ s ∈ S₂, ∑ j ∈ T, ∑ y ∈ S₃, ∑ q ∈ S₄, g u s y q j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ u ∈ S₁, ∑ j ∈ T, ∑ s ∈ S₂, ∑ y ∈ S₃, ∑ q ∈ S₄, g u s y q j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- One source's term of the indicator, summed against `A(u) B(s) Ψ(y, q)`. -/
private theorem one_source {a m L : ℕ} (fp mp : ℕ → ℕ) (ha : a < 2 ^ 16) (hm : m < 2 ^ 16)
    (hL : L ≤ 2 ^ 10) (hfp : ∀ s < L, fp s < 2 ^ 10) (hmp : ∀ s < L, mp s < 2 ^ 10)
    (A B : ℕ → F) (Ψ : ℕ → ℕ → F) :
    ∑ u ∈ range (2 ^ 16), ∑ s ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16), ∑ q ∈ range (2 ^ 10),
      A u * B s * Ψ y q * (if u = a ∧ s < L then
        (if y = a ∧ q = fp s then 1 else 0) - (if y = m ∧ q = mp s then 1 else 0) else 0) =
    A a * ∑ s ∈ range L, B s * (Ψ a (fp s) - Ψ m (mp s)) := by
  have hpt : ∀ u s y q, A u * B s * Ψ y q * (if u = a ∧ s < L then
      (if y = a ∧ q = fp s then (1 : F) else 0) - (if y = m ∧ q = mp s then 1 else 0) else 0) =
      (if u = a then A u else 0) * ((if s < L then B s else 0) *
        ((if y = a then 1 else 0) * (if q = fp s then Ψ y q else 0) -
          (if y = m then 1 else 0) * (if q = mp s then Ψ y q else 0))) := by
    intro u s y q
    rw [ite_and, ite_and, ite_and]
    split_ifs <;> ring
  simp only [hpt, ← Finset.mul_sum]
  rw [← Finset.sum_mul, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 ha)]
  refine congrArg (A a * ·) ?_
  simp only [ite_mul, zero_mul]
  rw [sum_lt hL]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.1 hs
  refine congrArg (B s * ·) ?_
  simp only [Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm (s := range (2 ^ 16)), Finset.sum_comm (s := range (2 ^ 16))]
  simp only [Finset.sum_ite_eq', Finset.mem_range, ha, hm, ite_true, hfp s hs', hmp s hs']

/-- **The indicator against any weights** (the family's residual): with `Ψ = z` the cells' values
this is `Σ_σ Σ_t A(src) Σ_s B(s) (z(src, field s) − z(mirBlk, mirPos s))`, zero when every field
equals its mirror. -/
theorem linkInd_sum (f : ℕ) (A B : ℕ → F) (Ψ : ℕ → ℕ → F) :
    ∑ u ∈ range (2 ^ 16), ∑ s ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16), ∑ q ∈ range (2 ^ 10),
      A u * B s * Ψ y q * linkInd f u s y q =
    ∑ σ ∈ range 2, ∑ t ∈ range (fam f).n, A (srcB σ f t) * ∑ s ∈ range (fbits f),
      B s * (Ψ (srcB σ f t) (fpos f s) - Ψ (mirB σ f t) (mpos f t s)) := by
  unfold linkInd
  simp only [Finset.mul_sum (s := range 2), Finset.mul_sum (s := range (fam f).n)]
  rw [sum_pull]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [sum_pull]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hσ' := Finset.mem_range.1 hσ
  have ht' := Finset.mem_range.1 ht
  have hb := fam_bounds (s := 0) hσ' ht'
  exact one_source (fpos f) (mpos f t) hb.1 hb.2.1 (fbits_le f)
    (fun s hs => ((fam_bounds hσ' ht').2.2 hs).1) (fun s hs => ((fam_bounds hσ' ht').2.2 hs).2)
    A B Ψ

/-- **`linkW_mle`** (A.8): `W_f` is the multilinear extension of the source-minus-mirror indicator
at `(τ, θ, r_blk, r_pos)` (`eqAtR r u = eq(r, cube u)`). -/
theorem linkW_mle (f : ℕ) (τ : Fin 16 → F) (θ : Fin 10 → F) (rb : Fin 16 → F) (rp : Fin 10 → F) :
    linkWS f τ θ rb rp =
      ∑ u ∈ range (2 ^ 16), ∑ s ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16), ∑ q ∈ range (2 ^ 10),
        eqAtR τ u * eqAtR θ s * (eqAtR rb y * eqAtR rp q) * linkInd f u s y q := by
  rw [linkInd_sum f (eqAtR τ) (eqAtR θ) (fun y q => eqAtR rb y * eqAtR rp q)]
  unfold linkWS slotWL
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun t _ => ?_
  refine congrArg (eqAtR τ (srcB σ f t) * ·) ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

end LinkProof

/-! ## Controls -/

section Controls

/-- At a Boolean block point the block sum reads the target: `G(p) = E(b, p)`. -/
theorem blkW_cube {b : ℕ} (hb : b < 2 ^ 16) (p : ℕ) : blkW (cubeN 16 b) p = nodeE b p := by
  unfold blkW
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_range.2 hb) fun x hx hne => by
    rw [eqAtR_cubeN hb (Finset.mem_range.1 hx), if_neg hne, zero_mul]]
  rw [eqAtR_cubeN hb hb, if_pos rfl, one_mul]

/-- (+) `one` on a chain block; the counter of chain block 1 is `t = 128` (bit 7 set). -/
theorem nodeBit_pos : nodeBit 0 1152 = true ∧ nodeBit 1 1031 = true ∧
    nodeBit Layout.stmtBase 1152 = true ∧ nodeBit (Layout.stmtBase + 1) 513 = true ∧
    nodeBit (Layout.wotsBase + 5) 584 = true ∧ nodeBit (Layout.wotsBase + 5) 593 = true := by
  decide

/-- (−) Wrong-offset and wrong-constant detection: chain block 1's bit 6 is clear (a counter
`64 k` would set it), `hashA`'s tag `0x4C` has bit 1 clear where `hashB1 tagNode`'s `0x4E` has it
set, `w43` step `(1, 2)` has `s`'s bit 0 clear, and `WM` is not pinned. -/
theorem nodeBit_neg : nodeBit 1 1030 = false ∧ nodeBit Layout.stmtBase 513 = false ∧
    nodeBit (Layout.wotsBase + 5) 592 = false ∧ nodeBit Layout.wmBase 1152 = false ∧
    nodeBit (2 * Layout.chainN - 1) 1088 = true ∧ nodeBit (2 * Layout.chainN - 2) 1088 = false := by
  decide

/-- (+/−) The closed form at a Boolean block point: chain block 1's counter bit 7 is read as `1`,
its bit 6 as `0`. -/
theorem Gc_controls : Gc (cubeN 16 1) 1031 = 1 ∧ Gc (cubeN 16 1) 1030 = 0 := by
  rw [← blkW_eq _ (by norm_num), ← blkW_eq _ (by norm_num), blkW_cube (by norm_num),
    blkW_cube (by norm_num), nodeE_bit, nodeE_bit, nodeBit_pos.2.1, nodeBit_neg.1]
  exact ⟨rfl, rfl⟩

/-- Family `x` at `τ` = its first source (slot 0, step 0). -/
theorem linkWS_x0 (θ : Fin 10 → F) (rb : Fin 16 → F) (rp : Fin 10 → F) :
    linkWS 0 (cubeN 16 (wb 0)) θ rb rp =
      eqAtR rb (wb 0) * slotWL (fpos 0) (fbits 0) θ rp -
        eqAtR rb (mirB 0 0 0) * slotWL (mpos 0 0) (fbits 0) θ rp := by
  have hw : ∀ σ, wb σ = 46298 + 498 * σ := fun σ => rfl
  have hn : (fam 0).n = 399 := rfl
  have hs : ∀ σ t, srcB σ 0 t = wb σ + t := fun _ _ => rfl
  have h0 : ∀ σ ∈ range 2, ∀ t ∈ range 399, (σ, t) ≠ (0, 0) →
      eqAtR (cubeN 16 (wb 0)) (srcB σ 0 t) = 0 := by
    intro σ hσ t ht hne
    have := Finset.mem_range.1 hσ
    have := Finset.mem_range.1 ht
    rw [eqAtR_cubeN (by rw [hw]; norm_num) (by rw [hs, hw]; omega), if_neg]
    rw [hs, hw, hw]
    intro h
    exact hne (by rw [Prod.mk.injEq]; omega)
  unfold linkWS
  rw [hn, Finset.sum_eq_single_of_mem 0 (by simp) fun σ hσ hne => Finset.sum_eq_zero fun t ht => by
    rw [h0 σ hσ t ht (by simp [hne]), zero_mul]]
  rw [Finset.sum_eq_single_of_mem 0 (by simp) fun t ht hne => by
    rw [h0 0 (by simp) t ht (by simp [hne]), zero_mul]]
  rw [eqAtR_cubeN (by rw [hw]; norm_num) (by rw [hs, hw]; norm_num), if_pos (by rw [hs]; rfl),
    one_mul]
  rfl

theorem bits0 : fbits 0 = 256 := rfl

/-- (+) Family `x`'s indicator: source block, field bit 0 at position 600 (byte 11). -/
theorem linkW_hit : linkWS 0 (cubeN 16 (wb 0)) (cubeN 10 0) (cubeN 16 (wb 0)) (cubeN 10 600) = 1 := by
  rw [linkWS_x0, bits0, slotWL_cube (by norm_num) (by norm_num) (fun s hs => by
      simp only [fpos, fam]; omega) (by norm_num),
    slotWL_cube (by norm_num) (by norm_num) (fun s hs => by simp only [mpos, fam, id]; omega)
      (by norm_num),
    eqAtR_cubeN (by simp [wb, Layout.wotsBase, Layout.stmtBase, Layout.chainN])
      (by simp [wb, Layout.wotsBase, Layout.stmtBase, Layout.chainN]),
    eqAtR_cubeN (by simp [wb, Layout.wotsBase, Layout.stmtBase, Layout.chainN])
      (by simp [mirB, wmB, fam, Layout.wmBase, Layout.wotsBase, Layout.stmtBase, Layout.chainN,
        Layout.wotsSlot])]
  simp [fpos, mpos, mirB, wmB, wb, fam, Layout.wmBase, Layout.wotsBase, Layout.stmtBase,
    Layout.chainN, Layout.wotsSlot]

/-- (−) A wrong offset (position 601 is the field's bit 1, not bit 0) reads `0`. -/
theorem linkW_off : linkWS 0 (cubeN 16 (wb 0)) (cubeN 10 0) (cubeN 16 (wb 0)) (cubeN 10 601) = 0 := by
  rw [linkWS_x0, bits0, slotWL_cube (by norm_num) (by norm_num) (fun s hs => by
      simp only [fpos, fam]; omega) (by norm_num),
    slotWL_cube (by norm_num) (by norm_num) (fun s hs => by simp only [mpos, fam, id]; omega)
      (by norm_num)]
  simp [fpos, mpos, fam]

/-- (+) The mirror side: its cell reads `−1`. -/
theorem linkW_mir : linkWS 0 (cubeN 16 (wb 0)) (cubeN 10 0) (cubeN 16 (mirB 0 0 0))
    (cubeN 10 (mpos 0 0 0)) = -1 := by
  have hm : mirB 0 0 0 = 47294 := rfl
  have hw : wb 0 = 46298 := rfl
  rw [linkWS_x0, bits0, slotWL_cube (by norm_num) (by norm_num) (fun s hs => by
      simp only [fpos, fam]; omega) (by simp [mpos, fam]),
    slotWL_cube (by norm_num) (by norm_num) (fun s hs => by simp only [mpos, fam, id]; omega)
      (by simp [mpos, fam]), hm, hw, eqAtR_cubeN (by norm_num) (by norm_num),
    eqAtR_cubeN (by norm_num) (by norm_num)]
  simp [fpos, mpos, fam]

end Controls

end NodeT
end FR
