-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2, A.6, A.8 `linkW`; stage S-E13b, track
-- L-circ). 3.x: `FRWots.wots_sound`, `w43_step`, `path_node`.
import FRNodeRows4WotsB
import FRWots
import FRNodeCircuit4Dig

/-!
# The WOTS run of a 4.1 node: blocks, link families, mux rows

What signed child `σ`'s WOTS blocks compute, read through the link families of `truthS4` and the
rows of `FRNodeRows4Wots`:

* **`fam_byte`**: a link family's source bytes are its mirror's (`truthS4`'s second conjunct, bit
  by bit);
* **`nodeKind4_wots`**: WOTS block `o` carries 3.x's target `NodeT.wotsTgt o`;
* **`step_out`**: chain `i`'s step `s` outputs `wotsStep idx i s x` with `x` its `x` mirror and
  `idx` the signature's index (its `j` bytes are the `j` mirror, which the index row ties to `idx`).
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block ProductCircuit Blake2sCircuit Kinds

/-! ## Mirrors -/

/-- **Mirror source `g`'s digest** (its two elements). -/
noncomputable def md (κ : NodeKind) (σ g : ℕ) (w : Asg) : Digest := Read.digestOf w (mc κ σ g 0) (mc κ σ g 1)

theorem md_get (κ : NodeKind) (σ g : ℕ) (w : Asg) {i : ℕ} (hi : i < 32) :
    (md κ σ g w)[i] = fb (w (mc κ σ g (i / 16))) (i % 16) := by
  rw [md, digestOf_eq, Vector.getElem_ofFn]
  by_cases h : i < 16
  · simp [h, Nat.div_eq_of_lt h]
  · simp [h, show i / 16 = 1 by omega]

theorem bitN_mod (a : F) (n : ℕ) : bitN a n = bitN a (n % 128) := by
  unfold bitN; simp

/-- **A link family's bytes** (A.8 `linkW`, `truthS4`): byte `k` of family `f`'s field in source
`t`'s block is byte `mbo/8 + k` of its mirror. -/
theorem fam_byte {κ : NodeKind} {w : Asg} (hS : truthS4 κ w) {σ f t k : ℕ} (hσ : σ < 2)
    (hf : f < nLinkFam) (ht : t < (NodeT.fam f).n) (hk : k < (NodeT.fam f).len)
    (ho : (NodeT.fam f).off + (NodeT.fam f).len ≤ 64) (hb : (NodeT.fam f).mbo % 8 = 0)
    (hb' : (NodeT.fam f).mbo / 8 + (NodeT.fam f).len ≤ 32) :
    (Block.msgBytes (bitsB4 w (wb κ σ ((NodeT.fam f).src t)))).getD ((NodeT.fam f).off + k) 0 =
      fb (w (mc κ σ ((NodeT.fam f).mir t) (((NodeT.fam f).mbo / 8 + k) / 16))) (((NodeT.fam f).mbo / 8 + k) % 16) := by
  rw [msgByte_hc _ _ (by omega)]
  refine fb_congr (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) fun j hj => ?_
  have hs : 8 * k + j < NodeT.fbits f := by unfold NodeT.fbits; omega
  have hl := hS.2 f hf σ hσ t ht (8 * k + j) hs
  have hm4 := Nat.mod_lt ((NodeT.fam f).mir t) (show 0 < 4 by norm_num)
  have h1 : NodeT.fpos f (8 * k + j) < 2 ^ 14 := by unfold NodeT.fpos; omega
  have h2 : NodeT.mpos f t (8 * k + j) < 2 ^ 14 := by unfold NodeT.mpos; omega
  have hb2 := bit_of_zN4 h1 h2 hl
  have e1 : srcB4 κ σ f t * 128 + NodeT.fpos f (8 * k + j) / 128 =
      hc (wb κ σ ((NodeT.fam f).src t)) (4 + ((NodeT.fam f).off + k) / 16) := by
    unfold srcB4 wb hc NodeT.fpos; omega
  have e2 : mirB4 κ σ f t * 128 + NodeT.mpos f t (8 * k + j) / 128 =
      mc κ σ ((NodeT.fam f).mir t) (((NodeT.fam f).mbo / 8 + k) / 16) := by
    unfold mirB4 mc NodeT.mpos; omega
  rw [e1, e2, bitN_mod, bitN_mod _ (NodeT.mpos f t _)] at hb2
  rw [bitN_mod, bitN_mod (w (mc _ _ _ _))]
  convert hb2 using 2
  · unfold NodeT.fpos; omega
  · unfold NodeT.mpos; omega

/-! ## The WOTS blocks' targets -/

/-- **WOTS block `o` of signed child `σ` carries `NodeT.wotsTgt o`.** -/
theorem nodeKind4_wots (κ : NodeKind) {σ o : ℕ} (hσ : σ < 2) (ho : o < wotsSlot4) :
    wb κ σ o < κ.blocks ∧ nodeKind4 κ (wb κ σ o) = some (NodeT.wotsTgt o) := by
  obtain ⟨iv, hm, hk⟩ := contig_cover wots0_contig (Layout.wotsBase + o) (by omega) (by omega)
  simp only [wots0, List.mem_map] at hm
  obtain ⟨iv₀, h₀, rfl⟩ := hm
  simp only [TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hk
  have hw : Layout.wotsBase ≤ iv₀.lo := by
    simp only [Layout.wotsIvs, Layout.wotsSlot, mul_zero, add_zero, List.mem_append, List.mem_cons,
      List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false] at h₀
    rcases h₀ with (rfl | rfl | rfl | rfl) | ⟨t, ht, rfl | rfl⟩ <;> simp <;> omega
  have hmem : (⟨iv₀.kind, iv₀.lo - Layout.wotsBase + wotsB κ σ, iv₀.hi - Layout.wotsBase + wotsB κ σ,
      fun o => some (NodeT.wotsTgt (iv₀.lo - Layout.wotsBase + o))⟩ : TIv) ∈ nodeLayout4 κ := by
    have : _ ∈ wotsIvs κ σ := List.mem_map.2 ⟨iv₀, h₀, rfl⟩
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> simp [nodeLayout4, this]
  have hk' : TIv.mem ⟨iv₀.kind, iv₀.lo - Layout.wotsBase + wotsB κ σ, iv₀.hi - Layout.wotsBase + wotsB κ σ,
      fun o => some (NodeT.wotsTgt (iv₀.lo - Layout.wotsBase + o))⟩ (wb κ σ o) = true := by
    show TIv.mem _ (wotsB κ σ + o) = true
    simp [TIv.mem]; omega
  refine ⟨mem_lt hmem hk', ?_⟩
  rw [tgt_of_mem hmem hk']
  simp only [wb]
  congr 2; omega

/-- WOTS block `o`'s Z truth. -/
theorem holds_wots {κ : NodeKind} {w : Asg} (hZ : truthZ4 κ w) {σ o : ℕ} (hσ : σ < 2) (ho : o < wotsSlot4) :
    HoldsE (blockR1CS (NodeT.wotsTgt o)) (targetVal F (NodeT.wotsTgt o)) (liftBlock F (bitsB4 w (wb κ σ o))) :=
  holds_of_Z hZ (nodeKind4_wots κ hσ ho).1 (nodeKind4_wots κ hσ ho).2

/-! ## Lists byte by byte -/

theorem take_eq_of_getD {l r : List UInt8} {n : ℕ} (hl : n ≤ l.length) (hr : r.length = n)
    (h : ∀ p < n, l.getD p 0 = r.getD p 0) : l.take n = r := by
  refine List.ext_getElem (by simp [hr, hl]) fun p h1 h2 => ?_
  have := h p (by simp at h1; omega)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : p < l.length),
    List.getElem?_eq_getElem h2, Option.getD_some] at this
  simpa using this

theorem msgBytes_len (W : Pos → Bool) : (Block.msgBytes W).length = 64 := by simp [Block.msgBytes]

/-! ## The index -/

/-- **The signature's index** (`readSig4`'s `idx`). -/
def idxOf (κ : NodeKind) (σ : ℕ) (w : Asg) : ℕ := (w (Lc κ σ 0)).c₀.val.toNat

/-- `enc64 idx` is the index element's first eight bytes. -/
theorem enc64_idx (κ : NodeKind) (σ : ℕ) (w : Asg) {k : ℕ} (hk : k < 8) :
    (enc64 (idxOf κ σ w)).getD k 0 = fb (w (Lc κ σ 0)) k := by
  have h := congrArg (fun l => l.getD k 0) (B64.toBytes_toList (w (Lc κ σ 0)).c₀)
  rw [idxOf, Snd.enc64_toListLE, ← h]
  simp only [fb, Nat.mod_eq_of_lt (show k < 16 by omega), F.toBytes, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList]
  rw [Vector.getElem_append_left (by simpa using hk)]
  simp [hk]

/-- **The `j` family**: bytes `1 … 8` of a step block or the key leaf's first block are `enc64
idx`, given the index row `mc 399 0 = idx`. -/
theorem j_byte {κ : NodeKind} {w : Asg} (hS : truthS4 κ w) {σ t k : ℕ} (hσ : σ < 2) (ht : t < 400)
    (hk : k < 8) (hj : w (mc κ σ 399 0) = w (Lc κ σ 0)) :
    (Block.msgBytes (bitsB4 w (wb κ σ t))).getD (1 + k) 0 = (enc64 (idxOf κ σ w)).getD k 0 := by
  have := fam_byte (f := 1) hS hσ (by decide) (t := t) (by simpa [NodeT.fam] using ht) (k := k)
    (by simpa [NodeT.fam] using hk) (by decide) (by decide) (by decide)
  simp only [NodeT.fam, id, Nat.zero_div, Nat.zero_add] at this
  rw [this, enc64_idx _ _ _ hk, Nat.div_eq_of_lt (show k < 16 by omega),
    Nat.mod_eq_of_lt (show k < 16 by omega), hj]

/-! ## A chain step -/

/-- **Chain `i`'s step `s` outputs `wotsStep idx i s x`**, `x` its `x` mirror. -/
theorem step_out {κ : NodeKind} {w : Asg} (hZ : truthZ4 κ w) (hS : truthS4 κ w) {σ i s : ℕ} (hσ : σ < 2)
    (hi : i < wotsLen) (hs : s < 3) (hj : w (mc κ σ 399 0) = w (Lc κ σ 0)) :
    Block.readDigest (bitsB4 w (wb κ σ (3 * i + s))) 256 = wotsStep (idxOf κ σ w) i s (md κ σ (3 * i + s) w) := by
  have hw : wotsLen = 133 := rfl
  have hh := holds_wots hZ hσ (o := 3 * i + s) (by unfold wotsSlot4; omega)
  have ht : NodeT.wotsTgt (3 * i + s) = (w43 i.toUInt8 s.toUInt8).target := by
    rw [NodeT.wotsTgt, if_pos (by omega), show (3 * i + s) / 3 = i by omega, show (3 * i + s) % 3 = s by omega]
  rw [ht] at hh
  refine Wots.w43_step hh (take_eq_of_getD (by rw [msgBytes_len]; omega) (by simp [enc64]) fun p hp => ?_)
  rcases (by omega : p = 0 ∨ (1 ≤ p ∧ p < 9) ∨ p = 9 ∨ p = 10 ∨ (11 ≤ p ∧ p < 43)) with
    rfl | ⟨h1, h2⟩ | rfl | rfl | ⟨h1, h2⟩
  · rw [msgBytes_getD _ (by norm_num), (w43 _ _).msgByte_eq (p := 0) (by norm_num) (u := tagWots)
      (by simp [w43]) hh]; rfl
  · obtain ⟨k, rfl⟩ : ∃ k, p = 1 + k := ⟨p - 1, by omega⟩
    rw [j_byte hS hσ (by omega) (by omega) hj]
    simp only [List.cons_append, List.getD_cons_succ, List.append_assoc]
    rw [show (1 + k) = k + 1 by omega, List.getD_cons_succ, List.getD_append _ _ _ _ (by simp [enc64]; omega)]
  · rw [msgBytes_getD _ (by norm_num), (w43 _ _).msgByte_eq (p := 9) (by norm_num) (u := i.toUInt8)
      (by simp [w43]) hh]; rfl
  · rw [msgBytes_getD _ (by norm_num), (w43 _ _).msgByte_eq (p := 10) (by norm_num) (u := s.toUInt8)
      (by simp [w43]) hh]; rfl
  · obtain ⟨k, rfl⟩ : ∃ k, p = 11 + k := ⟨p - 11, by omega⟩
    have := fam_byte (f := 0) hS hσ (by decide) (t := 3 * i + s) (by simp [NodeT.fam]; omega) (k := k)
      (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
    simp only [NodeT.fam, id, Nat.zero_div, Nat.zero_add] at this
    rw [this, ← md_get _ _ _ _ (show k < 32 by omega)]
    simp only [List.cons_append, List.append_assoc]
    rw [show 11 + k = (10 + k) + 1 by omega, List.getD_cons_succ,
      List.getD_append_right _ _ _ _ (by simp [enc64]; omega)]
    simp only [enc64_length, List.length_cons, List.length_nil, List.getD_eq_getElem?_getD]
    rw [show 10 + k - 8 = k + 2 by omega]
    simp [Vector.getElem?_toList, show k < 32 by omega]

end W4
end FR
