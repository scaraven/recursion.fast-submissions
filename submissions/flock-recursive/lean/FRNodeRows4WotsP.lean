-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2; stage S-E13b, track L-circ). 3.x:
-- `FRWots.path_node`, `sigRoot_bits`.
import FRNodeRows4WotsL

/-!
# The WOTS path and the index of a 4.1 node

* **`idx_lt`/`idx_bit`**: the index rows make `idx < 2^16` and its bit `t` the index bit cell `t`;
* **`r31_byte`**: the byte-31 rows put `r`'s byte 31 (bits 120–127 of its element 1) into the `r31`
  mirror's byte 0;
* **`path_out`**: level `t`'s blocks output `sigNode l r` with `(l, r) = (cur, sib)` or
  `(sib, cur)` by the index bit;
* **`root_vk`**: the last level's output is `vk` (the root rows and `PubCells4`).
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block ProductCircuit Blake2sCircuit Kinds Stream

/-! ## The index -/

theorem idx_bitF {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hix : ∀ r ∈ idxRows κ σ, r.Holds w) (j : Fin 128) :
    bitF (w (Lc κ σ 0)) j = decide (j.val < 16 ∧ w (ixC κ σ j.val) = 1) := by
  have hb : ∀ t < 16, w (ixC κ σ t) = 0 ∨ w (ixC κ σ t) = 1 := fun t ht =>
    boolR_val hone (hix _ (List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩)))
  have he := eqR_val hone (hix _ (List.mem_append_right _ (List.mem_cons_self ..)))
  rw [Lin.ev_cell] at he
  rw [he, bitF_pk w _ (by norm_num) hb]

theorem idx_testBit {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hix : ∀ r ∈ idxRows κ σ, r.Holds w) (t : ℕ) :
    (idxOf κ σ w).testBit t = decide (t < 16 ∧ w (ixC κ σ t) = 1) := by
  unfold idxOf
  show (w (Lc κ σ 0)).c₀.val.toBitVec.toNat.testBit t = _
  rw [BitVec.testBit_toNat]
  by_cases ht : t < 64
  · have := idx_bitF hone hix ⟨t, by omega⟩
    simp only [bitF, ht, if_true] at this
    exact this
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    simp; omega

/-- **The index is below `2^16`.** -/
theorem idx_lt {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hix : ∀ r ∈ idxRows κ σ, r.Holds w) : idxOf κ σ w < 2 ^ sigHeight :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [idx_testBit hone hix]; simp only [show sigHeight = 16 from rfl] at hi; simp; omega

/-- **Its bit `t`** is the index bit cell `t`. -/
theorem idx_bit {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hix : ∀ r ∈ idxRows κ σ, r.Holds w) {t : ℕ} (ht : t < 16) :
    (idxOf κ σ w / 2 ^ t % 2 = 0 ↔ w (ixC κ σ t) ≠ 1) := by
  have := idx_testBit hone hix t
  rw [Nat.testBit_eq_decide_div_mod_eq] at this
  constructor
  · intro h h1; simp [h, ht, h1] at this
  · intro h; have := (Nat.mod_two_eq_zero_or_one (idxOf κ σ w / 2 ^ t)); simp_all

/-- The `j` mirror is the index (the index rows). -/
theorem j_mirror {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hix : ∀ r ∈ idxRows κ σ, r.Holds w) : w (mc κ σ 399 0) = w (Lc κ σ 0) := by
  have := eqR_val hone (hix _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  simpa using this

/-! ## Lists of bytes -/

theorem list_ext_getD {l r : List UInt8} (h : l.length = r.length) (hg : ∀ p < l.length, l.getD p 0 = r.getD p 0) :
    l = r := by
  refine List.ext_getElem h fun p h1 h2 => ?_
  have := hg p h1
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

/-! ## A path level -/

/-- `cur_t`'s digest. -/
noncomputable def curD (κ : NodeKind) (σ : ℕ) (w : Asg) (t : ℕ) : Digest :=
  Read.digestOf w (hc (curB κ σ t) 2) (hc (curB κ σ t) 3)

/-- The sibling `t`'s digest. -/
noncomputable def sibD (κ : NodeKind) (σ : ℕ) (w : Asg) (t : ℕ) : Digest := Read.digestOf w (sibC κ σ t 0) (sibC κ σ t 1)

theorem pathRows_mem {κ : NodeKind} {σ t : ℕ} (ht : t < sigHeight) {r : Row} (h : r ∈ pathRowsT κ σ t) :
    r ∈ pathRows κ σ := List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, h⟩

/-- **Byte 31 of `r`** reaches the `r31` mirror. -/
theorem r31_byte {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ t : ℕ} (ht : t < sigHeight)
    (hp : ∀ r ∈ pathRows κ σ, r.Holds w) :
    fb (w (mc κ σ (565 + t) 0)) 0 = fb (w (mc κ σ (549 + t) 1)) 15 := by
  have hb : ∀ q < 128, w (rbC κ σ t q) = 0 ∨ w (rbC κ σ t q) = 1 := fun q hq =>
    boolR_val hone (hp _ (pathRows_mem ht (by
      simp only [pathRowsT, List.mem_append]; exact .inl (.inr (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩)))))
  have e1 := eqR_val hone (hp _ (pathRows_mem ht (List.mem_append_right _ (List.mem_cons_self ..))))
  have e2 := eqR_val hone (hp _ (pathRows_mem ht
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  rw [Lin.ev_cell] at e1 e2
  refine fb_congr (by norm_num) (by norm_num) fun j hj => ?_
  unfold bitN
  rw [e1, e2, bitF_pk w _ (by norm_num) (fun q hq => hb _ (by omega)),
    bitF_pk w _ (by norm_num) hb]
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt (show j < 128 by omega),
    Nat.mod_eq_of_lt (show 8 * 15 + j < 128 by omega)]
  exact decide_eq_decide.2 ⟨fun ⟨_, h⟩ => ⟨by omega, by simpa [show 8 * 15 + j = 120 + j by omega] using h⟩,
    fun ⟨_, h⟩ => ⟨hj, by simpa [show 8 * 15 + j = 120 + j by omega] using h⟩⟩

/-- **Path level `t`** (`path_node` on the level's blocks and mirrors). -/
theorem path_out {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hZ : truthZ4 κ w) (hS : truthS4 κ w)
    {σ t : ℕ} (hσ : σ < 2) (ht : t < sigHeight) (hix : ∀ r ∈ idxRows κ σ, r.Holds w)
    (hp : ∀ r ∈ pathRows κ σ, r.Holds w) :
    curD κ σ w (t + 1) = if idxOf κ σ w / 2 ^ t % 2 = 0 then sigNode (curD κ σ w t) (sibD κ σ w t)
      else sigNode (sibD κ σ w t) (curD κ σ w t) := by
  have hs : sigHeight = 16 := rfl
  have hrow : ∀ r ∈ pathRowsT κ σ t, r.Holds w := fun r hr => hp r (pathRows_mem ht hr)
  have hrow2 : ∀ h < 2, ∀ r ∈ (List.range 2).flatMap (fun h =>
      [eqR κ (Lin.cell (hc (wb κ σ (467 + 2 * t)) h)) (Lin.cell (hc (wb κ σ (466 + 2 * t)) (2 + h))),
       muxR (Lin.cell (ixC κ σ t)) (Lin.cell (sibC κ σ t h)) (Lin.cell (hc (curB κ σ t) (2 + h))) (Lin.cell (mc κ σ (533 + t) h)),
       muxR (Lin.cell (ixC κ σ t)) (Lin.cell (hc (curB κ σ t) (2 + h))) (Lin.cell (sibC κ σ t h)) (Lin.cell (mc κ σ (549 + t) h))]),
      r.Holds w := fun h hh r hr => hrow r (by simp only [pathRowsT, List.mem_append]; exact .inl (.inl hr))
  have hm : ∀ h < 2, ∀ r ∈ [eqR κ (Lin.cell (hc (wb κ σ (467 + 2 * t)) h)) (Lin.cell (hc (wb κ σ (466 + 2 * t)) (2 + h))),
       muxR (Lin.cell (ixC κ σ t)) (Lin.cell (sibC κ σ t h)) (Lin.cell (hc (curB κ σ t) (2 + h))) (Lin.cell (mc κ σ (533 + t) h)),
       muxR (Lin.cell (ixC κ σ t)) (Lin.cell (hc (curB κ σ t) (2 + h))) (Lin.cell (sibC κ σ t h)) (Lin.cell (mc κ σ (549 + t) h))],
      r.Holds w := fun h hh r hr => hrow2 h hh r (List.mem_flatMap.2 ⟨h, List.mem_range.2 hh, hr⟩)
  have hb : w (ixC κ σ t) = 0 ∨ w (ixC κ σ t) = 1 :=
    boolR_val hone (hix _ (List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_range.2 (by omega), rfl⟩)))
  have ml := mux_rows hb (x := sibC κ σ t) (y := fun h => hc (curB κ σ t) (2 + h)) (m := mc κ σ (533 + t))
    fun h hh => hm h hh _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have mr := mux_rows hb (x := fun h => hc (curB κ σ t) (2 + h)) (y := sibC κ σ t) (m := mc κ σ (549 + t))
    fun h hh => hm h hh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have h₁ := holds_wots hZ hσ (o := 466 + 2 * t) (by unfold wotsSlot4; omega)
  have h₂ := holds_wots hZ hσ (o := 467 + 2 * t) (by unfold wotsSlot4; omega)
  rw [NodeT.wotsTgt, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)] at h₁
  rw [NodeT.wotsTgt, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)] at h₂
  have hl : ∀ j < 256, bitsB4 w (wb κ σ (467 + 2 * t)) (pos j) = bitsB4 w (wb κ σ (466 + 2 * t)) (pos (256 + j)) := by
    intro j hj
    have e := eqR_val hone (hm (j / 128) (by omega) _ (List.mem_cons_self ..))
    simp only [Lin.ev_cell] at e
    rw [bitsB4_bit _ _ (by omega), bitsB4_bit _ _ (by omega)]
    unfold hc at e
    rw [e, show wb κ σ (466 + 2 * t) * 128 + (256 + j) / 128 = wb κ σ (466 + 2 * t) * 128 + (2 + j / 128) by omega,
      bitN_mod _ (256 + j), bitN_mod _ j, show (256 + j) % 128 = j % 128 by omega]
  have hnode := Wots.path_node (R := F) h₁ h₂ hl (l := md κ σ (533 + t) w) (r := md κ σ (549 + t) w) ?_
  · rw [readDigest_digestOf] at hnode
    have hc1 : curB κ σ (t + 1) = wb κ σ (467 + 2 * t) := by simp [curB]
    unfold curD
    rw [hc1, hnode, md, md, ml, mr]
    rw [show hc (curB κ σ t) (2 + 0) = hc (curB κ σ t) 2 from rfl,
      show hc (curB κ σ t) (2 + 1) = hc (curB κ σ t) 3 from rfl]
    by_cases hb1 : w (ixC κ σ t) = 1
    · rw [if_pos hb1, if_pos hb1, if_neg (fun h => (idx_bit hone hix (by omega)).1 h hb1)]; rfl
    · rw [if_neg hb1, if_neg hb1, if_pos ((idx_bit hone hix (by omega)).2 hb1)]; rfl
  · -- the message: `tagSigNode ‖ l ‖ r`
    refine list_ext_getD (by simp [msgBytes_len]) fun p hp' => ?_
    simp only [List.length_append, msgBytes_len, List.length_take, Nat.min_def] at hp'
    split_ifs at hp' <;> try omega
    rcases (by omega : p = 0 ∨ (1 ≤ p ∧ p < 33) ∨ (33 ≤ p ∧ p < 64) ∨ p = 64) with rfl | ⟨a, b⟩ | ⟨a, b⟩ | rfl
    · rw [List.getD_append _ _ _ _ (by simp [msgBytes_len]), msgBytes_getD _ (by norm_num),
        (hashB1 tagSigNode).msgByte_eq (p := 0) (by norm_num) (u := tagSigNode) (by simp [hashB1]) h₁]
      rfl
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have := fam_byte (f := 5) hS hσ (by decide) (t := t) (by simp [NodeT.fam]; omega) (k := q)
        (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
      simp only [NodeT.fam, Nat.zero_div, Nat.zero_add, show 1 + q = q + 1 by omega] at this
      rw [List.getD_append _ _ _ _ (by simp [msgBytes_len]; omega), this, ← md_get _ _ _ _ (by omega),
        List.cons_append, List.getD_cons_succ, List.getD_append _ _ _ _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, show q < 32 by omega]
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + 33 := ⟨p - 33, by omega⟩
      have := fam_byte (f := 6) hS hσ (by decide) (t := t) (by simp [NodeT.fam]; omega) (k := q)
        (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
      simp only [NodeT.fam, Nat.zero_div, Nat.zero_add, show 33 + q = q + 33 by omega] at this
      rw [List.getD_append _ _ _ _ (by simp [msgBytes_len]; omega), this, ← md_get _ _ _ _ (by omega),
        show q + 33 = (q + 32) + 1 by omega, List.cons_append, List.getD_cons_succ,
        List.getD_append_right _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, show q < 32 by omega]
    · have := fam_byte (f := 7) hS hσ (by decide) (t := t) (by simp [NodeT.fam]; omega) (k := 0)
        (by simp [NodeT.fam]) (by decide) (by decide) (by decide)
      simp only [NodeT.fam, Nat.zero_div, Nat.zero_add] at this
      rw [List.getD_append_right _ _ _ _ (by simp [msgBytes_len]), msgBytes_len, show 64 - 64 = 0 from rfl,
        List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by norm_num), ← List.getD_eq_getElem?_getD,
        this, r31_byte hone ht hp, show (64 : ℕ) = 63 + 1 from rfl, List.cons_append, List.getD_cons_succ,
        List.getD_append_right _ _ _ _ (by simp)]
      have := md_get κ σ (549 + t) w (i := 31) (by norm_num)
      simp only [show 31 / 16 = 1 from rfl, show 31 % 16 = 15 from rfl] at this
      rw [← this]
      simp [List.getD_eq_getElem?_getD]

/-! ## The root -/

theorem pub_vk {κ : NodeKind} {w : Asg} {vk c₁ c₂ : Digest} (hP : PubCells4 κ w vk c₁ c₂) {σ : ℕ} (hσ : σ < 2) :
    w (seedC κ σ 0) = dlo vk ∧ w (seedC κ σ 1) = dhi vk := by
  unfold PubCells4 at hP
  simp [cells4, Node.pubVals, Node.halves, List.range_succ] at hP
  rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl
  · exact ⟨hP.2.1, hP.2.2.1⟩
  · exact ⟨hP.2.2.2.2.2.1, hP.2.2.2.2.2.2.1⟩

/-- **The root is `vk`.** -/
theorem root_vk {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {vk c₁ c₂ : Digest} (hP : PubCells4 κ w vk c₁ c₂)
    {σ : ℕ} (hσ : σ < 2) (hr : ∀ r ∈ rootRows κ σ, r.Holds w) : curD κ σ w sigHeight = vk := by
  have e := fun h (hh : h < 2) => eqR_val hone (hr _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩))
  simp only [Lin.ev_cell] at e
  obtain ⟨h0, h1⟩ := pub_vk hP hσ
  have hc1 : curB κ σ sigHeight = wb κ σ 497 := by simp [curB, sigHeight]
  unfold curD
  rw [hc1]
  exact Snd.digestOf_halves ((e 0 (by norm_num)).trans h0) ((e 1 (by norm_num)).trans h1)

end W4
end FR
