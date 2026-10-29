-- New for `flock-recursive` (BLUEPRINT revision 4.3, (A)(ii); stage S-H4, pass 8, item 1:
-- `sig_of_H`). Uses S-E13b's WOTS rows (`FRNodeRows4Wots*`) and link families (`truthS4`).
import FRXSig4
import FRNodeRows4PackSound

/-!
# `sig_of_H`: the signature read off H is L's

On every witness of the node statement (`StmtN4`), the signature `sigH` reads from H's message
slots is the one the reader reads from L (`readSig4`). Every equality H ↔ L has a row or a link
family; no hypothesis beyond `StmtN4`:

* **the index**: the `j` family puts the `j` mirror's first eight bytes in the key leaf's message
  bytes `1 … 8`, and the index row makes the mirror L's index element (`j_byte`, `j_mirror`);
* **`ots_i`**: the `x` family puts mirror `3i` in block `3i`'s bytes `11 … 42` (`fam_byte`), and the
  chain row `x_{i,0} = ots_i` makes the mirror L's `ots_i` (`chainRowsI`, first row);
* **sibling `t`**: the `l` (`r0`, `r31`) family puts mirror `533 + t` (`549 + t`, `565 + t`) in the
  level's message bytes, and the mux rows make the `l` mirror the sibling when the index bit is `1`,
  the `r` mirror when it is `0` (`mux_rows`, `idx_bit`); byte 31 of `r` comes through the `r31`
  mirror (`r31_byte`).

The node rows `W4.xRows` hold on `StmtN4` (they are slot 1's link rows when their cell check
passes; otherwise slot 1 holds the rejecting row: `xRows_of_stmt`, S-E13a's fold).
-/

namespace FR.X

open RecursionFast FR.Snd FR.Rev4 FR.Circ FR.N4c FR.W4

/-- **The node rows hold on the node statement** (S-E13a's fold, `wots_aggPad_of_rows`'s split). -/
theorem xRows_of_stmt {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) : ∀ r ∈ xRows κ, r.Holds w := by
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hone := N4s.one_of_pubCells hP
  have hF := N4s.protoFit_of hone hE
  have h1 : 1 < κ.vslots := by cases κ <;> decide
  have hl := N4s.linkRows_hold hF h1 hE
  by_cases h : xOkK κ = true
  · intro r hr
    refine hl r (List.mem_append_right _ ?_)
    rw [extRowsC, if_pos rfl, if_pos h, xRowsK_eq]; exact List.mem_append_left _ hr
  · exfalso
    have := hl (rejR κ) (List.mem_append_right _ (by rw [extRowsC, if_pos rfl, if_neg h]; simp))
    simp [rejR, Row.Holds, hone] at this

/-- **The index read off H is L's** (`j` family, index row). -/
theorem idxH_eq {κ : NodeKind} {w : Asg} (hS : truthS4 κ w) {σ : ℕ} (hσ : σ < 2)
    (hj : w (mc κ σ 399 0) = w (Lc κ σ 0)) : idxH κ σ w = W4.idxOf κ σ w := by
  have hl : ((List.range 8).map fun k => hMB w (wb κ σ 399) (1 + k)) = enc64 (W4.idxOf κ σ w) := by
    refine list_ext_getD (by simp [enc64_length]) fun k hk => ?_
    simp only [List.length_map, List.length_range] at hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range,
      hMB_eq _ _ (by omega), j_byte hS hσ (by norm_num) hk hj]
  have hlt : W4.idxOf κ σ w < 2 ^ 64 := by
    unfold W4.idxOf; exact (UInt64.toNat_lt _).trans_le (by norm_num)
  rw [idxH, hl, ofLE_enc64, Nat.mod_eq_of_lt hlt]

/-- **`ots_i` read off H is L's** (`x` family, the chain's first row). -/
theorem otsH_eq {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hS : truthS4 κ w) {σ : ℕ}
    (hσ : σ < 2) (hch : ∀ r ∈ chainRows κ σ, r.Holds w) {i : ℕ} (hi : i < wotsLen) :
    hMD w (wb κ σ (3 * i)) 11 = Read.digestOf w (N4s.sigCell κ σ (1 + 2 * i)) (N4s.sigCell κ σ (2 + 2 * i)) := by
  have e : ∀ h < 2, w (mc κ σ (3 * i) h) = w (otsC κ σ i h) := fun h hh => by
    have := eqR_val hone (hch _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨h, List.mem_range.2 hh, List.mem_cons_self ..⟩⟩))
    simpa using this
  have hd : Read.digestOf w (N4s.sigCell κ σ (1 + 2 * i)) (N4s.sigCell κ σ (2 + 2 * i)) = md κ σ (3 * i) w := by
    rw [md, digestOf_congr (e 0 (by norm_num)) (e 1 (by norm_num))]
    unfold otsC N4s.sigCell Lc; rw [show 1 + 2 * i + 1 = 2 + 2 * i by omega, Nat.add_zero]
  rw [hd]
  refine Vector.ext fun k hk => ?_
  have := fam_byte (f := 0) hS hσ (by decide) (t := 3 * i) (by simp [NodeT.fam]; unfold wotsLen at hi; omega)
    (k := k) (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
  simp only [NodeT.fam, id, Nat.zero_div, Nat.zero_add] at this
  rw [hMD, Vector.getElem_ofFn, hMB_eq _ _ (by omega), this, md_get _ _ _ _ hk]

/-- **Path sibling `t` read off H is L's** (`l`/`r0`/`r31` families, the mux rows). -/
theorem sibFH_eq {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hS : truthS4 κ w) {σ : ℕ}
    (hσ : σ < 2) (hix : ∀ r ∈ idxRows κ σ, r.Holds w) (hp : ∀ r ∈ pathRows κ σ, r.Holds w)
    {t : ℕ} (ht : t < sigHeight) : sibFH κ σ t w = sibD κ σ w t := by
  have hs : sigHeight = 16 := rfl
  have hm : ∀ h < 2, ∀ r ∈ [eqR κ (Lin.cell (hc (wb κ σ (467 + 2 * t)) h)) (Lin.cell (hc (wb κ σ (466 + 2 * t)) (2 + h))),
       muxR (Lin.cell (ixC κ σ t)) (Lin.cell (sibC κ σ t h)) (Lin.cell (hc (curB κ σ t) (2 + h))) (Lin.cell (mc κ σ (533 + t) h)),
       muxR (Lin.cell (ixC κ σ t)) (Lin.cell (hc (curB κ σ t) (2 + h))) (Lin.cell (sibC κ σ t h)) (Lin.cell (mc κ σ (549 + t) h))],
      r.Holds w := fun h hh r hr => hp r (pathRows_mem ht (by
        simp only [pathRowsT, List.mem_append]; exact .inl (.inl (List.mem_flatMap.2 ⟨h, List.mem_range.2 hh, hr⟩))))
  have hb : w (ixC κ σ t) = 0 ∨ w (ixC κ σ t) = 1 :=
    boolR_val hone (hix _ (List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_range.2 (by omega), rfl⟩)))
  have ml := mux_rows hb (x := sibC κ σ t) (y := fun h => hc (curB κ σ t) (2 + h)) (m := mc κ σ (533 + t))
    fun h hh => hm h hh _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have mr := mux_rows hb (x := fun h => hc (curB κ σ t) (2 + h)) (y := sibC κ σ t) (m := mc κ σ (549 + t))
    fun h hh => hm h hh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rw [sibFH, idxH_eq hS hσ (j_mirror hone hix)]
  by_cases hb1 : w (ixC κ σ t) = 1
  · have hbit : W4.idxOf κ σ w / 2 ^ t % 2 = 1 := by
      have := (idx_bit hone hix (by omega : t < 16)).not.2 (not_not.2 hb1); omega
    rw [if_pos hbit]
    rw [if_pos hb1] at ml
    rw [sibD, ← ml]
    refine Vector.ext fun k hk => ?_
    have := fam_byte (f := 5) hS hσ (by decide) (t := t) (by simp [NodeT.fam]; omega) (k := k)
      (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
    simp only [NodeT.fam, Nat.zero_div, Nat.zero_add] at this
    rw [hMD, Vector.getElem_ofFn, hMB_eq _ _ (by omega), this, ← md, md_get _ _ _ _ hk]
  · have hbit : ¬ W4.idxOf κ σ w / 2 ^ t % 2 = 1 := by
      have := (idx_bit hone hix (by omega : t < 16)).2 hb1; omega
    rw [if_neg hbit]
    rw [if_neg hb1] at mr
    rw [sibD, ← mr]
    refine Vector.ext fun k hk => ?_
    rw [rFH, Vector.getElem_ofFn, ← md, md_get _ _ _ _ hk]
    split_ifs with h31
    · have := fam_byte (f := 6) hS hσ (by decide) (t := t) (by simp [NodeT.fam]; omega) (k := k)
        (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
      simp only [NodeT.fam, Nat.zero_div, Nat.zero_add] at this
      rw [hMB_eq _ _ (by omega), this]
    · have := fam_byte (f := 7) hS hσ (by decide) (t := t) (by simp [NodeT.fam]; omega) (k := 0)
        (by simp [NodeT.fam]) (by decide) (by decide) (by decide)
      simp only [NodeT.fam, Nat.zero_div, Nat.zero_add] at this
      have k31 : k = 31 := by simp only [not_lt] at h31; omega
      rw [hMB_eq _ _ (by norm_num), this, r31_byte hone ht hp, k31]

/-- **`sig_of_H`**: on every witness of the node statement, the signature read off H's message
slots (`sigH`) is the one the reader reads off L (`readSig4`). -/
theorem sig_of_H {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ σ < 2, sigH κ σ w = N4s.readSig4 κ σ w := by
  have hX := xRows_of_stmt hS
  obtain ⟨-, hSh, -, -, hP⟩ := hS
  have hone := N4s.one_of_pubCells hP
  intro σ hσ
  have hMW : ∀ r ∈ wotsRows κ σ (actW κ (aggOf κ σ)), r.Holds w := fun r hr => hX r (by
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl
    · exact List.mem_append_left _ (List.mem_append_left _ hr)
    · exact List.mem_append_left _ (List.mem_append_right _ hr))
  have hix : ∀ r ∈ idxRows κ σ, r.Holds w := fun r h => hMW r (mem_wotsRows.2 (.inl h))
  have hch : ∀ r ∈ chainRows κ σ, r.Holds w := fun r h => hMW r (mem_wotsRows.2 (.inr (.inr (.inl h))))
  have hpa : ∀ r ∈ pathRows κ σ, r.Holds w := fun r h =>
    hMW r (mem_wotsRows.2 (.inr (.inr (.inr (.inr (.inl h))))))
  have hj := j_mirror hone hix
  have e1 : (sigH κ σ w).idx = (N4s.readSig4 κ σ w).idx := idxH_eq hSh hσ hj
  have e2 : (sigH κ σ w).ots = (N4s.readSig4 κ σ w).ots :=
    List.map_congr_left fun i hi => otsH_eq hone hSh hσ hch (List.mem_range.1 hi)
  have e3 : (sigH κ σ w).path = (N4s.readSig4 κ σ w).path := by
    simp only [sigH, N4s.readSig4]
    refine List.map_congr_left fun t ht => ?_
    rw [sibFH_eq hone hSh hσ hix hpa (List.mem_range.1 ht), sibD]
    unfold sibC N4s.sigCell Lc
    rw [show 1 + 2 * wotsLen + 2 * t + 1 = 2 + 2 * wotsLen + 2 * t by omega, Nat.add_zero]
  calc sigH κ σ w = ⟨(sigH κ σ w).idx, (sigH κ σ w).ots, (sigH κ σ w).path⟩ := rfl
    _ = ⟨(N4s.readSig4 κ σ w).idx, (N4s.readSig4 κ σ w).ots, (N4s.readSig4 κ σ w).path⟩ := by
      rw [e1, e2, e3]
    _ = N4s.readSig4 κ σ w := rfl

/-- **`readW4 sigH` is the reader's node witness** on every node statement's witness `f⁽⁰⁾ = wF κ L es`
(`readW4_eq` with `sig_of_H`): the bridge S-L4's `hL_of_res` uses at `sg := sigH`. -/
theorem readW4_sigH {κ : NodeKind} {L es : Log} {vk c₁ c₂ : Digest}
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ (wF κ L es)) :
    readW4 sigH κ L es = .node c₁ c₂ ((N4s.rd4 pf4).sgn κ 0 (wF κ L es)) ((N4s.rd4 pf4).sgn κ 1 (wF κ L es)) :=
  readW4_eq hS.2.2.2.2 (sig_of_H hS)

end FR.X
