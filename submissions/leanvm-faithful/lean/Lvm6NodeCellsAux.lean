-- New for lvm6 (WP N4-cells). The auxiliary rows under the `E2` relation: season 1's `lh_auxRow` (K-only,
-- `WiringRel`) lifted to the coordinate-split relation `WiringRelX`, hence (through `wiringRelT_iff` and
-- `wiringRelE_iff`) to `TGoodE`; then NODE3's `PowRowsHold` from `TGoodE` and the layout's PoW blocks.
import Lvm6NodeSlots

/-!
# Auxiliary rows from `TGoodE` (WP N4-cells, target 1)

* **`lhx_ents_at_aux`**: at an auxiliary slot, the coordinate-split entries (`entsX`) are the row's own
  (`lh_ents_at_aux` with `instEntsX`; `lhx_instEntsX_slot` places every instance entry at a constraint slot).
* **`lhx_auxRow`**: `WiringRelX` gives `ARowHolds` of every auxiliary row at every iteration (coordinate `1` of
  the relation; matrices `4, 5` have no auxiliary entry, `auxRowEnts_o'`).
* **`auxRow_of_tgoodE`**: the same from `TGoodE` (with `Ti.Ok`, `NoE3`).
* **`PowAuxIn lay`** (layout fact; the exporter's `specOf` puts `powBlk a.2 (base k) a.1` for every
  `a ∈ powAns` into `lay.aux`): every PoW answer has a block in the layout.
* **`powRowsHold_of_tgoodE`**: `PowRowsHold Ti.lay (Ti.zOf …)` from `TGoodE` and `PowAuxIn Ti.lay`.
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

/-- **At an auxiliary slot only its row has entries** (the eight matrices). -/
theorem lhx_ents_at_aux {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {k r j : ℕ} (hk : k < lay.aux.length)
    (hr : r < (lay.aux.getD k default).rows.length) (hj : j < 2 ^ (lay.aux.getD k default).l) (o : ℕ) :
    (entsX Q lay).filter (fun e ↦ e.o == o && e.x == lay.auxSlot k r j) =
      (auxRowEnts lay k r j).filter (·.o == o) := by
  obtain ⟨c, hc, hcl⟩ := lh_aux_chunk hlay hk hr
  have hinst : (Q.insts.flatMap (instEntsX Q lay)).filter (fun e ↦ e.o == o && e.x == lay.auxSlot k r j) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
    obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := lh_mem_insts hi
    have hcon := (lhx_instEntsX_slot Q lay _ he).2
    have hx : e.x = lay.slot b t jf := (lhx_instEntsX_slot Q lay _ he).1
    obtain ⟨c', hcr, hx1, hl⟩ := lh_con_chunk hlay hb ht hcon
    unfold Lay.slot at hx
    rw [hcr] at hx
    have := (lh_slotR_inj hlay hx1 hc (hl ▸ hjf) (hcl ▸ hj) (hx.symm.trans hp.2)).1
    have : b < lay.blocks.length := by rw [(lh_ok hlay).2.2.1]; exact hb
    (clear hb hc hcl hcon hcr he hi hj hjf hk hl hlay hp hr ht hx hx1; omega)
  have haux : ∀ k' < lay.aux.length, ∀ j' < 2 ^ (lay.aux.getD k' default).l,
      ∀ r' < (lay.aux.getD k' default).rows.length, ¬ (k' = k ∧ j' = j ∧ r' = r) →
        (auxRowEnts lay k' r' j').filter (fun e ↦ e.o == o && e.x == lay.auxSlot k r j) = [] := by
    intro k' hk' j' hj' r' hr' hne
    rw [List.filter_eq_nil_iff]
    intro e he hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    unfold auxRowEnts at he
    obtain ⟨op, -, he⟩ := List.mem_flatMap.mp he
    obtain ⟨-, h2, -⟩ := lh_mem_tagE he
    obtain ⟨c', hc', hcl'⟩ := lh_aux_chunk hlay hk' hr'
    have := lh_slotR_inj hlay hc' hc (hcl' ▸ hj') (hcl ▸ hj) (h2.symm.trans hp.2)
    exact hne ⟨by (clear * - this; omega), this.2.2, this.2.1⟩
  rw [entsX, List.filter_append, hinst, List.nil_append, auxEnts]
  simp only [List.filter_flatMap]
  rw [lh_flatMap_single _ k _ hk fun k' hk' hne ↦ ?_]
  · rw [lh_flatMap_single _ j _ hj fun j' hj' hne ↦ ?_]
    · rw [lh_flatMap_single _ r _ hr fun r' hr' hne ↦ haux k hk j hj r' hr' fun h ↦ hne h.2.2]
      refine List.filter_congr fun e he ↦ ?_
      unfold auxRowEnts at he
      obtain ⟨op, -, he⟩ := List.mem_flatMap.mp he
      have h2 : e.x = lay.auxSlot k r j := (lh_mem_tagE he).2.1
      simp only [h2, beq_self_eq_true, Bool.and_true]
    · rw [List.flatMap_eq_nil_iff]
      intro r' hr'
      exact haux k hk j' hj' r' (List.mem_range.mp hr') fun h ↦ hne h.2.1
  · rw [List.flatMap_eq_nil_iff]
    intro j' hj'
    rw [List.flatMap_eq_nil_iff]
    intro r' hr'
    exact haux k' hk' j' (List.mem_range.mp hj') r' (List.mem_range.mp hr') fun h ↦ hne h.1

/-- **An auxiliary row holds** at every iteration under the coordinate-split relation. -/
theorem lhx_auxRow (Q : Program) (lay : Lay) (z : ℕ → FK) (hlay : lay.Ok Q) (hone : z lay.one = 1)
    (h : WiringRelX Q lay z) {k r j : ℕ} (hk : k < lay.aux.length) (hj : j < 2 ^ (lay.aux.getD k default).l)
    (hr : r < (lay.aux.getD k default).rows.length) :
    ARowHolds lay z j ((lay.aux.getD k default).rows.getD r default) := by
  have h4 : ∀ o, 4 ≤ o → (auxRowEnts lay k r j).filter (·.o == o) = [] := fun o ho ↦
    List.filter_eq_nil_iff.mpr fun e he hp ↦ by
      have := auxRowEnts_o' hlay k r j e he
      simp only [beq_iff_eq] at hp
      omega
  have := (h (lay.auxSlot k r j)).1
  simp only [relX0, lhx_matZX_eq, lhx_ents_at_aux hlay hk hr hj, h4 4 (le_refl _), h4 5 (by omega)] at this
  simp only [lh_auxVal hone] at this
  have e0 : lh_val z [] = 0 := by simp [lh_val]
  rw [e0, zero_mul, add_zero] at this
  exact this

end Lvm.Typed

namespace Lvm6.Node.Dep

open Lvm Lvm.Loop Lvm.Typed Lvm.Q2 LeanVM.Protocol
open Lvm6.Ty (TInst6 TGoodE NoE3 wiringRelE_iff)

/-- **The auxiliary rows hold on a good pair** (`TGoodE` at `E2`, the instance check, no `E3` row). -/
theorem auxRow_of_tgoodE (Ti : TInst6) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pw : ℕ → FK)
    (p : Column L.nuMain × Column L.nuRec) (hok : Ti.Ok) (hE3 : NoE3 Ti.Q Ti.lay) (hg : TGoodE Ti L hτ pw p)
    {k r j : ℕ} (hk : k < Ti.lay.aux.length) (hj : j < 2 ^ (Ti.lay.aux.getD k default).l)
    (hr : r < (Ti.lay.aux.getD k default).rows.length) :
    ARowHolds Ti.lay (Ti.zOf L pw p.1 p.2) j ((Ti.lay.aux.getD k default).rows.getD r default) := by
  have hone : Ti.zOf L pw p.1 p.2 Ti.lay.one = 1 := by
    unfold TInst6.zOf
    rw [hok.2]
  have hT := (wiringRelE_iff hok.1 hE3).mp hg.1
  exact lhx_auxRow Ti.Q Ti.lay _ hok.1 hone ((wiringRelT_iff Ti.Q Ti.lay hok.1 _).mp hT) hk hj hr

/-- Every row of an auxiliary block of the layout holds at iteration `0`. -/
theorem blkRows_of_tgoodE (Ti : TInst6) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pw : ℕ → FK)
    (p : Column L.nuMain × Column L.nuRec) (hok : Ti.Ok) (hE3 : NoE3 Ti.Q Ti.lay) (hg : TGoodE Ti L hτ pw p)
    {b : ABlk} (hb : b ∈ Ti.lay.aux) : ∀ r ∈ b.rows, ARowHolds Ti.lay (Ti.zOf L pw p.1 p.2) 0 r := by
  intro r hr
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hgk : Ti.lay.aux.getD k default = Ti.lay.aux[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have h := auxRow_of_tgoodE Ti L hτ pw p hok hE3 hg (k := k) (r := i) (j := 0) hk (by positivity)
    (by rw [hgk]; exact hi)
  rw [hgk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
  exact h

/-- **The layout carries the PoW blocks** (the exporter's `specOf`: `powBlk a.2 (base k) a.1` for the `k`-th
answer of `powAns`). A static fact of the deployed layout. -/
def PowAuxIn (lay : Lay) : Prop := ∀ a ∈ powAns, ∃ bw, powBlk a.2 bw a.1 ∈ lay.aux

/-- **`PowRowsHold` from the relation** and the layout's PoW blocks. -/
theorem powRowsHold_of_tgoodE (Ti : TInst6) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pw : ℕ → FK)
    (p : Column L.nuMain × Column L.nuRec) (hok : Ti.Ok) (hE3 : NoE3 Ti.Q Ti.lay) (hg : TGoodE Ti L hτ pw p)
    (hpow : PowAuxIn Ti.lay) : PowRowsHold Ti.lay (Ti.zOf L pw p.1 p.2) := by
  intro a ha
  obtain ⟨bw, hb⟩ := hpow a ha
  exact ⟨bw, blkRows_of_tgoodE Ti L hτ pw p hok hE3 hg hb⟩

end Lvm6.Node.Dep
