-- New for `flock-recursive` (BLUEPRINT revision 4.1, R-4-m2; stage S-E13b, track L-circ).
import FRNodeRows4WotsK

/-!
# `Gap4.aggPad` from the node rows (R-4-m2's `k`-gated final block)

Aggregate `a` of `k` segments ends at its candidate final block `F_{a,k}` (`k < maxK`) or at its
main chain's last block (`k = maxK`). The `aggPad` rows, gated by `[k = j]`, make the final block's
`h_in` the main chain's block `aggL k − 2`'s `h_out` and its message the main chain's block
`aggL k − 1`'s. With R-A′'s spacers the stream fills its last block (`lastR k = 64`), so the message
is whole (elements 4–7) and there is no padding.

* **`zN4_of_elem`**: equal elements have equal bits;
* **`gap4_aggPad`**: on `StmtN4` and the node rows, `AggPad4 κ a (kA (rd4 pf) κ w a) w` for every
  aggregate.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block

theorem zN4_of_elem {w : Asg} {b b' e e' x : ℕ} (he : w (hc b e) = w (hc b' e')) (hx : x < 128)
    (h1 : 128 * e + x < 2 ^ 14) (h2 : 128 * e' + x < 2 ^ 14) :
    zN4 w b (128 * e + x) = zN4 w b' (128 * e' + x) := by
  rw [zN4_eq w b h1, zN4_eq w b' h2]
  unfold hc at he
  rw [show b * 128 + (128 * e + x) / 128 = b * 128 + e by omega,
    show b' * 128 + (128 * e' + x) / 128 = b' * 128 + e' by omega, he, bitN_mod, bitN_mod _ (128 * e' + x),
    show (128 * e + x) % 128 = x by omega, show (128 * e' + x) % 128 = x by omega]

theorem zN4_bit {w : Asg} {b e x : ℕ} (hx : x < 128) (h1 : 128 * e + x < 2 ^ 14) :
    zN4 w b (128 * e + x) = if bitF (w (hc b e)) ⟨x, hx⟩ then 1 else 0 := by
  rw [zN4_eq w b h1]
  unfold bitN hc
  rw [show b * 128 + (128 * e + x) / 128 = b * 128 + e by omega]
  simp only [show (128 * e + x) % 128 = x by omega]

theorem lastR_64 {k : ℕ} (h1 : 1 ≤ k) (h4 : k ≤ 4) : lastR k = 64 := by
  interval_cases k <;> decide

theorem maxK_le (κ : NodeKind) : 2 ≤ κ.maxK ∧ κ.maxK ≤ 4 := by cases κ <;> decide

/-- **`Gap4.aggPad` from the node rows.** -/
theorem gap4_aggPad (pf : Trace → Proof) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) (hX : ∀ r ∈ xRows κ, r.Holds w) :
    ∀ a < nAgg κ, AggPad4 κ a (kA (N4s.rd4 pf) κ w a) w := by
  obtain ⟨hZ, hSh, hL, hE, hP⟩ := hS
  have hone := N4s.one_of_pubCells hP
  have hF := N4s.protoFit_of hone hE
  intro a ha
  have hlk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w :=
    fun i hi => N4s.linkRows_hold hF (sub_facts κ ha hi).1 hE
  have hK := N4s.actK_kAct hone ha hL hlk
  have hPr := act_profile hone ha hL hlk hK
  obtain ⟨hk1, hkm, -⟩ := hK
  rw [N4s.kA_rd4 pf κ ha]
  set k := N4s.kAct κ a w with hkdef
  set σ := aggChild κ a with hσdef
  have hpad : ∀ r ∈ padRows κ a (actW κ a), r.Holds w := fun r hr =>
    hX r (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, hr⟩))
  obtain ⟨hm2, hm4⟩ := maxK_le κ
  have hind : (ind κ (actW κ a) k).ev w = 1 := by rw [ind_ev hk1 hkm hPr hk1 hkm, if_pos rfl]
  have hL2 : 2 ≤ aggL k := N4c.aggL_ge hk1
  have hr : aggB k - 64 * (aggL k - 1) = 64 := lastR_64 hk1 (by omega)
  refine ⟨fun hlt => ?_, fun x hx1 hx2 => absurd hx1 (by rw [hr]; omega)⟩
  -- `k < maxK`: the candidate block's links
  have hrows : ∀ r ∈ (List.range 2).map (fun h =>
      gateR (ind κ (actW κ a) k) ((Lin.cell (hc (finBlk κ σ k) h)).sub (Lin.cell (hc (mb κ σ (aggL k - 2)) (2 + h))))) ++
      (List.range 4).map (fun e =>
      gateR (ind κ (actW κ a) k) ((Lin.cell (hc (finBlk κ σ k) (4 + e))).sub (Lin.cell (hc (mb κ σ (aggL k - 1)) (4 + e))))),
      r.Holds w := fun r hr => hpad r (by
    unfold padRows
    refine List.mem_flatMap.2 ⟨k - 1, List.mem_range.2 (by omega), ?_⟩
    rw [show k - 1 + 1 = k by omega]; exact hr)
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have e := gateR_val (hrows _ (List.mem_append_left _
      (List.mem_map.2 ⟨x / 128, List.mem_range.2 (by omega), rfl⟩))) hind
    simp only [Lin.ev_sub, Lin.ev_cell, sub_eq_zero] at e
    have := zN4_of_elem e (x := x % 128) (Nat.mod_lt _ (by norm_num)) (by omega) (by omega)
    rw [show 128 * (x / 128) + x % 128 = x by omega, show 128 * (2 + x / 128) + x % 128 = 256 + x by omega,
      show mb κ σ (aggL k - 2) = chBase κ σ + aggL k - 2 by unfold mb; omega] at this
    exact this
  · rw [hr] at hx
    have e := gateR_val (hrows _ (List.mem_append_right _
      (List.mem_map.2 ⟨x / 128, List.mem_range.2 (by omega), rfl⟩))) hind
    simp only [Lin.ev_sub, Lin.ev_cell, sub_eq_zero] at e
    have := zN4_of_elem e (x := x % 128) (Nat.mod_lt _ (by norm_num)) (by omega) (by omega)
    rw [show 128 * (4 + x / 128) + x % 128 = 512 + x by omega,
      show mb κ σ (aggL k - 1) = chBase κ σ + aggL k - 1 by unfold mb; omega] at this
    exact this

end W4
end FR

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c

/-! ## The fold: the node rows from the M rows -/

/-- **The node rows hold** once they are folded into slot 1's link rows (`hfold`: S-E13a's
`linkRows4 = linkRowsB4 ++ packRows4 ++ extRows4`, `extRows4 κ 1 = xRows κ`). -/
theorem xRows_hold {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} (hfold : ∀ r ∈ xRows κ, r ∈ linkRows4 κ 1)
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) : ∀ r ∈ xRows κ, r.Holds w := fun r hr => by
  obtain ⟨-, -, -, hE, hP⟩ := hS
  exact N4s.linkRows_hold (N4s.protoFit_of (N4s.one_of_pubCells hP) hE) (by cases κ <;> decide) hE r (hfold r hr)

/-- **`Gap4.wots` and `Gap4.aggPad` from the M rows** (with the fold). -/
theorem gap4_wots_aggPad (pf : Trace → Proof) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hfold : ∀ r ∈ xRows κ, r ∈ linkRows4 κ 1) (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    (∀ σ < 2, SigOk vk (hDig4 κ σ (kOf (N4s.rd4 pf) κ w σ) w) ((N4s.rd4 pf).sgn κ σ w).σ = true) ∧
      ∀ a < nAgg κ, AggPad4 κ a (kA (N4s.rd4 pf) κ w a) w :=
  ⟨gap4_wots pf hS (xRows_hold hfold hS), gap4_aggPad pf hS (xRows_hold hfold hS)⟩

end W4
end FR
