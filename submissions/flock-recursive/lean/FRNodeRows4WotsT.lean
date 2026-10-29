-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2; stage S-E13b, track L-circ). 3.x:
-- `FRWots.wots_chain_sound`, `digitSel_sound`.
import FRNodeRows4WotsS

/-!
# The WOTS chains of a 4.1 node: selectors and mux rows

* **`sel_val`**: chain `i`'s three selector cells are `[d_i < 1]`, `[d_i < 2]`, `[d_i < 3]` (as `0`/`1`),
  from the selector rows and the digit bits (S-E2 F-2);
* **`dig_mux`**: two mux rows (one per element) select a digest;
* **`chain_end`**: chain `i`'s end mirror is the contract's `wotsChain idx i d_i (3 − d_i) ots_i`.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block ProductCircuit Blake2sCircuit Kinds

/-! ## Membership in the WOTS rows -/

theorem mem_wotsRows {κ : NodeKind} {σ : ℕ} {S : ℕ → Lin} {r : Row} :
    r ∈ wotsRows κ σ S ↔ r ∈ idxRows κ σ ∨ r ∈ selRows κ σ ∨ r ∈ chainRows κ σ ∨ r ∈ leafRows κ σ ∨
      r ∈ pathRows κ σ ∨ r ∈ rootRows κ σ ∨ r ∈ digRows κ σ S ∨ r ∈ sumRows κ σ := by
  simp only [wotsRows, List.mem_append, or_assoc]

/-! ## Digits and selectors -/

/-- A cell's bit (`1` exactly). -/
def bv (w : Asg) (c : ℕ) : ℕ := if w c = 1 then 1 else 0

/-- **Digit `i`** as the circuit holds it: `b₀ + 2 b₁` of its two bit cells. -/
def digV (κ : NodeKind) (σ : ℕ) (w : Asg) (i : ℕ) : ℕ := bv w (digC κ σ (2 * i)) + 2 * bv w (digC κ σ (2 * i + 1))

theorem digV_le (κ : NodeKind) (σ : ℕ) (w : Asg) (i : ℕ) : digV κ σ w i ≤ 3 := by
  unfold digV bv; split_ifs <;> omega

/-- `ots_i` as a digest. -/
noncomputable def otsD (κ : NodeKind) (σ : ℕ) (w : Asg) (i : ℕ) : Digest := Read.digestOf w (otsC κ σ i 0) (otsC κ σ i 1)

/-- **The selectors** (S-E2 F-2): `s_k = [d < k + 1]`, Boolean. -/
theorem sel_val {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ i : ℕ} (hi : i < wotsLen)
    (hb₀ : w (digC κ σ (2 * i)) = 0 ∨ w (digC κ σ (2 * i)) = 1)
    (hb₁ : w (digC κ σ (2 * i + 1)) = 0 ∨ w (digC κ σ (2 * i + 1)) = 1)
    (hsel : ∀ r ∈ selRows κ σ, r.Holds w) {k : ℕ} (hk : k < 3) :
    w (selC κ σ i k) = if digV κ σ w i < k + 1 then 1 else 0 := by
  have hm : ∀ r ∈ [(⟨(one κ).sub (Lin.cell (digC κ σ (2 * i))), (one κ).sub (Lin.cell (digC κ σ (2 * i + 1))),
      Lin.cell (selC κ σ i 0)⟩ : Row),
      eqR κ (Lin.cell (selC κ σ i 1)) ((one κ).sub (Lin.cell (digC κ σ (2 * i + 1)))),
      ⟨Lin.cell (digC κ σ (2 * i)), Lin.cell (digC κ σ (2 * i + 1)), (one κ).sub (Lin.cell (selC κ σ i 2))⟩],
      r.Holds w := fun r hr => hsel r (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hr⟩)
  have r0 := hm _ (List.mem_cons_self ..)
  have r1 := eqR_val hone (hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have r2 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  simp only [Row.Holds, one, Lin.ev_sub, Lin.ev_cell, hone] at r0 r1 r2
  interval_cases k
  · rcases hb₀ with h₀ | h₀ <;> rcases hb₁ with h₁ | h₁ <;> rw [h₀, h₁] at r0 <;>
      simp [digV, bv, h₀, h₁] <;> linear_combination -r0
  · rcases hb₀ with h₀ | h₀ <;> rcases hb₁ with h₁ | h₁ <;> rw [h₁] at r1 <;>
      simp [digV, bv, h₀, h₁] <;> linear_combination r1
  · rcases hb₀ with h₀ | h₀ <;> rcases hb₁ with h₁ | h₁ <;> rw [h₀, h₁] at r2 <;>
      simp [digV, bv, h₀, h₁] <;> linear_combination r2

/-! ## The mux on digests -/

theorem dig_mux {w : Asg} {sv : F} {m₀ m₁ x₀ x₁ y₀ y₁ : ℕ}
    (h₀ : w m₀ = if sv = 1 then w x₀ else w y₀) (h₁ : w m₁ = if sv = 1 then w x₁ else w y₁) :
    Read.digestOf w m₀ m₁ = if sv = 1 then Read.digestOf w x₀ x₁ else Read.digestOf w y₀ y₁ := by
  split_ifs with h
  · rw [if_pos h] at h₀ h₁; exact digestOf_congr h₀ h₁
  · rw [if_neg h] at h₀ h₁; exact digestOf_congr h₀ h₁

/-- Two mux rows (elements `0`, `1`) with a Boolean selector cell. -/
theorem mux_rows {w : Asg} {s : ℕ} (hs : w s = 0 ∨ w s = 1) {x y m : ℕ → ℕ}
    (hr : ∀ h < 2, (muxR (Lin.cell s) (Lin.cell (x h)) (Lin.cell (y h)) (Lin.cell (m h))).Holds w) :
    Read.digestOf w (m 0) (m 1) = if w s = 1 then Read.digestOf w (x 0) (x 1) else Read.digestOf w (y 0) (y 1) := by
  have e := fun h (hh : h < 2) => muxR_val (hr h hh) (by simpa using hs)
  simp only [Lin.ev_cell] at e
  exact dig_mux (e 0 (by norm_num)) (e 1 (by norm_num))

/-! ## A chain -/

/-- **Chain `i`'s end** (`wots_chain_sound` on the blocks and the mux rows). -/
theorem chain_end {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hZ : truthZ4 κ w) (hS : truthS4 κ w)
    {σ i : ℕ} (hσ : σ < 2) (hi : i < wotsLen) (hj : w (mc κ σ 399 0) = w (Lc κ σ 0))
    (hb₀ : w (digC κ σ (2 * i)) = 0 ∨ w (digC κ σ (2 * i)) = 1)
    (hb₁ : w (digC κ σ (2 * i + 1)) = 0 ∨ w (digC κ σ (2 * i + 1)) = 1)
    (hsel : ∀ r ∈ selRows κ σ, r.Holds w) (hch : ∀ r ∈ chainRows κ σ, r.Holds w) :
    md κ σ (endG i) w = wotsChain (idxOf κ σ w) i (digV κ σ w i) (3 - digV κ σ w i) (otsD κ σ w i) := by
  have hrow : ∀ h < 2, ∀ r ∈ chainRowsI κ σ i h, r.Holds w := fun h hh r hr =>
    hch r (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_flatMap.2 ⟨h, List.mem_range.2 hh, hr⟩⟩)
  have sv := fun k (hk : k < 3) => sel_val hone hi hb₀ hb₁ hsel hk
  have sb : ∀ k < 3, w (selC κ σ i k) = 0 ∨ w (selC κ σ i k) = 1 := fun k hk => by
    rw [sv k hk]; split_ifs <;> simp
  have s1 : ∀ k < 3, (w (selC κ σ i k) = 1 ↔ digV κ σ w i < k + 1) := fun k hk => by
    rw [sv k hk]; split_ifs with h <;> simp [h]
  have hout : ∀ s < 3, Read.digestOf w (hc (wb κ σ (3 * i + s)) 2) (hc (wb κ σ (3 * i + s)) 3) =
      wotsStep (idxOf κ σ w) i s (md κ σ (3 * i + s) w) := fun s hs => by
    rw [← readDigest_digestOf]; exact step_out hZ hS hσ hi hs hj
  have m := fun k (hk : k < 3) (g : ℕ) (hg : g = if k = 2 then endG i else 3 * i + (k + 1)) =>
    mux_rows (sb k hk) (x := fun h => hc (wb κ σ (3 * i + k)) (2 + h)) (y := otsC κ σ i)
      (m := fun h => mc κ σ g h) fun h hh => hrow h hh _ (by
        subst hg; interval_cases k <;> simp [chainRowsI])
  have a0 : md κ σ (3 * i) w = otsD κ σ w i := digestOf_congr
    (by simpa using eqR_val hone (hrow 0 (by norm_num) _ (List.mem_cons_self ..)))
    (by simpa using eqR_val hone (hrow 1 (by norm_num) _ (List.mem_cons_self ..)))
  refine Wots.wots_chain_sound (digV_le κ σ w i)
    (out := fun s => Read.digestOf w (hc (wb κ σ (3 * i + (s - 1))) 2) (hc (wb κ σ (3 * i + (s - 1))) 3))
    (a := fun s => md κ σ (3 * i + (s - 1)) w)
    (fun s h1 h2 => hout (s - 1) (by omega)) (fun s h1 h2 => ?_) ?_
  · rcases (by omega : s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl
    · rw [if_neg (by omega)]; simpa using a0
    · rw [show 3 * i + (2 - 1) = 3 * i + 1 by omega, show 3 * i + (2 - 1 - 1) = 3 * i + 0 by omega, md,
        m 0 (by norm_num) (3 * i + 1) (by simp)]
      by_cases h : digV κ σ w i < 0 + 1
      · rw [if_pos ((s1 0 (by norm_num)).2 h), if_pos (by omega)]
      · rw [if_neg (mt (s1 0 (by norm_num)).1 h), if_neg (by omega)]; rfl
    · rw [show 3 * i + (3 - 1) = 3 * i + 2 by omega, show 3 * i + (3 - 1 - 1) = 3 * i + 1 by omega, md,
        m 1 (by norm_num) (3 * i + (1 + 1)) (by simp)]
      by_cases h : digV κ σ w i < 1 + 1
      · rw [if_pos ((s1 1 (by norm_num)).2 h), if_pos (by omega)]
      · rw [if_neg (mt (s1 1 (by norm_num)).1 h), if_neg (by omega)]; rfl
  · rw [md, m 2 (by norm_num) (endG i) (by simp)]
    by_cases h : digV κ σ w i < 2 + 1
    · rw [if_pos ((s1 2 (by norm_num)).2 h), if_pos (by omega)]
    · rw [if_neg (mt (s1 2 (by norm_num)).1 h), if_neg (by omega)]; rfl

end W4
end FR
