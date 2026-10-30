-- G6: this module also holds the former modules `FRNodeRows4WotsT`, `FRNodeRows4WotsL`, `FRNodeRows4WotsP`, `FRNodeRows4WotsD`, `FRNodeRows4WotsF`, `FRNodeRows4WotsK` (one section each, in import order).
import FRNodeRows4WotsS
import FRNodeRun4
import FRNodeRows4Ext

section G6_FRNodeRows4WotsT

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2; stage S-E13b, track L-circ). 3.x:
-- `FRWots.wots_chain_sound`, `digitSel_sound`.

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

end G6_FRNodeRows4WotsT

section G6_FRNodeRows4WotsL

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2; stage S-E13b, track L-circ). 3.x:
-- `FRBlockStream.stream_sound`, `FRWots.path_node`, `sigRoot_bits`.

/-!
# The WOTS key leaf of a 4.1 node

**`leaf_out`**: the key leaf's 67 blocks (`hashB1 tagWotsLeaf`, 65 `stream`, `streamEnd41`), linked
by the leaf rows, hash `tagWotsLeaf ‖ enc64 idx ‖ e₀ ‖ … ‖ e₁₃₂`, the ends read off their mirrors
(`end9` for an even end, `end41lo`/`end41hi` for an odd one, which crosses a block boundary): the
contract's `wotsLeaf idx ends`.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block ProductCircuit Blake2sCircuit Kinds Stream

/-! ## Lists of digests -/

theorem flat_get : ∀ (l : List Digest) (q : ℕ) (hq : q < 32 * l.length),
    (l.flatMap Vector.toList).getD q 0 = (l.getD (q / 32) default).toList.getD (q % 32) 0
  | [], q, hq => by simp at hq
  | e :: l, q, hq => by
    rw [List.flatMap_cons]
    by_cases h : q < 32
    · rw [List.getD_append _ _ _ _ (by simpa using h)]
      simp [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [Vector.length_toList]
      rw [flat_get l (q - 32) (by simp at hq; omega)]
      have e1 : q / 32 = (q - 32) / 32 + 1 := by omega
      have e2 : q % 32 = (q - 32) % 32 := by omega
      simp only [e1, e2, List.getD_cons_succ]

/-- Byte `q` of a digest (`0` past 32). -/
def fb' (d : Digest) (q : ℕ) : UInt8 := d.toList.getD q 0

theorem fb'_eq (d : Digest) {q : ℕ} (hq : q < 32) : fb' d q = d[q] := by
  simp [fb', List.getD_eq_getElem?_getD, hq]

/-! ## The leaf -/

/-- The key leaf's blocks as a stream. -/
noncomputable def leafW (κ : NodeKind) (σ : ℕ) (w : Asg) : ℕ → Pos → Bool := fun u => bitsB4 w (wb κ σ (399 + u))

/-- The chain ends, read off their mirrors. -/
noncomputable def endsD (κ : NodeKind) (σ : ℕ) (w : Asg) : List Digest := (List.range wotsLen).map fun i => md κ σ (endG i) w

theorem nB4265 : nBlocks 4265 = 67 := by decide

/-- The leaf message's byte `p`. -/
theorem leafMsg_get (j : ℕ) (ends : List Digest) (hl : ends.length = wotsLen) {p : ℕ} (hp : p < 4265) :
    (tagWotsLeaf :: enc64 j ++ ends.flatMap Vector.toList).getD p 0 =
      if p = 0 then tagWotsLeaf else if p < 9 then (enc64 j).getD (p - 1) 0
      else fb' (ends.getD ((p - 9) / 32) default) ((p - 9) % 32) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rfl
  rw [if_neg (by omega), show p = (p - 1) + 1 by omega, List.cons_append, List.getD_cons_succ]
  by_cases h9 : p - 1 + 1 < 9
  · rw [if_pos h9, List.getD_append _ _ _ _ (by simp [enc64]; omega), Nat.add_sub_cancel]
  · rw [if_neg h9, List.getD_append_right _ _ _ _ (by simp [enc64]; omega), enc64_length,
      flat_get _ _ (by rw [hl]; unfold wotsLen; omega)]
    simp only [fb', show p - 1 - 8 = p - 1 + 1 - 9 by omega]

/-- The key leaf's message bytes. -/
theorem leaf_bytes {κ : NodeKind} {w : Asg} (hZ : truthZ4 κ w) (hS : truthS4 κ w) {σ : ℕ} (hσ : σ < 2)
    (hj : w (mc κ σ 399 0) = w (Lc κ σ 0)) :
    Stream.streamBytes (leafW κ σ w) 4265 = tagWotsLeaf :: enc64 (idxOf κ σ w) ++ (endsD κ σ w).flatMap Vector.toList := by
  have hlen : (tagWotsLeaf :: enc64 (idxOf κ σ w) ++ (endsD κ σ w).flatMap Vector.toList).length = 4265 := by
    simp [endsD, enc64, List.length_flatMap, wotsLen, Function.comp_def, List.map_const', List.sum_replicate]
  have hel : (endsD κ σ w).length = wotsLen := by simp [endsD]
  refine List.ext_getElem (by rw [Stream.streamBytes_length, hlen]) fun p h1 h2 => ?_
  rw [Stream.streamBytes_length] at h1
  have hL : ∀ (l : List UInt8) (h : p < l.length), l[p] = l.getD p 0 := fun l h => by
    simp [List.getD_eq_getElem?_getD, h]
  rw [hL _ h2, leafMsg_get _ _ hel h1]
  simp only [Stream.streamBytes, List.getElem_map, List.getElem_range]
  rw [← msgBytes_getD _ (Nat.mod_lt _ (by norm_num)), leafW]
  have hu67 : p / 64 < 67 := by omega
  have hw := holds_wots hZ hσ (o := 399 + p / 64) (by unfold wotsSlot4; omega)
  have hend : ∀ i (hi : i < wotsLen) (q : ℕ), q < 32 →
      fb' ((endsD κ σ w).getD i default) q = fb (w (mc κ σ (endG i) (q / 16))) (q % 16) :=
    fun i hi q hq => by
      rw [fb'_eq _ hq, List.getD_eq_getElem _ _ (by rw [hel]; exact hi)]
      simp only [endsD, List.getElem_map, List.getElem_range]; exact md_get _ _ _ _ hq
  rcases (by omega : p = 0 ∨ (1 ≤ p ∧ p < 9) ∨ (64 ≤ p ∧ p % 64 < 9) ∨ (9 ≤ p % 64 ∧ p % 64 < 41) ∨
    (41 ≤ p % 64 ∧ p / 64 < 66)) with rfl | ⟨h1p, h9⟩ | ⟨h1u, h9⟩ | ⟨h9, h41⟩ | ⟨h41, h66⟩
  · -- the tag
    rw [if_pos rfl, msgBytes_getD _ (by norm_num)]
    rw [show 399 + 0 / 64 = 399 from rfl, NodeT.wotsTgt, if_neg (by norm_num), if_pos rfl] at hw
    exact (hashB1 tagWotsLeaf).msgByte_eq (p := 0) (by norm_num) (u := tagWotsLeaf) (by simp [hashB1]) hw
  · -- `j`
    rw [if_neg (by omega), if_pos h9, show p / 64 = 0 by omega, show p % 64 = 1 + (p - 1) by omega]
    exact j_byte hS hσ (t := 399 + 0) (by omega) (k := p - 1) (by omega) hj
  · -- `end41hi` of end `2(u − 1) + 1`
    rw [if_neg (by omega), if_neg (by omega)]
    have := fam_byte (f := 4) hS hσ (by decide) (t := p / 64 - 1) (by simp [NodeT.fam]; omega) (k := p % 64)
      (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
    simp only [NodeT.fam, Nat.zero_add, show 400 + (p / 64 - 1) = 399 + p / 64 by omega] at this
    rw [this, hend _ (by unfold wotsLen; omega) _ (Nat.mod_lt _ (by norm_num)),
      show (p - 9) % 32 = 184 / 8 + p % 64 by omega, show (p - 9) / 32 = 2 * (p / 64 - 1) + 1 by omega]
    simp only [endG, show (2 * (p / 64 - 1) + 1) % 2 ≠ 0 by omega, if_false,
      show (2 * (p / 64 - 1) + 1) / 2 = p / 64 - 1 by omega]
  · -- `end9` of end `2u`
    rw [if_neg (by omega), if_neg (by omega)]
    have := fam_byte (f := 2) hS hσ (by decide) (t := p / 64) (by simp [NodeT.fam]; omega) (k := p % 64 - 9)
      (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
    simp only [NodeT.fam, Nat.zero_div, Nat.zero_add, show 9 + (p % 64 - 9) = p % 64 by omega] at this
    rw [this, hend _ (by unfold wotsLen; omega) _ (Nat.mod_lt _ (by norm_num)),
      show (p - 9) % 32 = p % 64 - 9 by omega, show (p - 9) / 32 = 2 * (p / 64) by omega]
    simp only [endG, show 2 * (p / 64) % 2 = 0 by omega, if_true, show 2 * (p / 64) / 2 = p / 64 by omega]
  · -- `end41lo` of end `2u + 1`
    rw [if_neg (by omega), if_neg (by omega)]
    have := fam_byte (f := 3) hS hσ (by decide) (t := p / 64) (by simp [NodeT.fam]; omega) (k := p % 64 - 41)
      (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
    simp only [NodeT.fam, Nat.zero_div, Nat.zero_add, show 41 + (p % 64 - 41) = p % 64 by omega] at this
    rw [this, hend _ (by unfold wotsLen; omega) _ (Nat.mod_lt _ (by norm_num)),
      show (p - 9) % 32 = p % 64 - 41 by omega, show (p - 9) / 32 = 2 * (p / 64) + 1 by omega]
    simp only [endG, show (2 * (p / 64) + 1) % 2 ≠ 0 by omega, if_false,
      show (2 * (p / 64) + 1) / 2 = p / 64 by omega]

/-- **The key leaf** outputs `wotsLeaf idx ends`. -/
theorem leaf_out {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hZ : truthZ4 κ w) (hS : truthS4 κ w)
    {σ : ℕ} (hσ : σ < 2) (hj : w (mc κ σ 399 0) = w (Lc κ σ 0)) (hlf : ∀ r ∈ leafRows κ σ, r.Holds w) :
    Read.digestOf w (hc (wb κ σ 465) 2) (hc (wb κ σ 465) 3) = wotsLeaf (idxOf κ σ w) (endsD κ σ w) := by
  have hw := fun u (hu : u < 67) => holds_wots hZ hσ (o := 399 + u) (by unfold wotsSlot4; omega)
  have key := chain_digest 4265 (leafW κ σ w) ?_ ?_ ?_ ?_
  · rw [nB4265, leaf_bytes hZ hS hσ hj] at key
    rw [← readDigest_digestOf]
    exact key
  · -- `h_in = h0`
    have h0 := hw 0 (by norm_num)
    rw [show 399 + 0 = 399 from rfl, NodeT.wotsTgt, if_neg (by norm_num), if_pos rfl] at h0
    exact (hashB1 tagWotsLeaf).hIn_eq_h0 rfl h0
  · intro u hu
    rw [nB4265] at hu
    have h := hw u hu
    rcases (by omega : u = 0 ∨ (1 ≤ u ∧ u < 66) ∨ u = 66) with rfl | ⟨h1, h2⟩ | rfl
    · rw [show 399 + 0 = 399 from rfl, NodeT.wotsTgt, if_neg (by norm_num), if_pos rfl] at h
      rw [leafW, (hashB1 tagWotsLeaf).block_sound h]
      simp [ctrAt, flagAt, nB4265, hashB1, Stream.flagOf]
    · rw [NodeT.wotsTgt, if_neg (by omega), if_neg (by omega), if_pos (by omega),
        show 399 + u - 399 = u by omega] at h
      exact block_sound h
    · rw [show 399 + 66 = 465 from rfl, NodeT.wotsTgt, if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_pos rfl] at h
      rw [leafW, streamEnd41.block_sound h]
      simp [ctrAt, flagAt, nB4265, streamEnd41, Stream.flagOf]
  · intro u hu j hj
    rw [nB4265] at hu
    have e := fun h (hh : h < 2) => eqR_val hone (hlf _ (List.mem_flatMap.2 ⟨u, List.mem_range.2 (by omega),
      List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩⟩))
    simp only [Lin.ev_cell] at e
    simp only [leafW]
    rw [bitsB4_bit _ _ (by omega), bitsB4_bit _ _ (by omega)]
    have := e (j / 128) (by omega)
    unfold hc at this
    rw [show wb κ σ (399 + (u + 1)) = wb κ σ (400 + u) by unfold wb; omega, this,
      show wb κ σ (399 + u) * 128 + (256 + j) / 128 = wb κ σ (399 + u) * 128 + (2 + j / 128) by omega,
      bitN_mod _ (256 + j), bitN_mod _ j, show (256 + j) % 128 = j % 128 by omega]
  · intro p hp hp'
    rw [nB4265] at hp'
    have h := hw 66 (by norm_num)
    rw [show 399 + 66 = 465 from rfl, NodeT.wotsTgt, if_neg (by norm_num), if_neg (by norm_num),
      if_neg (by norm_num), if_pos rfl] at h
    rw [show p / 64 = 66 by omega, leafW]
    exact streamEnd41.msgByte_eq (by omega) (by simp [streamEnd41]; omega) h

end W4
end FR

end G6_FRNodeRows4WotsL

section G6_FRNodeRows4WotsP

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2; stage S-E13b, track L-circ). 3.x:
-- `FRWots.path_node`, `sigRoot_bits`.

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

end G6_FRNodeRows4WotsP

section G6_FRNodeRows4WotsD

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2; stage S-E13b, track L-circ). 3.x:
-- `FRWots.wots_sound`.

/-!
# The WOTS digits, the checksum, and a 4.1 `wots_sound`

* **`mD κ σ w`**: the digest whose 256 bits are signed child `σ`'s message digit bits (the digest
  the digit rows tie to the chain's `h_out`);
* **`msgDigits_mD`**: its 128 base-4 digits are the circuit's digits `digV`;
* **`gW_inj`**: `x` has order above 1023 (`gW ^ 255`, `^ 771`, `^ 641` are not `1`, checked by the
  kernel on 10 squarings; every divisor of `2^128 − 1` below 1024 divides 255, 771 or 641);
* **`wotsDigits_mD`**: with the checksum rows (`R_{i+1} = R_i f_i`), the 133 WOTS digits of `mD` are
  the circuit's digits;
* **`wots_sound4`**: the WOTS rows, the node's Z and S truths, its L rows and `PubCells4` give the
  contract's `SigOk vk (mD κ σ w) (readSig4 κ σ w)`.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block ProductCircuit Blake2sCircuit Kinds Stream

/-! ## The digest of the digit bits -/

/-- Half `h` of the digit bits, packed. -/
noncomputable def pkD (κ : NodeKind) (σ : ℕ) (w : Asg) (h : ℕ) : F := (pk (fun q => digC κ σ (128 * h + q)) 128).ev w

/-- **The digest of the message digit bits.** -/
noncomputable def mD (κ : NodeKind) (σ : ℕ) (w : Asg) : Digest :=
  Vector.ofFn fun i : Fin 32 => fb (pkD κ σ w (i / 16)) (i % 16)

theorem byte_digit : ∀ n < 256, ∀ t < 4,
    n / 4 ^ t % 4 = (if n.testBit (2 * t) then 1 else 0) + 2 * (if n.testBit (2 * t + 1) then 1 else 0) := by
  decide +kernel

theorem flatMap4_getD {α : Type} [Inhabited α] (f : α → List ℕ) (hf : ∀ a, (f a).length = 4) :
    ∀ (l : List α) (i : ℕ), i < 4 * l.length → (l.flatMap f).getD i 0 = (f (l.getD (i / 4) default)).getD (i % 4) 0
  | [], i, hi => by simp at hi
  | a :: l, i, hi => by
    rw [List.flatMap_cons]
    by_cases h : i < 4
    · rw [List.getD_append _ _ _ _ (by rw [hf]; exact h)]
      simp [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    · rw [List.getD_append_right _ _ _ _ (by rw [hf]; omega), hf,
        flatMap4_getD f hf l (i - 4) (by simp at hi; omega)]
      simp only [show i / 4 = (i - 4) / 4 + 1 by omega, show i % 4 = (i - 4) % 4 by omega, List.getD_cons_succ]

/-- **The message digits of `mD` are the circuit's.** -/
theorem msgDigits_mD {κ : NodeKind} {w : Asg} {σ : ℕ} (hb : ∀ p < 256, w (digC κ σ p) = 0 ∨ w (digC κ σ p) = 1)
    {i : ℕ} (hi : i < 128) : (msgDigits (mD κ σ w)).getD i 0 = digV κ σ w i := by
  rw [msgDigits, flatMap4_getD _ (fun a => by simp) _ _ (by simp; omega),
    List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [Vector.getElem_toList, mD, Vector.getElem_ofFn]
  have hk : (i / 4) % 16 < 16 := Nat.mod_lt _ (by norm_num)
  rw [byte_digit _ (UInt8.toNat_lt _) _ (Nat.mod_lt _ (by norm_num))]
  have bit : ∀ b < 2, (fb (pkD κ σ w (i / 4 / 16)) (i / 4 % 16)).toNat.testBit (2 * (i % 4) + b) =
      decide (w (digC κ σ (2 * i + b)) = 1) := fun b hb' => by
    rw [← UInt8.toNat_toBitVec, BitVec.testBit_toNat, fb_bit _ hk (by omega), bitN, pkD,
      bitF_pk w _ (by norm_num) (fun q hq => hb _ (by omega))]
    simp only [Nat.mod_eq_of_lt (show 8 * (i / 4 % 16) + (2 * (i % 4) + b) < 128 by omega)]
    rw [show 128 * (i / 4 / 16) + (8 * (i / 4 % 16) + (2 * (i % 4) + b)) = 2 * i + b by omega]
    simp [show 8 * (i / 4 % 16) + (2 * (i % 4) + b) < 128 by omega]
  have b0 := bit 0 (by norm_num)
  simp only [Nat.add_zero] at b0
  rw [b0, bit 1 (by norm_num)]
  simp [digV, bv]

/-! ## The generator's order -/

/-- Square-and-multiply on the bits (low first). -/
def bpowL (a : F) : List Bool → F
  | [] => 1
  | b :: bs => (if b then a else 1) * bpowL (a * a) bs

def bval : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bval bs

theorem bpowL_eq (a : F) (bs : List Bool) : bpowL a bs = a ^ bval bs := by
  induction bs generalizing a with
  | nil => simp [bpowL, bval]
  | cons b bs ih =>
    rw [bpowL, bval, ih, pow_add, pow_mul, sq]
    split_ifs <;> simp

theorem gW_255 : gW ^ 255 ≠ 1 := by
  rw [show 255 = bval [true, true, true, true, true, true, true, true] from rfl, ← bpowL_eq]; decide +kernel
theorem gW_771 : gW ^ 771 ≠ 1 := by
  rw [show 771 = bval [true, true, false, false, false, false, false, false, true, true] from rfl, ← bpowL_eq]
  decide +kernel
theorem gW_641 : gW ^ 641 ≠ 1 := by
  rw [show 641 = bval [true, false, false, false, false, false, false, true, false, true] from rfl, ← bpowL_eq]
  decide +kernel

theorem dvd_small : ∀ d < 1024, (2 ^ 128 - 1) % d = 0 → 255 % d = 0 ∨ 771 % d = 0 ∨ 641 % d = 0 := by
  decide +kernel

theorem gW_ne : gW ≠ 0 := by decide

/-- **`x` has order above 1023.** -/
theorem gW_order : 1023 < orderOf gW := by
  have h1 : gW ^ (2 ^ 128 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one gW gW_ne
    rwa [F.card_F] at this
  have hd := orderOf_dvd_of_pow_eq_one h1
  have hpos : 0 < orderOf gW := Nat.pos_of_dvd_of_pos hd (by norm_num)
  by_contra hle
  rcases dvd_small _ (by omega) (Nat.mod_eq_zero_of_dvd hd) with h | h | h
  · exact gW_255 (orderOf_dvd_iff_pow_eq_one.1 (Nat.dvd_of_mod_eq_zero h))
  · exact gW_771 (orderOf_dvd_iff_pow_eq_one.1 (Nat.dvd_of_mod_eq_zero h))
  · exact gW_641 (orderOf_dvd_iff_pow_eq_one.1 (Nat.dvd_of_mod_eq_zero h))

/-- **`n ↦ x^n` is injective below 1024.** -/
theorem gW_inj {a b : ℕ} (ha : a < 1024) (hb : b < 1024) (h : gW ^ a = gW ^ b) : a = b := by
  have ho := gW_order
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha h.symm (by omega)).symm
  have e : gW ^ (b - a) = 1 := by
    have : gW ^ a * gW ^ (b - a) = gW ^ a * 1 := by rw [← pow_add, Nat.add_sub_cancel' hab, ← h, mul_one]
    exact mul_left_cancel₀ (pow_ne_zero _ gW_ne) this
  have := Nat.eq_zero_of_dvd_of_lt (orderOf_dvd_of_pow_eq_one e) (by omega)
  omega

end W4
end FR

end G6_FRNodeRows4WotsD

section G6_FRNodeRows4WotsF

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2; stage S-E13b, track L-circ). 3.x:
-- `FRWots.wots_sound`.

/-!
# A 4.1 `wots_sound`: the checksum and the signature

* **`csum`**: the checksum rows (`R_{i+1} = R_i · f_i` from `1` to `1`) make the checksum digits the
  base-4 digits of `Σ (3 − dᵢ)`: `wotsDigits_mD`;
* **`wots_sound4`**: the WOTS rows of signed child `σ` (but the digest's mux, `digRows`), the node's Z
  and S truths, its L rows and `PubCells4` give the contract's `SigOk vk (mD κ σ w) σ'` for the
  signature `σ' = readSig4 κ σ w` the reader reads.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block ProductCircuit Blake2sCircuit Kinds Stream

/-! ## L's bits -/

/-- **A declared L bit is Boolean** (`lRows4`). -/
theorem lbit {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hL : ∀ r ∈ lRows4 κ, r.Holds w) {σ j : ℕ}
    (hσ : σ < κ.vslots) (hj : j < 266 + 399 + 7552 + 3) : w (Lc κ σ (299 + j)) = 0 ∨ w (Lc κ σ (299 + j)) = 1 := by
  refine boolR_val hone (hL (boolR κ (Lc κ σ (299 + j))) (List.mem_map.2 ⟨_, List.mem_flatMap.2 ⟨σ,
    List.mem_range.2 hσ, List.mem_map.2 ⟨j, List.mem_range.2 hj, ?_⟩⟩, rfl⟩))
  simp [Lc, Nat.add_assoc]

/-! ## The checksum -/

theorem fac_ev {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {c u v : F} {b₀ b₁ s : ℕ}
    (hs : w s = 1 - w b₀ * w b₁) : (fac κ c u v b₀ b₁ s).ev w = c * (1 + u * w b₀) * (1 + v * w b₁) := by
  simp only [fac, Lin.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hone, hs]
  ring

theorem bit_pow {x : F} (hx : x = 0 ∨ x = 1) (a : F) : 1 + (a - 1) * x = a ^ (if x = 1 then 1 else 0) := by
  rcases hx with rfl | rfl <;> simp

/-- **Digit `i`'s factor**: `g^3 · g⁻¹^{dᵢ}` (message digit), `g⁻¹^{4^t dᵢ}` (checksum digit `t`). -/
theorem facI_ev {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ i : ℕ} (hi : i < wotsLen)
    (hb₀ : w (digC κ σ (2 * i)) = 0 ∨ w (digC κ σ (2 * i)) = 1)
    (hb₁ : w (digC κ σ (2 * i + 1)) = 0 ∨ w (digC κ σ (2 * i + 1)) = 1)
    (hsel : ∀ r ∈ selRows κ σ, r.Holds w) :
    (facI κ σ i).ev w = if i < 128 then gW ^ 3 * gW⁻¹ ^ digV κ σ w i else gW⁻¹ ^ (4 ^ (i - 128) * digV κ σ w i) := by
  have r2 := hsel ⟨Lin.cell (digC κ σ (2 * i)), Lin.cell (digC κ σ (2 * i + 1)), (one κ).sub (Lin.cell (selC κ σ i 2))⟩
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩)
  simp only [Row.Holds, one, Lin.ev_cell, Lin.ev_sub, hone] at r2
  have hs : w (selC κ σ i 2) = 1 - w (digC κ σ (2 * i)) * w (digC κ σ (2 * i + 1)) := by
    linear_combination r2
  unfold facI
  split_ifs with h
  · rw [fac_ev hone hs]; unfold digV bv
    rcases hb₀ with h0 | h0 <;> rcases hb₁ with h1 | h1 <;> simp [h0, h1] <;> ring
  · rw [fac_ev hone hs]; unfold digV bv
    rcases hb₀ with h0 | h0 <;> rcases hb₁ with h1 | h1 <;> simp [h0, h1] <;> ring

/-- **The checksum rows telescope**: `Π_{i<133} fᵢ = 1`. -/
theorem prod_fac {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hsum : ∀ r ∈ sumRows κ σ, r.Holds w) : ∏ i ∈ Finset.range wotsLen, (facI κ σ i).ev w = 1 := by
  have key : ∀ n ≤ wotsLen, ∏ i ∈ Finset.range n, (facI κ σ i).ev w = (prL κ σ n).ev w := by
    intro n
    induction n with
    | zero => intro _; simp [prL, one, hone]
    | succ n ih =>
      intro hn
      have hr := hsum _ (List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩)
      simp only [Row.Holds] at hr
      rw [Finset.prod_range_succ, ih (by omega), hr]
  rw [key _ le_rfl]
  simp [prL, one, hone]

theorem lsum_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- **The checksum**: `Σ_{i<128} (3 − dᵢ) = Σ_{t<5} 4^t d_{128+t}`. -/
theorem csum {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hb : ∀ p < 266, w (digC κ σ p) = 0 ∨ w (digC κ σ p) = 1)
    (hsel : ∀ r ∈ selRows κ σ, r.Holds w) (hsum : ∀ r ∈ sumRows κ σ, r.Holds w) :
    ∑ i ∈ Finset.range 128, (3 - digV κ σ w i) = ∑ t ∈ Finset.range 5, 4 ^ t * digV κ σ w (128 + t) := by
  have hp := prod_fac hone hsum
  rw [show wotsLen = 128 + 5 from rfl, Finset.prod_range_add] at hp
  have hfa : ∀ i < wotsLen, (facI κ σ i).ev w = _ := fun i hi =>
    facI_ev hone hi (hb _ (by unfold wotsLen at hi; omega)) (hb _ (by unfold wotsLen at hi; omega)) hsel
  rw [Finset.prod_congr rfl fun i hi => (hfa i (by simp at hi; unfold wotsLen; omega)).trans
      (if_pos (Finset.mem_range.1 hi)),
    Finset.prod_congr rfl fun t ht => (hfa (128 + t) (by simp at ht; unfold wotsLen; omega)).trans
      (if_neg (by omega))] at hp
  have h3 : ∀ i, gW ^ 3 * gW⁻¹ ^ digV κ σ w i = gW ^ (3 - digV κ σ w i) := fun i => by
    have hd := digV_le κ σ w i
    conv_lhs => rw [show 3 = (3 - digV κ σ w i) + digV κ σ w i by omega, pow_add, mul_assoc, ← mul_pow,
      mul_inv_cancel₀ gW_ne, one_pow, mul_one]
  simp only [h3, Finset.prod_pow_eq_pow_sum, show ∀ t, 128 + t - 128 = t from fun t => by omega] at hp
  rw [inv_pow] at hp
  have := gW_inj (a := ∑ i ∈ Finset.range 128, (3 - digV κ σ w i))
    (b := ∑ t ∈ Finset.range 5, 4 ^ t * digV κ σ w (128 + t)) ?_ ?_ (mul_inv_eq_one₀ (pow_ne_zero _ gW_ne) |>.1 hp)
  · exact this
  · calc ∑ i ∈ Finset.range 128, (3 - digV κ σ w i) ≤ ∑ _i ∈ Finset.range 128, 3 :=
          Finset.sum_le_sum fun i _ => by omega
      _ < 1024 := by simp
  · have d0 := digV_le κ σ w 128; have d1 := digV_le κ σ w 129; have d2 := digV_le κ σ w 130
    have d3 := digV_le κ σ w 131; have d4 := digV_le κ σ w 132
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reducePow, zero_add]
    omega

/-- **The WOTS digits of `mD` are the circuit's.** -/
theorem wotsDigits_mD {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ}
    (hb : ∀ p < 266, w (digC κ σ p) = 0 ∨ w (digC κ σ p) = 1)
    (hsel : ∀ r ∈ selRows κ σ, r.Holds w) (hsum : ∀ r ∈ sumRows κ σ, r.Holds w) {i : ℕ} (hi : i < wotsLen) :
    (wotsDigits (mD κ σ w)).getD i 0 = digV κ σ w i := by
  have hm : msgDigits (mD κ σ w) = (List.range 128).map (digV κ σ w) := by
    refine List.ext_getElem (by simp [Wots.msgDigits_length]) fun j h1 h2 => ?_
    have := msgDigits_mD (fun p hp => hb p (by omega)) (i := j) (by simpa [Wots.msgDigits_length] using h1)
    simpa [List.getD_eq_getElem?_getD, h1] using this
  unfold wotsDigits
  rw [hm]
  by_cases h : i < 128
  · rw [List.getD_append _ _ _ _ (by simpa using h)]; simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_map, List.length_range, List.map_map]
    rw [List.getD_eq_getElem _ _ (by simp; unfold wotsLen at hi; omega)]
    simp only [List.getElem_map, List.getElem_range]
    rw [show (fun x => 3 - x) ∘ digV κ σ w = fun x => 3 - digV κ σ w x from rfl, lsum_range,
      csum hone hb hsel hsum]
    have d0 := digV_le κ σ w 128; have d1 := digV_le κ σ w 129; have d2 := digV_le κ σ w 130
    have d3 := digV_le κ σ w 131; have d4 := digV_le κ σ w 132
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reducePow, zero_add]
    rcases (by unfold wotsLen at hi; omega : i = 128 ∨ i = 129 ∨ i = 130 ∨ i = 131 ∨ i = 132) with
      rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega

/-! ## `wots_sound` at 4.1 -/

/-- **A 4.1 `wots_sound`**: on the node's Z and S truths, its L rows and `PubCells4`, the WOTS rows
of signed child `σ` (the index, selectors, chains, key leaf, path, root and checksum rows) make the
signature the reader reads (`readSig4`) sign the digest of the digit bits `mD`. -/
theorem wots_sound4 {κ : NodeKind} {w : Asg} {vk c₁ c₂ : Digest} (hZ : truthZ4 κ w) (hS : truthS4 κ w)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hP : PubCells4 κ w vk c₁ c₂) {σ : ℕ} (hσ : σ < 2) {S : ℕ → Lin}
    (hW : ∀ r ∈ wotsRows κ σ S, r.Holds w) :
    SigOk vk (mD κ σ w) (N4s.readSig4 κ σ w) = true := by
  have hone : w κ.oneCell = 1 := by
    have := congrArg List.head? hP
    simpa [cells4, Node.pubVals] using this
  have hv : 2 ≤ κ.vslots := by cases κ <;> decide
  have hb : ∀ p < 266, w (digC κ σ p) = 0 ∨ w (digC κ σ p) = 1 := fun p hp =>
    lbit hone hL (by omega) (by omega)
  have hix : ∀ r ∈ idxRows κ σ, r.Holds w := fun r h => hW r (mem_wotsRows.2 (.inl h))
  have hsel : ∀ r ∈ selRows κ σ, r.Holds w := fun r h => hW r (mem_wotsRows.2 (.inr (.inl h)))
  have hch : ∀ r ∈ chainRows κ σ, r.Holds w := fun r h => hW r (mem_wotsRows.2 (.inr (.inr (.inl h))))
  have hlf : ∀ r ∈ leafRows κ σ, r.Holds w := fun r h => hW r (mem_wotsRows.2 (.inr (.inr (.inr (.inl h)))))
  have hpa : ∀ r ∈ pathRows κ σ, r.Holds w := fun r h =>
    hW r (mem_wotsRows.2 (.inr (.inr (.inr (.inr (.inl h))))))
  have hro : ∀ r ∈ rootRows κ σ, r.Holds w := fun r h =>
    hW r (mem_wotsRows.2 (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
  have hsu : ∀ r ∈ sumRows κ σ, r.Holds w := fun r h =>
    hW r (mem_wotsRows.2 (.inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))))
  have hj := j_mirror hone hix
  have hidx : (N4s.readSig4 κ σ w).idx = idxOf κ σ w := rfl
  refine Wots.wots_sound (by rw [hidx]; exact idx_lt hone hix) (by simp [N4s.readSig4])
    (by simp [N4s.readSig4]) (ends := endsD κ σ w) (by simp [endsD]) (fun i hi => ?_)
    (cur := curD κ σ w) ?_ (fun t ht => ?_) (root_vk hone hP hσ hro)
  · have hd := wotsDigits_mD hone hb hsel hsu hi
    rw [List.getD_eq_getElem _ _ (by rw [Wots.wotsDigits_length]; exact hi)] at hd
    simp only [hd, endsD, List.getElem_map, List.getElem_range, hidx]
    rw [chain_end hone hZ hS hσ hi hj (hb _ (by unfold wotsLen at hi; omega))
      (hb _ (by unfold wotsLen at hi; omega)) hsel hch]
    have ho : Read.digestOf w (N4s.sigCell κ σ (1 + 2 * i)) (N4s.sigCell κ σ (2 + 2 * i)) = otsD κ σ w i := by
      unfold otsD otsC N4s.sigCell Lc; rw [show 1 + 2 * i + 1 = 2 + 2 * i by omega, Nat.add_zero]
    simp only [N4s.readSig4, List.getElem_map, List.getElem_range, ho]
  · rw [hidx]
    have : curB κ σ 0 = wb κ σ 465 := rfl
    simp only [curD, this]
    exact leaf_out hone hZ hS hσ hj hlf
  · have ht' : t < sigHeight := by simpa [N4s.readSig4] using ht
    rw [path_out hone hZ hS hσ ht' hix hpa, hidx]
    have hs : Read.digestOf w (N4s.sigCell κ σ (1 + 2 * wotsLen + 2 * t))
        (N4s.sigCell κ σ (2 + 2 * wotsLen + 2 * t)) = sibD κ σ w t := by
      unfold sibD sibC N4s.sigCell Lc
      rw [show 1 + 2 * wotsLen + 2 * t + 1 = 2 + 2 * wotsLen + 2 * t by omega, Nat.add_zero]
    simp only [N4s.readSig4, List.getElem_map, List.getElem_range, hs]

end W4
end FR

end G6_FRNodeRows4WotsF

section G6_FRNodeRows4WotsK

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2, R-4-m2; stage S-E13b, track L-circ).

/-!
# `Gap4.wots` from the node rows

* **`actW_eq`**: the rows' activity form is `selSum` of the sub-slot;
* **`ind_ev`**: on S-E12c's activity profile (`act_profile`), `ind j` is `[k = j]`;
* **`hDig4_mD`**: the digit rows make the digest H computes for the reader's segment count
  (`hDig4 κ σ (kOf …)`) the digest of the digit bits `mD` (an aggregate's through the `k`-mux);
* **`gap4_wots`**: on `StmtN4` and the node rows, `Gap4.wots` holds at `rd4 pf`.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c Block

theorem actW_eq (κ : NodeKind) (a i : ℕ) : actW κ a i = selSum κ (N4c.sub κ a i) := by
  simp [actW, selSum, selR, selIx, Circ.kinds, Lin.cell, List.range_succ, Nat.add_assoc]

/-- **The segment-count indicator** on the activity profile. -/
theorem ind_ev {κ : NodeKind} {a k : ℕ} {w : Asg} (hk1 : 1 ≤ k) (hkm : k ≤ κ.maxK)
    (hP : ∀ i < κ.maxK, (selSum κ (N4c.sub κ a i)).ev w = if i < k then 1 else 0) {j : ℕ} (hj1 : 1 ≤ j)
    (hjm : j ≤ κ.maxK) : (ind κ (actW κ a) j).ev w = if k = j then 1 else 0 := by
  unfold ind
  simp only [actW_eq]
  split_ifs with h1 h2 h2
  · rw [Lin.ev_sub, hP _ (by omega), hP _ (by omega), if_pos (by omega), if_neg (by omega), sub_zero]
  · rw [Lin.ev_sub, hP _ (by omega), hP _ (by omega)]
    by_cases h3 : j - 1 < k <;> by_cases h4 : j < k <;> simp [h3, h4] <;> omega
  · rw [hP _ (by omega), if_pos (by omega)]
  · rw [hP _ (by omega), if_neg (by omega)]

/-- `h_out` of a block read through its elements equals `mD` when the elements are the packed digit
bits. -/
theorem readDigest_mD {κ : NodeKind} {σ : ℕ} {w : Asg} {blk : ℕ} (h : ∀ h < 2, w (hc blk (2 + h)) = pkD κ σ w h) :
    Block.readDigest (bitsB4 w blk) 256 = mD κ σ w := by
  rw [readDigest_hc]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_ofFn, mD, h _ (show i / 16 < 2 by omega)]

/-- **The digest H computes for the reader's `k` is `mD`.** -/
theorem hDig4_mD (pf : Trace → Proof) {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) {σ : ℕ} (hσ : σ < 2)
    (hd : ∀ r ∈ digRows κ σ (actW κ (aggOf κ σ)), r.Holds w)
    (hprof : isAgg κ σ = true → ActK κ (aggOf κ σ) (N4s.kAct κ (aggOf κ σ) w) w ∧
      ∀ i < κ.maxK, (selSum κ (N4c.sub κ (aggOf κ σ) i)).ev w = if i < N4s.kAct κ (aggOf κ σ) w then 1 else 0) :
    hDig4 κ σ (kOf (N4s.rd4 pf) κ w σ) w = mD κ σ w := by
  unfold hDig4
  by_cases hA : isAgg κ σ = true
  · obtain ⟨ha, hc'⟩ := agg_of_isAgg κ hσ hA
    obtain ⟨⟨hk1, hkm, -⟩, hP⟩ := hprof hA
    have hk : kOf (N4s.rd4 pf) κ w σ = N4s.kAct κ (aggOf κ σ) w := by
      simp only [kOf, hA, if_true]; exact N4s.kA_rd4 pf κ ha w
    rw [hk]
    refine readDigest_mD fun h hh => ?_
    simp only [digRows, hA, if_true] at hd
    have hT : ∀ j < κ.maxK, w (tmC κ σ (j + 1) h) =
        (if N4s.kAct κ (aggOf κ σ) w = j + 1 then 1 else 0) * w (hc (finBlk κ σ (j + 1)) (2 + h)) := by
      intro j hj
      have r := hd _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
        List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩⟩))
      simp only [Row.Holds, Lin.ev_cell] at r
      rw [← r, ind_ev hk1 hkm hP (by omega) (by omega)]
    have e := eqR_val hone (hd _ (List.mem_append_right _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩)))
    rw [← pkD] at e
    rw [← e]
    simp only [Lin.ev, List.map_map, Function.comp_def, one_mul]
    rw [List.map_congr_left fun j hj => hT j (List.mem_range.1 hj)]
    obtain ⟨m, hm⟩ : ∃ m, κ.maxK = N4s.kAct κ (aggOf κ σ) w + m := ⟨_, (Nat.add_sub_cancel' hkm).symm⟩
    rw [hm, List.range_add, List.map_append, List.sum_append]
    obtain ⟨k', hk'⟩ : ∃ k', N4s.kAct κ (aggOf κ σ) w = k' + 1 := ⟨_, (Nat.sub_add_cancel hk1).symm⟩
    rw [hk', List.range_succ, List.map_append, List.sum_append]
    have z1 : ((List.range k').map fun j => (if k' + 1 = j + 1 then (1 : F) else 0) *
        w (hc (finBlk κ σ (j + 1)) (2 + h))).sum = 0 :=
      List.sum_eq_zero fun x hx => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        rw [if_neg (by have := List.mem_range.1 hj; omega), zero_mul]
    have z2 : ((List.range m).map fun j => (if k' + 1 = k' + 1 + j + 1 then (1 : F) else 0) *
        w (hc (finBlk κ σ (k' + 1 + j + 1)) (2 + h))).sum = 0 :=
      List.sum_eq_zero fun x hx => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
        rw [if_neg (by omega), zero_mul]
    simp only [List.map_map, Function.comp_def] at z2 ⊢
    rw [z1, z2]
    simp
  · have hk : kOf (N4s.rd4 pf) κ w σ = 0 := by simp [kOf, hA]
    rw [hk]
    refine readDigest_mD fun h hh => ?_
    simp only [digRows, hA, if_false, Bool.false_eq_true] at hd
    have e := eqR_val hone (hd _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩))
    simpa [pkD] using e

theorem readSig_rd4 (pf : Trace → Proof) (κ : NodeKind) (σ : ℕ) (w : Asg) :
    ((N4s.rd4 pf).sgn κ σ w).σ = N4s.readSig4 κ σ w := by
  simp only [N4s.rd4, N4s.sgn4]; split_ifs <;> rfl

/-- **`Gap4.wots` from the node rows**: on the node's truths and the node rows (`xRows`, folded into
slot 1's link rows), both signed children's signatures sign the digest H computes. -/
theorem gap4_wots (pf : Trace → Proof) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) (hX : ∀ r ∈ xRows κ, r.Holds w) :
    ∀ σ < 2, SigOk vk (hDig4 κ σ (kOf (N4s.rd4 pf) κ w σ) w) ((N4s.rd4 pf).sgn κ σ w).σ = true := by
  obtain ⟨hZ, hSh, hL, hE, hP⟩ := hS
  have hone := N4s.one_of_pubCells hP
  have hF := N4s.protoFit_of hone hE
  intro σ hσ
  have hW : ∀ r ∈ wotsRows κ σ (actW κ (aggOf κ σ)), r.Holds w := fun r hr => hX r (by
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl
    · exact List.mem_append_left _ (List.mem_append_left _ hr)
    · exact List.mem_append_left _ (List.mem_append_right _ hr))
  have hd : ∀ r ∈ digRows κ σ (actW κ (aggOf κ σ)), r.Holds w := fun r hr =>
    hW r (mem_wotsRows.2 (.inr (.inr (.inr (.inr (.inr (.inr (.inl hr))))))))
  rw [readSig_rd4, hDig4_mD pf hone hσ hd fun hA => ?_]
  · exact wots_sound4 hZ hSh hL hP hσ hW
  · obtain ⟨ha, -⟩ := agg_of_isAgg κ hσ hA
    have hlk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ (aggOf κ σ) i), r.Holds w :=
      fun i hi => N4s.linkRows_hold hF (sub_facts κ ha hi).1 hE
    have hK := N4s.actK_kAct hone ha hL hlk
    exact ⟨hK, act_profile hone ha hL hlk hK⟩

end W4
end FR

end G6_FRNodeRows4WotsK

section G6_FRNodeRows4Agg

-- New for `flock-recursive` (BLUEPRINT revision 4.1, R-4-m2; stage S-E13b, track L-circ).

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

end G6_FRNodeRows4Agg
