-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4, A.7; S-E12a's `HFit4`; stage S-E12c, track
-- L-circ).
import FRNodeRows4
import FRNodeCircuit4

/-!
# `hfit4`: the 4.1 nodes' M rows fit `evalM`'s variables, with distinct indices

P4b's O1 per node kind (`N4c.HFit4`): the indexed rows `nodeIRows4 κ` have distinct indices below
`2^logM` (`e2R κ`) and cells below `2^(m − 7)` (`ncR κ`). **`hfit4`** proves it for every kind,
with no evaluation of the rows:

* if the prototypes fit (`ProtoFit`: each prototype's rows lie in its `2^20` region below the
  link region, with distinct indices), slot `σ`'s rows are a prototype's moved into region `σ`
  (indices `σ·2^20 + j`, `j < 2^20 − 2^15`), its link rows take the region's link region (the
  last `2^15` rows), and the regions are disjoint and inside M (`regions4_fit`); every cell is M's
  (below `oneCell + vslots·2^20 ≤ 2^(logM+2)`), a selector bit in L or an H stream cell of the pack
  rows (below `oneCell`: `sCell_lt`);
* otherwise the rows are the one rejecting row (`rejectRows`), which fits.

`ProtoFit` holds in practice: the plan checks it on its pieces (`FRNodeRows4Plan.Plan4.hR`), and
`planOf4.inR` is `true` (S-E12c RESULT).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval

theorem protoOf_le' (κ : NodeKind) (σ : ℕ) : protoOf κ σ ≤ 1 := by unfold protoOf; split_ifs <;> omega

theorem r_rowMapC' (s : Mat) (f : ℕ → ℕ) (r : Row) : s.r (rowMapC f r) = mapC f (s.r r) := by cases s <;> rfl

/-- The cells a slot's link rows read. -/
def linkCells (κ : NodeKind) (σ : ℕ) : List ℕ :=
  [κ.oneCell, κ.oneCell + oneR σ] ++ Circ.kinds.map (κ.oneCell + selR σ ·) ++ Circ.kinds.map (selCells4 κ σ) ++
    Circ.kinds.map (κ.oneCell + selR (σ - 1) ·)

theorem linkRowsB4_cells (κ : NodeKind) (σ : ℕ) :
    ∀ r ∈ linkRowsB4 κ σ, ∀ t ∈ r.a ++ r.b ++ r.c, t.1 ∈ linkCells κ σ := by
  intro r hr t ht
  have key : ∀ x ∈ (linkRowsB4 κ σ).flatMap (fun r => (r.a ++ r.b ++ r.c).map Prod.fst), x ∈ linkCells κ σ := by
    unfold linkRowsB4 actRows4
    split_ifs <;>
      simp [selSum, Lin.sub, Lin.smul, Lin.cell, linkCells, Circ.kinds, or_assoc]
  exact key _ (List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨t, ht, rfl⟩⟩)

/-- The signed children's main chains end before M (`chBase σ + cLen ≤ mBase`, `σ < 2`). -/
theorem chBase_cLen_le (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) : N4c.chBase κ σ + N4c.cLen ≤ κ.mBase := by
  interval_cases σ <;> cases κ <;> decide

/-- **An H stream cell of a segment** (`16 e < segB`) of a signed child's stream lies below M. -/
theorem sCell_lt (κ : NodeKind) {σ e : ℕ} (hσ : σ < 2) (he : 16 * e < N4c.segB) :
    sCell (N4c.chBase κ σ) e < κ.oneCell := by
  have h := chBase_cLen_le κ hσ
  have hs : N4c.segB = 64 * N4c.cLen := by decide
  simp only [sCell, NodeKind.oneCell]
  have : e / 4 + 1 ≤ N4c.cLen := by omega
  have : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
  nlinarith

/-- The aggregate child of a slot's aggregate is a signed child (`< 2`). -/
theorem aggChild_lt (κ : NodeKind) (σ : ℕ) (hσ : σ < κ.vslots) : N4c.aggChild κ (aggSlot κ σ) < 2 := by
  cases κ <;> simp only [N4c.aggChild, aggSlot, NodeKind.hasPrev, NodeKind.vslots, NodeKind.segSlots,
    if_true, Bool.false_eq_true, if_false] at hσ ⊢ <;> omega

/-- The kinds' constants the bounds use. -/
theorem fitConsts (κ : NodeKind) :
    κ.oneCell = 3 * 2 ^ κ.dims.logM ∧ Snd.P4b.ncR κ = κ.dims.logM + 2 ∧ Snd.P4b.e2R κ = κ.dims.logM ∧
      κ.vslots * slotM4 ≤ 2 ^ κ.dims.logM ∧ κ.lBase * 128 + κ.vslots * 2 ^ 14 ≤ κ.oneCell := by
  refine ⟨oneCell_eq κ, by cases κ <;> decide, rfl, mSlots_fit κ, ?_⟩
  obtain ⟨-, h2, -, -⟩ := regions_fit κ
  have hl := lSlots_fit κ
  have hd : κ.nL / 128 * 128 = κ.nL := by cases κ <;> decide
  simp only [NodeKind.oneCell]
  nlinarith

/-- **Every slot's stream segment lies in H** (R-A′: sub-slot `i` at block `chBase + i·sBlk`): its
`cLen` blocks end before M, a later sub-slot has the spacer's two blocks before it, and the spacer's
bit cells are in its aggregate's L stride. -/
theorem packB_fit (κ : NodeKind) : ∀ σ < κ.vslots,
    (if isPrevSlot κ σ then N4c.chBase κ 0 else N4c.chBase κ (N4c.aggChild κ (aggSlot κ σ)) + subIx κ σ * N4c.sBlk) +
      N4c.cLen ≤ κ.mBase ∧
    (segIx κ σ ≠ 0 → 2 ≤ (if isPrevSlot κ σ then N4c.chBase κ 0 else
      N4c.chBase κ (N4c.aggChild κ (aggSlot κ σ)) + subIx κ σ * N4c.sBlk)) ∧
    segIx κ σ < 4 ∧ N4c.aggChild κ (aggSlot κ σ) < 2 := by
  cases κ <;> decide

theorem pinRow_cells {one x : ℕ} {c : F} {t : ℕ × F}
    (ht : t ∈ (pinRow one x c).a ++ (pinRow one x c).b ++ (pinRow one x c).c) : t.1 = one ∨ t.1 = x := by
  simp only [pinRow, Lin.sub, Lin.cell, Lin.smul, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> simp

theorem boolRow_cells {one c : ℕ} {t : ℕ × F}
    (ht : t ∈ (boolRow one c).a ++ (boolRow one c).b ++ (boolRow one c).c) : t.1 = one ∨ t.1 = c := by
  simp only [boolRow, Lin.sub, Lin.cell, Lin.smul, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> simp

theorem decRow_cells {one x : ℕ} {c : F} {cell : ℕ → ℕ} {d n : ℕ} {t : ℕ × F}
    (ht : t ∈ (decRow one x c (packAt cell d n)).a ++ (decRow one x c (packAt cell d n)).b ++
      (decRow one x c (packAt cell d n)).c) : t.1 = one ∨ t.1 = x ∨ ∃ q < n, t.1 = cell q := by
  simp only [decRow, Lin.sub, Lin.cell, Lin.smul, packAt, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.mem_cons, List.map_map, List.mem_map,
    List.mem_range, Function.comp_def] at ht
  rcases ht with rfl | rfl | rfl | ⟨q, hq, rfl⟩
  · simp
  · simp
  · simp
  · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)

/-- **The pack rows' cells**: M's `one`, the slot's selector copies, H stream cells and the spacer's L
bit cells, all below M. -/
theorem packRows4_cells (κ : NodeKind) {σ : ℕ} (hσ : σ < κ.vslots) :
    ∀ r ∈ packRows4 κ σ, ∀ t ∈ r.a ++ r.b ++ r.c,
      t.1 = κ.oneCell ∨ (∃ ι, t.1 = κ.oneCell + selR σ ι) ∨ t.1 < κ.oneCell := by
  obtain ⟨hb, h2, hs4, hσa⟩ := packB_fit κ σ hσ
  set b0 := (if isPrevSlot κ σ then N4c.chBase κ 0 else
    N4c.chBase κ (N4c.aggChild κ (aggSlot κ σ)) + subIx κ σ * N4c.sBlk) with hb0
  have hpk : packB κ σ = some (b0, if isPrevSlot κ σ then nodeGrp else segGrp) := by
    rw [hb0]; unfold packB; split_ifs <;> rfl
  obtain ⟨-, -, -, -, hL⟩ := fitConsts κ
  have hv3 : 3 ≤ κ.vslots := by cases κ <;> decide
  have hone : κ.oneCell = κ.mBase * 128 := rfl
  have hH : ∀ e, e / 4 < N4c.cLen → sCell b0 e < κ.oneCell := fun e he => by
    have : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
    simp only [sCell]; nlinarith
  have hH2 : ∀ j < 8, segIx κ σ ≠ 0 → sCell (b0 - 2) j < κ.oneCell := fun j hj hs => by
    have := h2 hs
    have h0 := hH 0 (by decide)
    simp only [sCell] at h0 ⊢
    have : j / 4 ≤ 1 := by omega
    have : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have : (b0 - 2 + j / 4) * 128 + 4 + j % 4 < b0 * 128 := by
      have : b0 - 2 + j / 4 + 1 ≤ b0 := by omega
      nlinarith
    omega
  have hC : ∀ q < 128, spC κ (N4c.aggChild κ (aggSlot κ σ)) (segIx κ σ) q < κ.oneCell := fun q hq => by
    simp only [spC]
    have : N4c.aggChild κ (aggSlot κ σ) * 2 ^ 14 ≤ 2 ^ 14 := by
      have := hσa; interval_cases (N4c.aggChild κ (aggSlot κ σ)) <;> simp
    have : 128 * (segIx κ σ - 1) ≤ 384 := by omega
    have : 3 * 2 ^ 14 ≤ κ.vslots * 2 ^ 14 := Nat.mul_le_mul_right _ hv3
    omega
  have hok : ∀ x, x = κ.oneCell ∨ x < κ.oneCell →
      x = κ.oneCell ∨ (∃ ι, x = κ.oneCell + selR σ ι) ∨ x < κ.oneCell := fun x h => by
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  intro r hr t ht
  rw [packRows4, packHead4, packWf4, hpk] at hr
  simp only [List.mem_append, List.mem_cons] at hr
  rcases hr with (rfl | hr) | hr
  · -- the kind tie
    simp only [kindRow, Lin.sub, Lin.cell, Lin.smul, Circ.kinds, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (hH 5 (by decide)))
    · exact Or.inr (Or.inl ⟨.L32, rfl⟩)
    · exact Or.inr (Or.inl ⟨.P30, rfl⟩)
    · exact Or.inr (Or.inl ⟨.N30, rfl⟩)
  · -- the head rows
    unfold headRows at hr
    split_ifs at hr with hs0
    · simp only [List.mem_singleton] at hr; subst hr
      rcases pinRow_cells ht with h | h <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hH 0 (by decide)))
    · rcases List.mem_append.1 hr with hr | hr
      rcases List.mem_append.1 hr with hr | hr
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
        have hj := List.mem_range.1 hj
        rcases pinRow_cells ht with h | h <;> rw [h]
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (hH2 j (by omega) hs0))
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
        have hq := List.mem_range.1 hq
        rcases boolRow_cells ht with h | h <;> rw [h]
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (hC q hq))
      rcases List.mem_cons.1 hr with rfl | hr
      · rcases decRow_cells ht with h | h | ⟨q, hq, h⟩ <;> rw [h]
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (hH2 6 (by norm_num) hs0))
        · exact Or.inr (Or.inr (hC q (by omega)))
      rw [List.mem_singleton] at hr; subst hr
      · rcases decRow_cells ht with h | h | ⟨q, hq, h⟩ <;> rw [h]
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (hH 0 (by decide)))
        · exact Or.inr (Or.inr (hC _ (by omega)))
  · -- the pinned elements
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    rcases pinRow_cells ht with h | h <;> rw [h]
    · exact Or.inl rfl
    · have := wfSeg_lt p hp
      have hs : N4c.segB = 64 * N4c.cLen := by decide
      exact Or.inr (Or.inr (hH _ (by omega)))

/-- **A slot's rows and link rows**: indices in its region, cells below `2^(logM + 2)`. -/
theorem slot_mem (κ : NodeKind) (hF : ProtoFit) {σ : ℕ} (hσ : σ < κ.vslots) {p : ℕ × Row}
    (hp : p ∈ slotRows4 κ σ ++ linkIRows4 κ σ) :
    (σ * slotM4 ≤ p.1 ∧ p.1 < σ * slotM4 + slotM4) ∧
      ∀ t ∈ p.2.a ++ p.2.b ++ p.2.c, t.1 < 2 ^ (κ.dims.logM + 2) := by
  obtain ⟨h1, -, -, hv, hL⟩ := fitConsts κ
  have hM : 2 ^ (κ.dims.logM + 2) = 4 * 2 ^ κ.dims.logM := by rw [pow_succ, pow_succ]; ring
  have hσ' : σ * slotM4 + slotM4 ≤ 2 ^ κ.dims.logM := by
    have := Nat.mul_le_mul_right slotM4 (Nat.succ_le_of_lt hσ); rw [Nat.succ_mul] at this; omega
  rw [hM]
  rcases List.mem_append.1 hp with hp | hp
  · -- a moved prototype row
    have hπ := protoOf_le' κ σ
    obtain ⟨hin, -⟩ := hF _ hπ
    simp only [slotRows4, absRows4, mvRows, List.map_map, List.mem_map, Function.comp_def] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨⟨hq1, hq2⟩, hc⟩ := hin q hq
    refine ⟨by simp only [mvC]; omega, fun t ht => ?_⟩
    have hs : ∀ s : Mat, ∀ t ∈ s.r (rowMapC (· + κ.oneCell) (rowMapC (mvC (protoOf κ σ) σ) q.2)),
        t.1 < 4 * 2 ^ κ.dims.logM := fun s t ht => by
      rw [r_rowMapC', r_rowMapC'] at ht
      simp only [mapC, List.map_map, List.mem_map, Function.comp_def] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have := hc s u hu
      simp only [mvC]; omega
    simp only [List.mem_append] at ht
    rcases ht with (ht | ht) | ht
    exacts [hs .a t ht, hs .b t ht, hs .c t ht]
  · -- a link row
    simp only [linkIRows4, List.mem_map] at hp
    obtain ⟨⟨r, j⟩, hj, rfl⟩ := hp
    have hjl := List.mk_mem_zipIdx_iff_getElem?.1 hj
    obtain ⟨hjn, hr⟩ := List.getElem?_eq_some_iff.1 hjl
    have hlen : j < linkN := lt_of_lt_of_le hjn (le_of_lt (linkRows4_length_le κ σ))
    have hs8 : linkN ≤ slotM4 := by decide
    refine ⟨by omega, fun t ht => ?_⟩
    have hrm : r ∈ linkRows4 κ σ := hr ▸ List.getElem_mem hjn
    have hsel : ∀ ι, selCells4 κ σ ι < κ.oneCell := fun ι => by
      have : selCells4 κ σ ι < κ.lBase * 128 + (σ + 1) * 2 ^ 14 := by
        simp only [selCells4]; cases ι <;> simp only [selIx] <;> omega
      have := Nat.mul_le_mul_right (2 ^ 14) (Nat.succ_le_of_lt hσ)
      omega
    have e2' : ∀ ι, selR σ ι < σ * slotM4 + slotM4 := fun ι => by
      simp only [selR, slotM4]; cases ι <;> simp only [selIx] <;> omega
    rcases List.mem_append.1 hrm with hrm | hrm
    swap
    · have hσM : κ.vslots * slotM4 ≤ 2 ^ κ.dims.logM := hv
      unfold extRowsC at hrm
      split_ifs at hrm with hs1 hok
      · rw [xOkK_eq] at hok
        have := List.all_eq_true.1 (List.all_eq_true.1 hok r hrm) t ht
        simp only [decide_eq_true_eq] at this
        omega
      · simp only [List.mem_singleton] at hrm; subst hrm
        simp only [rejR, Lin.cell, List.append_nil, List.mem_append, List.mem_singleton] at ht
        rcases ht with rfl | rfl <;> omega
      · simp at hrm
    rcases List.mem_append.1 hrm with hrm | hrm
    swap
    · rcases packRows4_cells κ hσ r hrm t ht with h | ⟨ι, h⟩ | h
      · rw [h]; omega
      · rw [h]; have := e2' ι; omega
      · omega
    have hc := linkRowsB4_cells κ σ r hrm t ht
    simp only [linkCells, Circ.kinds, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.mem_nil_iff, or_false] at hc
    have e1 : oneR σ < σ * slotM4 + slotM4 := by simp only [oneR, slotM4]; omega
    have e2 : ∀ ι, selR σ ι < σ * slotM4 + slotM4 := fun ι => by
      simp only [selR, slotM4]; cases ι <;> simp only [selIx] <;> omega
    have e3 : ∀ ι, selR (σ - 1) ι < σ * slotM4 + slotM4 := fun ι => by
      simp only [selR, slotM4]; cases ι <;> simp only [selIx] <;> omega
    rcases hc with h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | (have := hsel .L32; omega) | (have := hsel .P30; omega) | (have := hsel .N30; omega)
      | (have := e2 .L32; omega) | (have := e2 .P30; omega) | (have := e2 .N30; omega)
      | (have := e3 .L32; omega) | (have := e3 .P30; omega) | (have := e3 .N30; omega) | omega

/-- **A slot's indices are distinct.** -/
theorem slot_nodup (κ : NodeKind) (hF : ProtoFit) (σ : ℕ) :
    ((slotRows4 κ σ ++ linkIRows4 κ σ).map Prod.fst).Nodup := by
  obtain ⟨hin, hnd⟩ := hF _ (protoOf_le' κ σ)
  rw [List.map_append, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · simp only [slotRows4, absRows4, mvRows, List.map_map, Function.comp_def]
    rw [show (fun x : ℕ × Row => mvC (protoOf κ σ) σ x.1) = mvC (protoOf κ σ) σ ∘ Prod.fst from rfl,
      ← List.map_map]
    refine hnd.map_on fun x hx y hy h => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hy
    have := (hin q hq).1.1; have := (hin q' hq').1.1
    simp only [mvC] at h; omega
  · simp only [linkIRows4, List.map_map, Function.comp_def]
    rw [show (fun p : Row × ℕ => σ * slotM4 + slotM4 - linkN + p.2) = (σ * slotM4 + slotM4 - linkN + ·) ∘ Prod.snd
      from rfl, ← List.map_map]
    rw [List.zipIdx_map_snd]
    exact (List.nodup_range' 1).map fun a b h => by simpa using h
  · intro a ha b hb hab
    subst hab
    simp only [slotRows4, absRows4, mvRows, List.map_map, List.mem_map, Function.comp_def] at ha
    obtain ⟨q, hq, rfl⟩ := ha
    simp only [linkIRows4, List.map_map, List.mem_map, Function.comp_def] at hb
    obtain ⟨⟨r, j⟩, -, hj⟩ := hb
    have := (hin q hq).1
    simp only [mvC] at hj; omega

/-- **`hfit4`** (P4b O1 per kind, S-E12a's `HFit4`) at the 4.1 nodes' rows. -/
theorem hfit4 : N4c.HFit4 nodeIRows4 := fun κ => by
  obtain ⟨h1, hn, he, hv, -⟩ := fitConsts κ
  rw [hn, he]
  unfold nodeIRows4
  split_ifs with hF
  · refine ⟨?_, fun p hp => ?_, fun p hp t ht => ?_⟩
    · rw [List.map_flatMap]
      refine List.nodup_flatMap.2 ⟨fun σ _ => slot_nodup κ hF σ, ?_⟩
      refine (List.nodup_range).pairwise_of_forall_ne fun σ hσ σ' hσ' hne => ?_
      show List.Disjoint _ _
      rw [List.disjoint_left]
      intro x hx hx'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨p', hp', hpp⟩ := List.mem_map.1 hx'
      have a := (slot_mem κ hF (List.mem_range.1 hσ) hp).1
      have b := (slot_mem κ hF (List.mem_range.1 hσ') hp').1
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := Nat.mul_le_mul_right slotM4 (Nat.succ_le_of_lt h); rw [Nat.succ_mul] at this; omega
      · have := Nat.mul_le_mul_right slotM4 (Nat.succ_le_of_lt h); rw [Nat.succ_mul] at this; omega
    · obtain ⟨σ, hσ, hp⟩ := List.mem_flatMap.1 hp
      have hσ := List.mem_range.1 hσ
      have := (slot_mem κ hF hσ hp).1
      have := Nat.mul_le_mul_right slotM4 (Nat.succ_le_of_lt hσ); rw [Nat.succ_mul] at this; omega
    · obtain ⟨σ, hσ, hp⟩ := List.mem_flatMap.1 hp
      exact (slot_mem κ hF (List.mem_range.1 hσ) hp).2 t ht
  · refine ⟨by simp [rejectRows], fun p hp => ?_, fun p hp t ht => ?_⟩
    · simp only [rejectRows, List.mem_singleton] at hp; subst hp; exact Nat.two_pow_pos _
    · simp only [rejectRows, List.mem_singleton] at hp; subst hp
      simp only [Lin.cell, List.append_nil, List.mem_append, List.mem_singleton] at ht
      have hM : 2 ^ (κ.dims.logM + 2) = 4 * 2 ^ κ.dims.logM := by rw [pow_succ, pow_succ]; ring
      have := Nat.two_pow_pos κ.dims.logM
      rcases ht with rfl | rfl <;> simp only [h1, hM] <;> omega

/-! ## The selectors and the activity -/

/-- **Slot `σ`'s assignment for its prototype**: `w` at the slot's cells (the prototype's cells
moved to region `σ`, then made absolute), so that the slot's rows hold at `w` iff the prototype's
hold here (`holds_rowMapC`). -/
def slotAsg (κ : NodeKind) (σ : ℕ) (w : Asg) : Asg := fun c => w (mvC (protoOf κ σ) σ c + κ.oneCell)

theorem slotAsg_sel (κ : NodeKind) (σ : ℕ) (w : Asg) (ι : Kind) :
    slotAsg κ σ w (selR (protoOf κ σ) ι) = w (κ.oneCell + selR σ ι) := by
  simp only [slotAsg, mvC, selR]; congr 1; omega

theorem slotAsg_one (κ : NodeKind) (σ : ℕ) (w : Asg) :
    slotAsg κ σ w (oneR (protoOf κ σ)) = w (κ.oneCell + oneR σ) := by
  simp only [slotAsg, mvC, oneR]; congr 1; omega

/-- A slot's activity `S_σ` at `w`. -/
theorem selSum_ev (κ : NodeKind) (σ : ℕ) (w : Asg) :
    (selSum κ σ).ev w = w (κ.oneCell + selR σ .L32) + w (κ.oneCell + selR σ .P30) + w (κ.oneCell + selR σ .N30) := by
  simp [selSum, Circ.kinds, Lin.ev, Lin.cell]; ring

/-- **What a slot's link rows give** (with the L bits and `one = 1`): its `one′` is `1`, its
selector copies are bits, at most one is set, and the activity row. -/
theorem link_facts {κ : NodeKind} {σ : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (hσ : σ < κ.vslots)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ r ∈ linkRows4 κ σ, r.Holds w) :
    w (κ.oneCell + oneR σ) = 1 ∧ (∀ ι, w (κ.oneCell + selR σ ι) = 0 ∨ w (κ.oneCell + selR σ ι) = 1) ∧
      (∀ ι ι', ι ≠ ι' → w (κ.oneCell + selR σ ι) * w (κ.oneCell + selR σ ι') = 0) ∧
      ∀ r ∈ actRows4 κ σ, r.Holds w := by
  have hcopy : ∀ ι, w (κ.oneCell + selR σ ι) = w (selCells4 κ σ ι) := fun ι => by
    have := hk ⟨Lin.cell κ.oneCell, (Lin.cell (κ.oneCell + selR σ ι)).sub (Lin.cell (selCells4 κ σ ι)), []⟩
      (List.mem_append_left _ <| List.mem_append_left _ (by cases ι <;> simp [linkRowsB4, Circ.kinds]))
    simp only [Row.Holds, Lin.ev_cell, Lin.ev_sub, hone, one_mul, Lin.ev_nil] at this
    exact sub_eq_zero.1 this
  have hbit : ∀ ι, w (selCells4 κ σ ι) = 0 ∨ w (selCells4 κ σ ι) = 1 := fun ι => by
    have hm : selCells4 κ σ ι ∈ (List.range κ.vslots).flatMap (lBitCells4 κ) := by
      refine List.mem_flatMap.2 ⟨σ, List.mem_range.2 hσ, List.mem_map.2 ⟨8217 + selIx ι, ?_, ?_⟩⟩
      · simp only [List.mem_range]; cases ι <;> simp [selIx]
      · simp only [selCells4]; omega
    have := hL _ (List.mem_map.2 ⟨_, hm, rfl⟩)
    simp only [Row.Holds, Lin.ev_cell, Lin.ev_sub, hone, Lin.ev_nil] at this
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h).symm
  refine ⟨?_, fun ι => hcopy ι ▸ hbit ι, fun ι ι' hne => ?_,
    fun r hr => hk r (List.mem_append_left _ <| List.mem_append_left _ (by simp only [linkRowsB4, List.mem_append]; exact Or.inr hr))⟩
  · by_cases h0 : σ = 0
    · subst h0; simpa [oneR] using hone
    · have := hk ⟨Lin.cell κ.oneCell, (Lin.cell (κ.oneCell + oneR σ)).sub (Lin.cell κ.oneCell), []⟩
        (List.mem_append_left _ <| List.mem_append_left _ (by simp [linkRowsB4, h0]))
      simp only [Row.Holds, Lin.ev_cell, Lin.ev_sub, hone, one_mul, Lin.ev_nil] at this
      exact sub_eq_zero.1 this
  · have p := fun (x y : Kind) (h : (⟨Lin.cell (κ.oneCell + selR σ x), Lin.cell (κ.oneCell + selR σ y), []⟩ : Row) ∈
        linkRows4 κ σ) => hk _ h
    have p1 := p .L32 .P30 (List.mem_append_left _ <| List.mem_append_left _ (by simp [linkRowsB4]))
    have p2 := p .L32 .N30 (List.mem_append_left _ <| List.mem_append_left _ (by simp [linkRowsB4]))
    have p3 := p .P30 .N30 (List.mem_append_left _ <| List.mem_append_left _ (by simp [linkRowsB4]))
    simp only [Row.Holds, Lin.ev_cell, Lin.ev_nil] at p1 p2 p3
    cases ι <;> cases ι' <;> simp_all [mul_comm]

/-- **An active slot selects exactly one kind** (`SelOk` at its prototype's selector forms). -/
theorem selOk_of_act {κ : NodeKind} {σ : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (hσ : σ < κ.vslots)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ r ∈ linkRows4 κ σ, r.Holds w) (hS : (selSum κ σ).ev w = 1) :
    ∃ ι, SelOk (slotAsg κ σ w) (protoP (protoOf κ σ)) ι := by
  obtain ⟨h1, hb, hx, -⟩ := link_facts hone hσ hL hk
  obtain ⟨ι, hι⟩ := oneHot_of_rows (w := w) (one := κ.oneCell) (cells := fun ι => κ.oneCell + selR σ ι) hone
    (fun ι => hb ι) ⟨hx _ _ (by decide), hx _ _ (by decide), hx _ _ (by decide),
      by rw [hone, one_mul, ← selSum_ev, hS]⟩
  refine ⟨ι, ?_, fun ι' => ?_⟩
  · simp only [protoP, Lin.ev_cell, slotAsg_one, h1]
  · have := hι.2 ι'
    simpa only [protoP, muxP, Lin.ev_cell, slotAsg_sel] using this

/-- **An inactive slot selects none.** -/
theorem sel_zero_of_act {κ : NodeKind} {σ : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (hσ : σ < κ.vslots)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ r ∈ linkRows4 κ σ, r.Holds w) (hS : (selSum κ σ).ev w = 0) :
    ∀ ι, w (κ.oneCell + selR σ ι) = 0 := by
  obtain ⟨-, hb, hx, -⟩ := link_facts hone hσ hL hk
  rw [selSum_ev] at hS
  have a := hb .L32; have b := hb .P30; have c := hb .N30
  have ab := hx .L32 .P30 (by decide); have ac := hx .L32 .N30 (by decide)
  have bc := hx .P30 .N30 (by decide)
  intro ι
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
    simp_all <;> cases ι <;> simp_all

/-- The activity is a bit. -/
theorem selSum_bit {κ : NodeKind} {σ : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (hσ : σ < κ.vslots)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ r ∈ linkRows4 κ σ, r.Holds w) :
    (selSum κ σ).ev w = 0 ∨ (selSum κ σ).ev w = 1 := by
  obtain ⟨-, hb, hx, -⟩ := link_facts hone hσ hL hk
  rw [selSum_ev]
  have a := hb .L32; have b := hb .P30; have c := hb .N30
  have ab := hx .L32 .P30 (by decide); have ac := hx .L32 .N30 (by decide)
  have bc := hx .P30 .N30 (by decide)
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all

/-- **The previous node's slot is active**, as is every aggregate's first sub-slot. -/
theorem act_first {κ : NodeKind} {σ : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (hσ : σ < κ.vslots)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ r ∈ linkRows4 κ σ, r.Holds w)
    (hf : isPrevSlot κ σ = true ∨ subIx κ σ = 0) : (selSum κ σ).ev w = 1 := by
  obtain ⟨-, -, -, ha⟩ := link_facts hone hσ hL hk
  have hc : (isPrevSlot κ σ || subIx κ σ == 0) = true := by
    rcases hf with h | h <;> simp [h]
  have := ha ⟨Lin.cell κ.oneCell, (selSum κ σ).sub (Lin.cell κ.oneCell), []⟩ (by simp [actRows4, hc])
  simp only [Row.Holds, Lin.ev_cell, Lin.ev_sub, hone, one_mul, Lin.ev_nil] at this
  exact sub_eq_zero.1 this

/-- **A later sub-slot is active only if the one before it is.** -/
theorem act_mono {κ : NodeKind} {σ : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (hσ : σ < κ.vslots)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ r ∈ linkRows4 κ σ, r.Holds w)
    (hf : isPrevSlot κ σ = false) (hs : subIx κ σ ≠ 0) :
    (selSum κ σ).ev w * (1 - (selSum κ (σ - 1)).ev w) = 0 := by
  obtain ⟨-, -, -, ha⟩ := link_facts hone hσ hL hk
  have hc : (isPrevSlot κ σ || subIx κ σ == 0) = false := by simp [hf, hs]
  have := ha ⟨selSum κ σ, (Lin.cell κ.oneCell).sub (selSum κ (σ - 1)), []⟩ (by simp [actRows4, hc])
  simpa [Row.Holds, Lin.ev_cell, Lin.ev_sub, hone, Lin.ev_nil] using this

/-- Aggregate `a`'s sub-slot `i` as a slot: its index `i`, not the previous node's, in range. -/
theorem sub_facts (κ : NodeKind) {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) :
    N4c.sub κ a i < κ.vslots ∧ subIx κ (N4c.sub κ a i) = i ∧ isPrevSlot κ (N4c.sub κ a i) = false ∧
      (i ≠ 0 → N4c.sub κ a i - 1 = N4c.sub κ a (i - 1)) := by
  cases κ <;> simp only [N4c.nAgg, N4c.sub, NodeKind.maxK, NodeKind.hasPrev, NodeKind.segSlots,
    NodeKind.vslots, subIx, isPrevSlot, if_true, if_false, Bool.true_and, Bool.false_and,
    Bool.false_eq_true] at ha hi ⊢ <;> refine ⟨by omega, by omega, by simp, fun h => by omega⟩

/-- **The aggregate's activity profile**: with the activity rows of its sub-slots, the tie to its
`k` (`ActK`: sub-slot `k − 1` active and, below `maxK`, sub-slot `k` inactive; the pack map's
obligation) makes exactly the sub-slots `i < k` active. -/
def ActK (κ : NodeKind) (a k : ℕ) (w : Asg) : Prop :=
  1 ≤ k ∧ k ≤ κ.maxK ∧ (selSum κ (N4c.sub κ a (k - 1))).ev w = 1 ∧
    (k < κ.maxK → (selSum κ (N4c.sub κ a k)).ev w = 0)

theorem act_profile {κ : NodeKind} {a k : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (ha : a < N4c.nAgg κ)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w)
    (hK : ActK κ a k w) :
    ∀ i < κ.maxK, (selSum κ (N4c.sub κ a i)).ev w = if i < k then 1 else 0 := by
  obtain ⟨hk1, hkm, hlast, hnext⟩ := hK
  have mono : ∀ i, i + 1 < κ.maxK → (selSum κ (N4c.sub κ a (i + 1))).ev w *
      (1 - (selSum κ (N4c.sub κ a i)).ev w) = 0 := fun i hi => by
    obtain ⟨hv, hx, hp, hm⟩ := sub_facts κ ha hi
    have := act_mono hone hv hL (hk _ hi) hp (by omega)
    rwa [hm (by omega), Nat.add_sub_cancel] at this
  -- below `k`: active, downwards from `k − 1`
  have up : ∀ j, j < k → (selSum κ (N4c.sub κ a (k - 1 - j))).ev w = 1 := by
    intro j hj
    induction j with
    | zero => simpa using hlast
    | succ j ih =>
      have h := mono (k - 1 - (j + 1)) (by omega)
      rw [show k - 1 - (j + 1) + 1 = k - 1 - j by omega, ih (by omega), one_mul, sub_eq_zero] at h
      exact h.symm
  -- from `k`: inactive, upwards
  have down : ∀ j, k + j < κ.maxK → (selSum κ (N4c.sub κ a (k + j))).ev w = 0 := by
    intro j hj
    induction j with
    | zero => exact hnext (by omega)
    | succ j ih =>
      have h := mono (k + j) (by omega)
      rw [ih (by omega), sub_zero, mul_one] at h
      rwa [show k + (j + 1) = k + j + 1 by omega]
  intro i hi
  split_ifs with h
  · have := up (k - 1 - i) (by omega); rwa [show k - 1 - (k - 1 - i) = i by omega] at this
  · have := down (i - k) (by omega); rwa [show k + (i - k) = i by omega] at this

/-- **The selectors of an aggregate's sub-slots** (the selector part of `NodeResid4.selA`): under
`ActK`, every active sub-slot `i < k` selects exactly one kind of the segment group. -/
theorem selA_sel {κ : NodeKind} {a k : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (ha : a < N4c.nAgg κ)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ i < κ.maxK, ∀ r ∈ linkRows4 κ (N4c.sub κ a i), r.Holds w)
    (hK : ActK κ a k w) :
    ∀ i < k, ∃ ι, SelOk (slotAsg κ (N4c.sub κ a i) w) (protoP (protoOf κ (N4c.sub κ a i))) ι := fun i hi => by
  have him : i < κ.maxK := lt_of_lt_of_le hi hK.2.1
  have := act_profile hone ha hL hk hK i him
  rw [if_pos hi] at this
  exact selOk_of_act hone (sub_facts κ ha him).1 hL (hk i him) this

/-- **The previous node's selector** (the selector part of `NodeResid4.selP`): slot 0 selects
exactly one kind of the node group. -/
theorem selP_sel {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hp : κ.hasPrev = true)
    (hL : ∀ r ∈ lRows4 κ, r.Holds w) (hk : ∀ r ∈ linkRows4 κ 0, r.Holds w) :
    ∃ ι, SelOk (slotAsg κ 0 w) (protoP (protoOf κ 0)) ι := by
  have hv : 0 < κ.vslots := by cases κ <;> decide
  exact selOk_of_act hone hv hL hk (act_first hone hv hL hk (Or.inl (by simp [isPrevSlot, hp])))

/-! ## Controls -/

/-- (+) The rejecting rows fit, and do not hold when `one = 1` (they reject); (−) they are not
empty. -/
theorem rejectRows_ctl (κ : NodeKind) (w : Asg) (h : w κ.oneCell = 1) :
    ¬ ∀ p ∈ rejectRows κ, p.2.Holds w := fun hh => by
  have := hh _ (List.mem_singleton_self _)
  simp [Row.Holds, Lin.ev, Lin.cell, h] at this

/-- (+) Which activity row a slot gets: `N4`'s previous-node slot 0 and first sub-slot 1, and `N8`'s
aggregate-1 first sub-slot 4, are pinned active; (−) `N4`'s slot 2 and `N8`'s slot 5 get the
monotone row instead. -/
theorem actRows4_ctl :
    (isPrevSlot .N4 0 || subIx .N4 0 == 0) = true ∧ (isPrevSlot .N4 1 || subIx .N4 1 == 0) = true ∧
      (isPrevSlot .N8 4 || subIx .N8 4 == 0) = true ∧ (isPrevSlot .N4 2 || subIx .N4 2 == 0) = false ∧
      (isPrevSlot .N8 5 || subIx .N8 5 == 0) = false := by decide

/-- (−) `ActK` asks for at least one segment and at most `maxK`. -/
theorem actK_ctl (κ : NodeKind) (a : ℕ) (w : Asg) : ¬ ActK κ a 0 w ∧ ¬ ActK κ a (κ.maxK + 1) w :=
  ⟨fun h => absurd h.1 (by norm_num), fun h => absurd h.2.1 (by omega)⟩

end Rev4
end FR
