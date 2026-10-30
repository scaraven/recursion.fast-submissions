-- New for `flock-recursive` (BLUEPRINT A.10 RS1, B′ → P1.0, §5.2 row B′; stage S-G5).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessFrW0
import FRSoundnessRows
import FRSoundnessCoreFront

/-!
# The front's last phase: B′ (`κ′`) and the handoff into P1.0

* **`DRS1`** (RS1's doom at its last answer, A.10 RS1): the level-0 word is far, or `v_RS` is not
  its truth `⟨W_rs, f⁽⁰⁾⟩` (`fipL`), or (a node) a public cell of `f⁽⁰⁾` is not its public value
  (`PubOK`: `Node.PubCells` on the log's `vk`, `c₁`, `c₂`; a statement part kept in the
  background until B′).
* **`DB`** (B′'s doom, A.10 B′): the word is far, or `c₀ ≠ ⟨W₀, f⁽⁰⁾⟩` in P1.0's form
  (`trueSum e2 (lvT W₀L 0 …)`).
* **`single_B`** (`FrontObl.hsingle` at position 317): at most `10·2^128` answers escape
  (`batch_pow_bad_le` at degree 10 over `v = (v_RS, 0, pub_0 … pub_8)`, §5.2's `10/2^128`).
* **`handoff_B`** (`FrontObl.handoff`): B′'s doom is `D1 0` at P1.0's first absorb.
-/

namespace FR.Snd
open RecursionFast Finset

set_option linter.constructorNameAsVariable false

/-! ## The doom parts -/

/-- **The true `v_RS`**: `⟨W_rs, f⁽⁰⁾⟩` over level 0's `2^(nrP 0)` elements. -/
noncomputable def fipL (κ : Kind) (L es : Log) : F :=
  ∑ y ∈ range (2 ^ nrP 0 κ), wrsL κ es y * fF κ L es y

/-- **RS1's doom at its last answer**: far, `v_RS` false, or a public cell false. -/
def DRS1 (L es : Log) : Prop :=
  farL (kindOf es) L es 0 ∨ vRSL (kindOf es) es ≠ fipL (kindOf es) L es ∨ ¬ PubOK (kindOf es) L es

/-- **B′'s doom** (`D1 0` before P1.0's first round): far, or `c₀ ≠ ⟨W₀, f⁽⁰⁾⟩`. -/
def DB (L es : Log) : Prop :=
  farL (kindOf es) L es 0 ∨
    (¬ farL (kindOf es) L es 0 ∧ c₀L L es ≠ trueSum e2 (lvT W₀L 0 L es) (nrP 0 (kindOf es)))

/-! ## The algebra of B′'s batch -/

theorem nrP_zero (κ : Kind) : nrP 0 κ = κ.m - 7 := by cases κ <;> decide

theorem cells_lt {κ : Kind} : ∀ c ∈ cellsOf κ, c < 2 ^ nrP 0 κ := by
  cases κ <;> simp only [cellsOf, Kind.isNode, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil,
    false_imp_iff, implies_true]
  rw [nrP_zero]
  intro c hc
  simp only [Node.pubCells, Node.seedCell, Layout.oneCell, Layout.mBase, Layout.chainN,
    List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map] at hc
  rcases hc with rfl | ⟨σ, hσ, e, he, rfl⟩
  · decide
  · simp only [Kind.m]; omega

/-- `⟨W₀, f⁽⁰⁾⟩` is `v_RS`'s truth plus the cells' batch (`truthP1_zero`'s computation). -/
theorem ip_W0 {L es : Log} (hfar : ¬ farL (kindOf es) L es 0) :
    trueSum e2 (lvT W₀L 0 L es) (nrP 0 (kindOf es)) = algebraMap F K (fipL (kindOf es) L es +
      ∑ k ∈ range (cellsOf (kindOf es)).length,
        kpL es ^ (k + 2) * fF (kindOf es) L es ((cellsOf (kindOf es)).getD k 0)) := by
  rw [lvT, trueSum_tabs]
  have hf : ∀ y, fTab (kindOf es) L es 0 y = algebraMap F K (fF (kindOf es) L es y) := fTab_F hfar
  simp only [lvW, W₀L, hf, ← map_mul, ← map_sum]
  refine congrArg _ ?_
  simp only [w0F, add_mul, sum_add_distrib, fipL]
  refine congrArg (_ + ·) ?_
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hc : (cellsOf (kindOf es)).getD k 0 < 2 ^ nrP 0 (kindOf es) := cells_lt _ (by
    rw [List.getD_eq_getElem _ _ (mem_range.mp hk)]; exact List.getElem_mem _)
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [sum_ite_eq' (range _), if_pos (mem_range.mpr hc)]

/-! ## `hsingle` at B′ -/

/-- The batched terms: `v_RS`, `0`, and (a node) the nine public values (`v`), or their truths
(`t`). -/
def bTerms (κ : Kind) (v0 : F) (pub : List F) (i : Fin 11) : F :=
  if i.val = 0 then v0 else if κ.isNode ∧ 2 ≤ i.val then pub.getD (i.val - 2) 0 else 0

theorem bTerms_sum (κ : Kind) (v0 kp : F) (pub : List F) :
    ∑ i, kp ^ i.val * bTerms κ v0 pub i =
      v0 + if κ.isNode then kp * kp * ∑ k ∈ range 9, kp ^ k * pub.getD k 0 else 0 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, bTerms, Finset.sum_range_succ,
    Finset.sum_range_zero]
  cases κ <;> simp [Kind.isNode] <;> ring

theorem same_ext1 (L es : Log) (a : Digest) : Same L (ext1 es a) L es es.length :=
  same_append L es _

open Classical in
/-- **`hsingle` at B′** (position 317, §5.2's `10/2^128`): from RS1's doom, at most `10·2^128`
answers `κ′` make B′'s doom false. -/
theorem single_B (L es : Log) (hl : es.length = 317) :
    (univ.filter fun a => DRS1 L es ∧ ¬ DB L (ext1 es a)).card ≤ 10 * 2 ^ 128 := by
  set κ := kindOf es
  have hS : ∀ a, Same L (ext1 es a) L es 317 := fun a => hl ▸ same_ext1 L es a
  have hk : ∀ a, kindOf (ext1 es a) = κ := fun a => (hS a).kind (by norm_num)
  have hfar : ∀ a, farL κ L (ext1 es a) 0 ↔ farL κ L es 0 := fun a =>
    farL_same (hS a) (by norm_num) κ (by rw [capPos_zero]; norm_num)
  have hag : ∀ a, Agree (ext1 es a) es 317 := fun a => (hS a).1
  by_cases hf : farL κ L es 0
  · rw [filter_false_of_mem fun a _ ha => ha.2 (.inl (by rw [hk]; exact (hfar a).mpr hf)),
      card_empty]
    exact Nat.zero_le _
  by_cases hD : DRS1 L es
  swap
  · rw [filter_false_of_mem fun a _ ha => hD ha.1, card_empty]
    exact Nat.zero_le _
  set v := bTerms κ (vRSL κ es) (pubL es)
  set t := bTerms κ (fipL κ L es) ((cellsOf κ).map (fF κ L es))
  have hvt : v ≠ t := by
    intro hvt
    rcases hD with h | h | h
    · exact hf h
    · exact h (by simpa [v, t, bTerms] using congrFun hvt 0)
    · apply h
      intro hn
      have hn' : κ.isNode = true := hn
      have hc : (cellsOf κ) = Node.pubCells := by simp [cellsOf, hn']
      unfold Node.PubCells
      apply List.ext_getElem (by simp [(Node.pubCells_length (vkL es) (stL es 0) (stL es 1)).1,
        (Node.pubCells_length (vkL es) (stL es 0) (stL es 1)).2])
      intro k h1 h2
      have hk9 : k < 9 := by simpa [Node.pubCells] using h1
      have := congrFun hvt ⟨k + 2, by omega⟩
      simp only [v, t, bTerms, hn', true_and, show k + 2 ≠ 0 by omega, le_add_iff_nonneg_left,
        zero_le, ↓reduceIte, Nat.add_sub_cancel, hc] at this
      rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2, ← this]
      rfl
  refine batch_count (k := 10) _ v t hvt fun a ha => ?_
  have hnf' : ¬ farL (kindOf (ext1 es a)) L (ext1 es a) 0 := by
    rw [hk]; exact fun h => hf ((hfar a).mp h)
  have heq : c₀L L (ext1 es a) =
      trueSum e2 (lvT W₀L 0 L (ext1 es a)) (nrP 0 (kindOf (ext1 es a))) := by
    by_contra hne; exact ha.2 (.inr ⟨hnf', hne⟩)
  rw [ip_W0 hnf', c₀L] at heq
  have heq' := (algebraMap F K).injective heq
  have hkp : kpL (ext1 es a) = chF a 0 := by
    simp [kpL, fAt, ansAt, entAt, ext1, hl]
  have hcell : ∀ y, fF κ L (ext1 es a) y = fF κ L es y := fun y => by
    simp only [fF, fTab_same (hS a) (i := 0) (by norm_num) κ (by rw [capPos_zero]; norm_num)]
  have hfip : fipL κ L (ext1 es a) = fipL κ L es := by
    simp only [fipL, wrsL_congr (hag a), hcell]
  have hv : vStarL κ (ext1 es a) = vRSL κ es +
      if κ.isNode then chF a 0 * chF a 0 * pubHL es (chF a 0) else 0 := by
    simp only [vStarL, vRSL_congr (hag a), pubHL_congr ((hag a).mono (by norm_num)), hkp]
  have hw : ∑ k ∈ range (cellsOf κ).length,
      kpL (ext1 es a) ^ (k + 2) * fF κ L (ext1 es a) ((cellsOf κ).getD k 0) =
      if κ.isNode then chF a 0 * chF a 0 *
        ∑ k ∈ range 9, chF a 0 ^ k * ((cellsOf κ).map (fF κ L es)).getD k 0 else 0 := by
    rw [hkp]
    simp only [hcell]
    cases hn : κ.isNode
    · simp [cellsOf, hn]
    · have hc : cellsOf κ = Node.pubCells := by simp [cellsOf, hn]
      rw [if_pos rfl, hc, (Node.pubCells_length (vkL es) (stL es 0) (stL es 1)).1, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      have hk' : k < Node.pubCells.length := by
        rw [(Node.pubCells_length (vkL es) (stL es 0) (stL es 1)).1]; exact mem_range.mp hk
      rw [listGetD_map_lt hk']
      ring
  simp only [v, t]
  rw [bTerms_sum, bTerms_sum, ← pubHL_eq, ← hv, ← hfip, ← hw]
  simpa only [hk] using heq'

/-! ## The handoff into P1.0 -/

/-- **`FrontObl.handoff`**: B′'s doom at P1.0's first absorb is P1.0's doom `D1 0`. -/
theorem handoff_B {L es : Log} (x : ByteArray × Digest) (hl : es.length = 318) (hd : DB L es) :
    D1 W₀L c₀L 0 L (es ++ [x]) := by
  have hS : Same L (es ++ [x]) L es 318 := hl ▸ same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by norm_num)
  have hfar : farL (kindOf es) L (es ++ [x]) 0 ↔ farL (kindOf es) L es 0 :=
    farL_same hS (by norm_num) _ (by rw [capPos_zero]; norm_num)
  have hp : p1Start 0 = 318 := frW0_starts.2.2.2.2.2.2.2.2
  have h0 : hRnd (es ++ [x]) 0 = 0 := by simp [hRnd, hl, hp]
  unfold D1
  rw [h0, closeP_zero, not_not, hk, hfar]
  rcases hd with hd | ⟨hnf, hd⟩
  · exact .inl hd
  refine .inr ⟨hnf, by simp [hl, hp], ?_⟩
  have ha : ans3 (p1Start 0) (nrP 0) (es ++ [x]) = 0 := by simp [ans3, hl, hp]
  rw [ha]
  simp only [Wrong2, clR2, lvC, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero, hk]
  rwa [(frontLocal_W0 _ _ _ _ _ hS hp.le).2, lvT_same frontLocal_W0 hS (show 0 < 5 by norm_num)
    hp.le]

/-! ## Controls -/

/-- Control (positive): a far word dooms B′. -/
theorem DB_of_far {L es : Log} (h : farL (kindOf es) L es 0) : DB L es := .inl h

/-- Control (negative): on a close word with the true claim, B′ is not doomed. -/
theorem not_DB_true {L es : Log} (hnf : ¬ farL (kindOf es) L es 0)
    (hc : c₀L L es = trueSum e2 (lvT W₀L 0 L es) (nrP 0 (kindOf es))) : ¬ DB L es := by
  rintro (h | ⟨-, h⟩) <;> contradiction

/-- Control (positive): a wrong `v_RS` on a close word dooms RS1's end. -/
theorem DRS1_of_ne {L es : Log} (h : vRSL (kindOf es) es ≠ fipL (kindOf es) L es) : DRS1 L es :=
  .inr (.inl h)

/-- Control (negative): a leaf's public cells never doom (no cells are claimed). -/
theorem pubOK_leaf (L es : Log) : PubOK .P30 L es := fun h => absurd h (by decide)

end FR.Snd
