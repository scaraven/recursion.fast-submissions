-- New for lvm2 E2F (E2F-QH4): the specs of the `E2` Keccak layer's template gadgets (`LvmE2QKTB`, `LvmE2QKLayer`)
-- against the generic weight forms (`LvmQEqKeccakAlgG`) at `FE2`, and the tools to walk an `E2` template
-- (`THold2`), the `E2` counterparts of `LvmQKeccakParts`/`Parts2`/`Rounds` and `LvmQEqKeccakLayer2`.
import LvmE2QKRead
import LvmQEqKeccakAlgG
import LvmQEqKeccakGkr

/-!
# `E2` layer gadgets: specs and template walking

* `gx = x ∈ FE2`; **gadget specs** in `FE2`: `q2Proj_spec` (`V`'s projected sum), `q2Powers_spec`, `q2Inst_spec`
  (`powersF`), `q2LowTab_spec`/`q2HighTab_spec`/`q2Shift_spec` (`lowTabG`, `highTabG`, `shiftLHG`),
  `q2LaneForm_spec`, `q2Flip_spec`, `q2LaneW_spec`, `q2Index_spec` (`indexProdG gx`);
* the stream: `lv2 xv str q` (lanes `q`, `q + 1` as an `E2` value); **`packSpec2`** (`V`'s `packRoundsD` on a
  view, its proof-of-work flags) with `q2PackRounds_spec`; `q2LocalRounds_spec` (`scSpec2`, four coefficients);
* `NoA` of every `E2` gadget; **`TInv2`** (`TInv` on `THold2`) with `peelN2`, `peelL2`, `peelA2` (the
  coordinatewise assertion), `inv_end2`; the copy rows (`cp2_get`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.E2V DM

/-! ## Values -/

/-- `x` in `FE2`. -/
def gx : FE2 := FE2.ofK FK.x

theorem fe2_ofK_pow (a : FK) (n : Nat) : FE2.ofK (a ^ n) = FE2.ofK a ^ n := map_pow FE2.ofKRingHom a n

theorem getD_valF2 {xv : Src → FE} {V : Nat → FE} (l : List S2) {i : Nat} (hi : i < l.length) :
    (l.getD i default).valF xv V = (vals2 xv V l).getD i 0 := by
  simp [List.getD_eq_getElem _ _ hi, hi]

/-- `mapT2_spec` with the elements' membership. -/
theorem mapT2_spec_mem {α β : Type} {xv : Src → FE} {V : Nat → FE} {f : α → TB β} {P : α → β → Prop} :
    ∀ (as : List α), (∀ a ∈ as, ∀ n, THold2 xv V n (f a n).2 → P a (f a n).1) →
      ∀ (n : Nat), THold2 xv V n (mapT2 f as n).2 → List.Forall₂ P as (mapT2 f as n).1
  | [], _, _, _ => List.Forall₂.nil
  | a :: as, hf, n, h => by
    simp only [mapT2, tb_bind, tb_pure, List.append_nil] at h ⊢
    rw [thold2_append] at h
    exact List.Forall₂.cons (hf a (by simp) n h.1) (mapT2_spec_mem as (fun b hb => hf b (by simp [hb])) _ h.2)

/-! ## The RMFE projection and the instance weights -/

theorem projSrcs2_map {xv : Src → FE} {V : Nat → FE} (masks : List Nat) (c : Nat) (mu : List S2) :
    vals2 xv V (projSrcs2 masks mu c) =
      ((vals2 xv V mu).zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none := by
  rw [projSrcs2, vals2, List.map_filterMap, List.zip_map_left, List.filterMap_map]
  apply List.filterMap_congr
  intro p _
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
  split <;> rfl

theorem q2Proj_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) (masks : List Nat)
    (mu prod : List S2) (n : Nat) (h : THold2 xv V n (q2Proj z masks mu prod n).2) :
    (q2Proj z masks mu prod n).1.valF xv V = sumF ((List.range prod.length).map fun c =>
      sumF (((vals2 xv V mu).zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none) *
        (prod.getD c default).valF xv V) := by
  rw [sumF_eq_sum]
  refine q2SumMap_spec hz (fun c _ m hm => ?_) n h
  obtain ⟨h1, h2⟩ := (thold2_bind _ _).mp hm
  rw [tb_bind, q2Mul_spec h2, q2Sum_spec _ _ _ h1, hz, zero_add, add_zero, projSrcs2_map, sumF_eq_sum]

theorem q2Powers_spec {xv : Src → FE} {V : Nat → FE} {z s : S2} (hz : z.valF xv V = 0) :
    ∀ (k : Nat) (acc : S2) (n : Nat), THold2 xv V n (q2Powers z s acc k n).2 →
      vals2 xv V (q2Powers z s acc k n).1 = powersFromF (acc.valF xv V) (s.valF xv V) k
  | 0, _, _, _ => rfl
  | k + 1, acc, n, h => by
    simp only [q2Powers] at h ⊢
    obtain ⟨h1, h⟩ := (thold2_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold2_bind _ _).mp h
    simp only [tb_bind, tb_pure, vals2, List.map_cons, powersFromF]
    rw [← vals2, q2Powers_spec hz k _ _ h2, q2Mul_spec h1, hz, add_zero]

theorem q2Powers_length (z s : S2) : ∀ (k : Nat) (acc : S2) (n : Nat), (q2Powers z s acc k n).1.length = k
  | 0, _, _ => rfl
  | k + 1, acc, n => by simp [q2Powers, tb_bind, tb_pure, q2Powers_length z s k]

/-- **The instance weights** `μ_e = Σ_{b ∈ e} s^b` (`instWeightsF`'s terms) and `κ = Σ μ`. -/
theorem q2Inst_spec {xv : Src → FE} {V : Nat → FE} {z one s : S2} (hz : z.valF xv V = 0)
    (hone : one.valF xv V = 1) (embs : List Nat) (n : Nat) (h : THold2 xv V n (q2Inst z one s embs n).2) :
    vals2 xv V (q2Inst z one s embs n).1.1 =
        embs.map (fun e => sumF ((List.range embedBits).filterMap fun b =>
          if e.testBit b then some ((powersF (s.valF xv V) embedBits).getD b 0) else none)) ∧
    (q2Inst z one s embs n).1.2.valF xv V = (vals2 xv V (q2Inst z one s embs n).1.1).sum := by
  obtain ⟨h1, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h2, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h3, -⟩ := (thold2_bind _ _).mp h
  have epw := q2Powers_spec hz embedBits one n h1
  rw [hone] at epw
  have hlen := q2Powers_length z s embedBits one n
  have k2 := mapT2_spec (P := fun e x => S2.valF xv V x = sumF ((List.range embedBits).filterMap fun b =>
      if e.testBit b then some ((powersF (s.valF xv V) embedBits).getD b 0) else none))
    (fun e m hm => by
      rw [q2Sum_spec _ _ _ hm, hz, zero_add, sumF_eq_sum]
      congr 1
      simp only [embSrcs2, vals2, List.map_filterMap]
      apply List.filterMap_congr
      intro b hb
      split
      · simp only [Option.map_some, Option.some.injEq]
        rw [getD_valF2 _ (by rw [hlen]; simpa using hb), epw]; rfl
      · rfl) embs _ h2
  refine ⟨?_, ?_⟩
  · simp only [q2Inst, tb_bind, tb_pure]
    exact forall₂_map_eq2 k2
  · simp only [q2Inst, tb_bind, tb_pure]
    rw [q2Sum_spec _ _ _ h3, hz, zero_add]

/-! ## RMFE by 4-bit tables (W32, lead D4): values

`q2Proj4`/`q2Inst4` compute the values `q2Proj_spec`/`q2Inst_spec` state, so the layer proof only swaps the lemmas. -/

/-- A subset-sum table entry's value: `Σ_{j<L, j ∈ m} w_j`. -/
def tabVal (w : Nat → FE2) (L m : Nat) : FE2 := ∑ j ∈ Finset.range L, if m.testBit j then w j else 0

theorem tabVal_zero (w : Nat → FE2) (L : Nat) : tabVal w L 0 = 0 := by simp [tabVal]

theorem top4_facts : ∀ m < 16, 1 ≤ m → 2 ^ top4 m ≤ m ∧ (m - 2 ^ top4 m).testBit (top4 m) = false ∧
    ∀ i < 4, m.testBit i = ((m - 2 ^ top4 m).testBit i || i == top4 m) := by decide

theorem top4_lt : ∀ L < 5, ∀ m < 2 ^ L, 1 ≤ m → top4 m < L := by decide

theorem tabVal_step (w : Nat → FE2) {L m : Nat} (hL : L ≤ 4) (hm : m < 2 ^ L) (h1 : 1 ≤ m) :
    tabVal w L m = tabVal w L (m - 2 ^ top4 m) + w (top4 m) := by
  have h16 : m < 16 := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hL)
  obtain ⟨-, hb, hbits⟩ := top4_facts m h16 h1
  have hj : top4 m < L := top4_lt L (by omega) m hm h1
  unfold tabVal
  have e : ∑ j ∈ Finset.range L, (if j = top4 m then w j else 0) = w (top4 m) := by
    rw [Finset.sum_ite_eq']; exact if_pos (Finset.mem_range.mpr hj)
  rw [← e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi4 : i < 4 := by have := Finset.mem_range.mp hi; omega
  rw [hbits i hi4]
  by_cases e : i = top4 m
  · subst e; simp [hb]
  · have : (i == top4 m) = false := by simp [e]
    simp [this, e]

theorem getD_append_one {α : Type} [Inhabited α] (l : List α) (x : α) (i : Nat) :
    (l ++ [x]).getD i default = if i < l.length then l.getD i default else if i = l.length then x else default := by
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem q2TabStep_spec {xv : Src → FE} {V : Nat → FE} (v tab : List S2) (w : Nat → FE2)
    (hw : ∀ j < v.length, (v.getD j default).valF xv V = w j) (hL : v.length ≤ 4) {m : Nat} (h1 : 1 ≤ m)
    (hm : m < 2 ^ v.length) (htab : tab.length = m) (hv : ∀ i < m, (tab.getD i default).valF xv V = tabVal w v.length i)
    (n : Nat) (h : THold2 xv V n (q2TabStep v tab m n).2) :
    (q2TabStep v tab m n).1.length = m + 1 ∧
      ∀ i < m + 1, ((q2TabStep v tab m n).1.getD i default).valF xv V = tabVal w v.length i := by
  have h16 : m < 16 := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hL)
  obtain ⟨hle, -, -⟩ := top4_facts m h16 h1
  have hj : top4 m < v.length := top4_lt _ (by omega) m hm h1
  have hval : ∀ x : S2, x.valF xv V = tabVal w v.length m →
      (tab ++ [x]).length = m + 1 ∧ ∀ i < m + 1, ((tab ++ [x]).getD i default).valF xv V = tabVal w v.length i := by
    intro x hx
    refine ⟨by simp [htab], fun i hi => ?_⟩
    rw [getD_append_one]
    by_cases hi' : i < tab.length
    · rw [if_pos hi']; exact hv i (by omega)
    · rw [if_neg hi', if_pos (by omega)]; rw [show i = m by omega]; exact hx
  by_cases h0 : m - 2 ^ top4 m = 0
  · simp only [q2TabStep, h0, ↓reduceIte, tb_pure] at h ⊢
    refine hval _ ?_
    rw [hw _ hj, tabVal_step w hL hm h1, h0, tabVal_zero, zero_add]
  · simp only [q2TabStep, h0, ↓reduceIte] at h ⊢
    rw [tb_bind] at h ⊢
    rw [thold2_append] at h
    simp only [tb_pure]
    refine hval _ ?_
    have hpos : 0 < 2 ^ top4 m := Nat.two_pow_pos _
    rw [q2Add_spec h.1, hv _ (by omega), hw _ hj, ← tabVal_step w hL hm h1]

theorem q2TabGo_spec {xv : Src → FE} {V : Nat → FE} (v : List S2) (w : Nat → FE2)
    (hw : ∀ j < v.length, (v.getD j default).valF xv V = w j) (hL : v.length ≤ 4) :
    ∀ (k : Nat) (tab : List S2) (m n : Nat), 1 ≤ m → m + k ≤ 2 ^ v.length → tab.length = m →
      (∀ i < m, (tab.getD i default).valF xv V = tabVal w v.length i) → THold2 xv V n (q2TabGo v tab m k n).2 →
      (q2TabGo v tab m k n).1.length = m + k ∧
        ∀ i < m + k, ((q2TabGo v tab m k n).1.getD i default).valF xv V = tabVal w v.length i
  | 0, tab, m, n, _, _, htab, hv, _ => ⟨htab, hv⟩
  | k + 1, tab, m, n, h1, hk, htab, hv, h => by
    simp only [q2TabGo] at h ⊢
    rw [tb_bind] at h ⊢
    rw [thold2_append] at h
    obtain ⟨l1, v1⟩ := q2TabStep_spec v tab w hw hL h1 (by omega) htab hv n h.1
    have := q2TabGo_spec v w hw hL k _ (m + 1) _ (by omega) (by omega) l1 v1 h.2
    rw [show m + (k + 1) = m + 1 + k by omega]
    exact this

/-- **The subset-sum table** (`|v| ≤ 4`): `2^|v|` entries, entry `m` worth `Σ_{j ∈ m} v_j`. -/
theorem q2Tab_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) (v : List S2) (w : Nat → FE2)
    (hw : ∀ j < v.length, (v.getD j default).valF xv V = w j) (hL : v.length ≤ 4) (n : Nat)
    (h : THold2 xv V n (q2Tab z v n).2) :
    (q2Tab z v n).1.length = 2 ^ v.length ∧
      ∀ m < 2 ^ v.length, ((q2Tab z v n).1.getD m default).valF xv V = tabVal w v.length m := by
  have hp : 1 ≤ 2 ^ v.length := Nat.one_le_two_pow
  have := q2TabGo_spec v w hw hL (2 ^ v.length - 1) [z] 1 n le_rfl (by omega) rfl
    (fun i hi => by rw [show i = 0 by omega]; simp [hz, tabVal_zero]) h
  rw [show 1 + (2 ^ v.length - 1) = 2 ^ v.length by omega] at this
  exact this

theorem q2SumL_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) :
    ∀ (cs : List S2) (n : Nat), THold2 xv V n (q2SumL z cs n).2 → (q2SumL z cs n).1.valF xv V = (vals2 xv V cs).sum
  | [], n, _ => by simp [q2SumL, tb_pure, hz]
  | a :: as, n, h => by
    simp only [q2SumL] at h ⊢
    rw [q2Sum_spec _ _ _ h]; simp

/-- A `filterMap` that drops the indices `p` as an indicator sum. -/
theorem sum_filterMap_range (p : Nat → Prop) [DecidablePred p] (f : Nat → FE2) :
    ∀ k : Nat, ((List.range k).filterMap fun g => if p g then none else some (f g)).sum =
      ∑ g ∈ Finset.range k, if p g then 0 else f g
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.filterMap_append, List.sum_append, sum_filterMap_range p f k, Finset.sum_range_succ]
    by_cases hp : p k <;> simp [hp]

/-- A `zip` `filterMap` on a bit as an indicator sum. -/
theorem sum_zip_filterMap (c : Nat) : ∀ (l : List FE2) (ms : List Nat), l.length = ms.length →
    ((l.zip ms).filterMap fun p => if p.2.testBit c then some p.1 else none).sum =
      ∑ i ∈ Finset.range l.length, if (ms.getD i 0).testBit c then l.getD i 0 else 0
  | [], [], _ => by simp
  | a :: l, m :: ms, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zip_cons_cons, List.filterMap_cons, List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
      List.getD_cons_zero]
    rw [← sum_zip_filterMap c l ms h]
    by_cases hb : m.testBit c <;> simp [hb, add_comm]

/-- The range of `4k` by groups of four. -/
theorem sum_range_four (f : Nat → FE2) : ∀ k : Nat,
    ∑ i ∈ Finset.range (4 * k), f i = ∑ g ∈ Finset.range k, ∑ j ∈ Finset.range 4, f (4 * g + j)
  | 0 => by simp
  | k + 1 => by
    rw [show 4 * (k + 1) = 4 * k + 4 by ring, Finset.sum_range_add, sum_range_four f k,
      Finset.sum_range_succ (fun g => ∑ j ∈ Finset.range 4, f (4 * g + j)) k]

theorem nib4_testBit : ∀ (b0 b1 b2 b3 : Bool), ∀ j < 4, (nib4 b0 b1 b2 b3).testBit j = [b0, b1, b2, b3].getD j false := by
  decide

theorem nib4_lt (b0 b1 b2 b3 : Bool) : nib4 b0 b1 b2 b3 < 16 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem nibP_testBit (masks : List Nat) (g c : Nat) {j : Nat} (hj : j < 4) :
    (nibP masks g c).testBit j = (masks.getD (4 * g + j) 0).testBit c := by
  unfold nibP
  rw [nib4_testBit _ _ _ _ j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- Column `c`'s weight from the tables: `Σ_{i<32, bit c of mask i} μ_i`. -/
theorem colW_eq (masks : List Nat) (μw : Nat → FE2) (c : Nat) :
    ∑ g ∈ Finset.range 8, tabVal (fun j => μw (4 * g + j)) 4 (nibP masks g c) =
      ∑ i ∈ Finset.range 32, if (masks.getD i 0).testBit c then μw i else 0 := by
  rw [show (32 : Nat) = 4 * 8 from rfl, sum_range_four]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun j hj => ?_
  rw [nibP_testBit masks g c (Finset.mem_range.mp hj)]

theorem q2ProjAcc_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) (masks : List Nat)
    (tabs : List (List S2)) (hl : tabs.length = 8) (μw : Nat → FE2)
    (ht : ∀ g < 8, ∀ m < 16, ((tabs.getD g []).getD m default).valF xv V = tabVal (fun j => μw (4 * g + j)) 4 m) :
    ∀ (ps : List S2) (c : Nat) (acc : S2) (n : Nat), THold2 xv V n (q2ProjAcc z masks tabs ps c acc n).2 →
      (q2ProjAcc z masks tabs ps c acc n).1.valF xv V = acc.valF xv V + ((List.range ps.length).map fun k =>
        (∑ i ∈ Finset.range 32, if (masks.getD i 0).testBit (c + k) then μw i else 0) * (ps.getD k default).valF xv V).sum
  | [], _, acc, _, _ => by simp [q2ProjAcc, tb_pure]
  | p :: ps, c, acc, n, h => by
    have hsrc : (vals2 xv V (nibSrcsP masks tabs c)).sum =
        ∑ i ∈ Finset.range 32, if (masks.getD i 0).testBit c then μw i else 0 := by
      have e : vals2 xv V (nibSrcsP masks tabs c) = (List.range 8).filterMap fun g => if nibP masks g c = 0 then none
          else some (((tabs.getD g []).getD (nibP masks g c) default).valF xv V) := by
        simp only [nibSrcsP, hl, vals2, List.map_filterMap]
        apply List.filterMap_congr
        intro g _
        split <;> rfl
      rw [← colW_eq, e, sum_filterMap_range (fun g => nibP masks g c = 0)
        (fun g => ((tabs.getD g []).getD (nibP masks g c) default).valF xv V) 8]
      refine Finset.sum_congr rfl fun g hg => ?_
      have hg8 := Finset.mem_range.mp hg
      split
      · next h0 => rw [h0, tabVal_zero]
      · rw [ht g hg8 _ (by unfold nibP; exact nib4_lt _ _ _ _)]
    have hsplit : ∀ X : FE2, ((List.range (p :: ps).length).map fun k =>
        (∑ i ∈ Finset.range 32, if (masks.getD i 0).testBit (c + k) then μw i else 0) *
          ((p :: ps).getD k default).valF xv V).sum =
        (∑ i ∈ Finset.range 32, if (masks.getD i 0).testBit c then μw i else 0) * p.valF xv V +
        ((List.range ps.length).map fun k =>
          (∑ i ∈ Finset.range 32, if (masks.getD i 0).testBit (c + 1 + k) then μw i else 0) *
            (ps.getD k default).valF xv V).sum := fun _ => by
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      refine congrArg₂ (· + ·) (by simp only [Nat.add_zero, List.getD_cons_zero])
        (congrArg List.sum (List.map_congr_left fun k _ => ?_))
      simp only [Function.comp_apply, List.getD_cons_succ]
      rw [show c + (k + 1) = c + 1 + k by omega]
    rw [hsplit 0]
    by_cases he : (nibSrcsP masks tabs c).isEmpty = true
    · simp only [q2ProjAcc, he, ↓reduceIte] at h ⊢
      have h0 : (vals2 xv V (nibSrcsP masks tabs c)).sum = 0 := by
        rw [List.isEmpty_iff.mp he]; rfl
      rw [hsrc] at h0
      rw [q2ProjAcc_spec hz masks tabs hl μw ht ps (c + 1) acc n h, h0, zero_mul, zero_add]
    · simp only [q2ProjAcc, he, Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [tb_bind] at h ⊢
      rw [thold2_append] at h
      rw [tb_bind] at h ⊢
      rw [thold2_append] at h
      rw [q2ProjAcc_spec hz masks tabs hl μw ht ps (c + 1) _ _ h.2.2, q2Mul_spec h.2.1, q2SumL_spec hz _ _ h.1, hsrc]
      ring

/-- **The projection by tables** has `q2Proj`'s value (`|μ| = |masks| = 32`). -/
theorem q2Proj4_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) (masks : List Nat)
    (mu prod : List S2) (hmu : mu.length = 32) (hm : masks.length = 32) (n : Nat)
    (h : THold2 xv V n (q2Proj4 z masks mu prod n).2) :
    (q2Proj4 z masks mu prod n).1.valF xv V = sumF ((List.range prod.length).map fun c =>
      sumF (((vals2 xv V mu).zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none) *
        (prod.getD c default).valF xv V) := by
  rw [show q2Proj4 z masks mu prod = (mapT2 (fun g => q2Tab z ((mu.drop (4 * g)).take 4)) (List.range 8) >>= fun tabs =>
    q2ProjAcc z masks tabs prod 0 z) from rfl] at h ⊢
  rw [tb_bind] at h ⊢
  rw [thold2_append] at h
  set μw : Nat → FE2 := fun i => (vals2 xv V mu).getD i 0
  have k1 := mapT2_spec_mem (P := fun g t => g < 8 → ∀ m < 16, (t.getD m default).valF xv V =
      tabVal (fun j => μw (4 * g + j)) 4 m)
    (List.range 8) (fun g hg m hm g8 => by
      have hlen : ((mu.drop (4 * g)).take 4).length = 4 := by simp [hmu]; omega
      have := (q2Tab_spec hz ((mu.drop (4 * g)).take 4) (fun j => μw (4 * g + j)) (fun j hj => by
          rw [hlen] at hj
          rw [getD_valF2 _ (by rw [hlen]; exact hj)]
          simp only [μw, vals2, List.map_take, List.map_drop]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj,
            List.getElem?_drop]) (by rw [hlen]) m hm).2
      rw [hlen] at this
      exact this) n h.1
  have hl : (mapT2 (fun g => q2Tab z ((mu.drop (4 * g)).take 4)) (List.range 8) n).1.length = 8 := by
    rw [mapT2_length]; simp
  generalize (mapT2 (fun g => q2Tab z ((mu.drop (4 * g)).take 4)) (List.range 8) n).1 = tabs at h k1 hl ⊢
  have ht : ∀ g < 8, ∀ m < 16, ((tabs.getD g []).getD m default).valF xv V =
      tabVal (fun j => μw (4 * g + j)) 4 m := fun g hg m hm => by
    have hg' : g < tabs.length := by rw [hl]; exact hg
    have := (List.forall₂_iff_get.mp k1).2 g (by simpa using hg) hg'
    simp only [List.get_eq_getElem, List.getElem_range] at this
    rw [List.getD_eq_getElem tabs [] hg']
    exact this hg m hm
  have e := q2ProjAcc_spec hz masks tabs hl μw ht prod 0 z _ h.2
  rw [e, hz, zero_add, sumF_eq_sum]
  refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
  rw [Nat.zero_add, sumF_eq_sum, sum_zip_filterMap c _ _ (by rw [List.length_map, hmu, hm]), List.length_map, hmu]

/-- `embNib`'s bits are the embedding's (`j` below the group's size). -/
theorem embNib_testBit (pw : List S2) (e g : Nat) {j : Nat} (hj : j < ((pw.drop (4 * g)).take 4).length) :
    (embNib pw e g).testBit j = e.testBit (4 * g + j) := by
  unfold embNib
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, decide_eq_true hj, Bool.true_and, add_comm]

/-- A `filterMap` that keeps the indices `p` as an indicator sum. -/
theorem sum_filterMap_range_pos (p : Nat → Prop) [DecidablePred p] (f : Nat → FE2) :
    ∀ k : Nat, ((List.range k).filterMap fun g => if p g then some (f g) else none).sum =
      ∑ g ∈ Finset.range k, if p g then f g else 0
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.filterMap_append, List.sum_append, sum_filterMap_range_pos p f k, Finset.sum_range_succ]
    by_cases hp : p k <;> simp [hp]

/-- The 53 embedding bits by the 14 groups (13 of four, one of one). -/
theorem sum_range_53 (f : Nat → FE2) (len : Nat → Nat) (hlen : ∀ g, len g = min 4 (53 - 4 * g)) :
    ∑ g ∈ Finset.range 14, ∑ j ∈ Finset.range (len g), f (4 * g + j) = ∑ b ∈ Finset.range 53, f b := by
  rw [Finset.sum_range_succ, hlen 13, show min 4 (53 - 4 * 13) = 1 from rfl, Finset.sum_range_one,
    Finset.sum_congr rfl (g := fun g => ∑ j ∈ Finset.range 4, f (4 * g + j)) (fun g hg => by
      rw [hlen g, show min 4 (53 - 4 * g) = 4 by have := Finset.mem_range.mp hg; omega]),
    ← sum_range_four f 13, Finset.sum_range_succ f 52]

/-- **The instance weights by tables** have `q2Inst`'s values (`embedBits = 53`, 14 groups). -/
theorem q2Inst4_spec {xv : Src → FE} {V : Nat → FE} {z one s : S2} (hz : z.valF xv V = 0)
    (hone : one.valF xv V = 1) (embs : List Nat) (n : Nat) (h : THold2 xv V n (q2Inst4 z one s embs n).2) :
    vals2 xv V (q2Inst4 z one s embs n).1.1 =
        embs.map (fun e => sumF ((List.range embedBits).filterMap fun b =>
          if e.testBit b then some ((powersF (s.valF xv V) embedBits).getD b 0) else none)) ∧
    (q2Inst4 z one s embs n).1.2.valF xv V = (vals2 xv V (q2Inst4 z one s embs n).1.1).sum := by
  rw [show q2Inst4 z one s embs = (q2Powers z s one embedBits >>= fun pw =>
    mapT2 (fun g => q2Tab z ((pw.drop (4 * g)).take 4)) (List.range 14) >>= fun tabs =>
    mapT2 (fun e => q2SumL z ((List.range 14).filterMap fun g =>
      if embNib pw e g = 0 then none else some ((tabs.getD g []).getD (embNib pw e g) default))) embs >>= fun mu =>
    q2SumL z mu >>= fun kappa => pure (mu, kappa)) from rfl] at h ⊢
  rw [tb_bind] at h ⊢
  rw [thold2_append] at h
  have epw := q2Powers_spec hz embedBits one n h.1
  rw [hone] at epw
  have hlen := q2Powers_length z s embedBits one n
  generalize hP : q2Powers z s one embedBits n = P at h epw hlen ⊢
  set pw := P.1 with hpw
  set pwv : Nat → FE2 := fun b => (powersF (s.valF xv V) embedBits).getD b 0
  have hlg : ∀ g, ((pw.drop (4 * g)).take 4).length = min 4 (53 - 4 * g) := fun g => by
    simp [hlen, embedBits]
  rw [tb_bind] at h ⊢
  rw [thold2_append] at h
  have k1 := mapT2_spec_mem (P := fun g t => g < 14 → ∀ m < 2 ^ ((pw.drop (4 * g)).take 4).length,
      (t.getD m default).valF xv V = tabVal (fun j => pwv (4 * g + j)) ((pw.drop (4 * g)).take 4).length m)
    (List.range 14) (fun g hg m hm g14 mm hmm => by
      refine (q2Tab_spec hz ((pw.drop (4 * g)).take 4) (fun j => pwv (4 * g + j)) (fun j hj => ?_)
        (by rw [hlg]; omega) m hm).2 mm hmm
      rw [getD_valF2 _ hj]
      have hj' : j < 4 ∧ 4 * g + j < pw.length := by rw [hlg] at hj; rw [hlen]; simp [embedBits]; omega
      simp only [vals2, List.map_take, List.map_drop]
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj'.1, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
        ← vals2, epw]
      rfl) _ h.2.1
  have hl : (mapT2 (fun g => q2Tab z ((pw.drop (4 * g)).take 4)) (List.range 14) (n + P.2.length)).1.length = 14 := by
    rw [mapT2_length]; simp
  generalize (mapT2 (fun g => q2Tab z ((pw.drop (4 * g)).take 4)) (List.range 14) (n + P.2.length)).1 = tabs
    at h k1 hl ⊢
  have ht : ∀ g < 14, ∀ m < 2 ^ ((pw.drop (4 * g)).take 4).length, ((tabs.getD g []).getD m default).valF xv V =
      tabVal (fun j => pwv (4 * g + j)) ((pw.drop (4 * g)).take 4).length m := fun g hg m hm => by
    have hg' : g < tabs.length := by rw [hl]; exact hg
    have := (List.forall₂_iff_get.mp k1).2 g (by simpa using hg) hg'
    simp only [List.get_eq_getElem, List.getElem_range] at this
    rw [List.getD_eq_getElem tabs [] hg']
    exact this hg m hm
  rw [tb_bind] at h ⊢
  rw [thold2_append] at h
  have k2 := mapT2_spec (P := fun e x => S2.valF xv V x = sumF ((List.range embedBits).filterMap fun b =>
      if e.testBit b then some (pwv b) else none))
    (fun e m hm => by
      rw [q2SumL_spec hz _ _ hm, sumF_eq_sum]
      have ev : vals2 xv V ((List.range 14).filterMap fun g => if embNib pw e g = 0 then none
          else some ((tabs.getD g []).getD (embNib pw e g) default)) = (List.range 14).filterMap fun g =>
          if embNib pw e g = 0 then none else some (((tabs.getD g []).getD (embNib pw e g) default).valF xv V) := by
        simp only [vals2, List.map_filterMap]
        apply List.filterMap_congr
        intro g _
        split <;> rfl
      rw [ev, sum_filterMap_range (fun g => embNib pw e g = 0)
        (fun g => ((tabs.getD g []).getD (embNib pw e g) default).valF xv V) 14,
        sum_filterMap_range_pos (fun b => e.testBit b = true) pwv embedBits]
      rw [show embedBits = 53 from rfl, ← sum_range_53 (fun b => if e.testBit b = true then pwv b else 0)
        (fun g => ((pw.drop (4 * g)).take 4).length) hlg]
      refine Finset.sum_congr rfl fun g hg => ?_
      have hg14 := Finset.mem_range.mp hg
      have hnib : embNib pw e g < 2 ^ ((pw.drop (4 * g)).take 4).length := Nat.mod_lt _ (Nat.two_pow_pos _)
      split
      · next h0 =>
        have e0 : tabVal (fun j => pwv (4 * g + j)) ((pw.drop (4 * g)).take 4).length (embNib pw e g) = 0 := by
          rw [h0, tabVal_zero]
        refine e0.symm.trans ?_
        unfold tabVal
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [embNib_testBit pw e g (Finset.mem_range.mp hj)]
      · rw [ht g hg14 _ hnib]
        unfold tabVal
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [embNib_testBit pw e g (Finset.mem_range.mp hj)]) embs _ h.2.2.1
  refine ⟨?_, ?_⟩
  · simp only [tb_bind, tb_pure]
    exact forall₂_map_eq2 k2
  · simp only [tb_bind, tb_pure]
    rw [q2SumL_spec hz _ _ ((thold2_bind _ _).mp h.2.2.2).1]

/-! ## The shift tables, lane forms, flips, lane weights, `indexMle` -/

theorem q2LowTab_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {ta tb : List S2}
    {a b : List FE2} (hta : vals2 xv V ta = eqKernelF (a.take 3)) (htb : vals2 xv V tb = eqKernelF (b.take 3))
    (ha : 3 ≤ a.length) (hb : 3 ≤ b.length) (c rl : Nat) (n : Nat) (h : THold2 xv V n (q2LowTab z ta tb c rl n).2) :
    (q2LowTab z ta tb c rl n).1.valF xv V = lowTabG a b c rl := by
  have la : ta.length = 8 := by
    have := congrArg List.length hta; rw [List.length_map, eqKernelF_length] at this; simp [this, ha]
  have lb : tb.length = 8 := by
    have := congrArg List.length htb; rw [List.length_map, eqKernelF_length] at this; simp [this, hb]
  rw [lowTabG, sumF_eq_sum]
  refine q2SumMap_spec hz (fun zz hzz m hm => ?_) n h
  by_cases hc : (zz + rl) / 8 = c
  · simp only [hc, if_true] at hm ⊢
    rw [q2Mul_spec hm, hz, add_zero, getD_valF2 _ (by (clear * - zz tb ta a b c rl lb hzz; omega)), getD_valF2 _ (by rw [la]; exact Nat.mod_lt _ (by (clear * - ta tb a b c rl zz; omega))),
      hta, htb]
    rfl
  · simp only [hc, if_false] at hm ⊢
    exact hz

theorem q2HighTab_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {ta tb : List S2}
    {a b : List FE2} (hta : vals2 xv V ta = eqKernelF (a.drop 3)) (htb : vals2 xv V tb = eqKernelF (b.drop 3))
    (ha : a.length = 6) (hb : b.length = 6) (k : Nat) (n : Nat) (h : THold2 xv V n (q2HighTab z ta tb k n).2) :
    (q2HighTab z ta tb k n).1.valF xv V = highTabG a b k := by
  have la : ta.length = 8 := by
    have := congrArg List.length hta; rw [List.length_map, eqKernelF_length] at this; simp [this, ha]
  have lb : tb.length = 8 := by
    have := congrArg List.length htb; rw [List.length_map, eqKernelF_length] at this; simp [this, hb]
  rw [highTabG, sumF_eq_sum]
  refine q2SumMap_spec hz (fun zz hzz m hm => ?_) n h
  rw [q2Mul_spec hm, hz, add_zero, getD_valF2 _ (by (clear * - zz tb ta a b lb hzz; omega)), getD_valF2 _ (by rw [la]; exact Nat.mod_lt _ (by (clear * - ta tb a b zz; omega))),
    hta, htb]
  rfl

theorem q2Shift_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {L0 L1 H : List S2}
    {a b : List FE2} (h0 : vals2 xv V L0 = (List.range 8).map (lowTabG a b 0))
    (h1 : vals2 xv V L1 = (List.range 8).map (lowTabG a b 1)) (hH : vals2 xv V H = (List.range 8).map (highTabG a b))
    {r : Nat} (hr : r < 64) (n : Nat) (h : THold2 xv V n (q2Shift z L0 L1 H r n).2) :
    (q2Shift z L0 L1 H r n).1.valF xv V = shiftLHG a b r := by
  have l0 : L0.length = 8 := by simpa using congrArg List.length h0
  have l1 : L1.length = 8 := by simpa using congrArg List.length h1
  have lH : H.length = 8 := by simpa using congrArg List.length hH
  obtain ⟨g1, g2⟩ := (thold2_bind _ _).mp h
  rw [q2Shift, tb_bind, q2Mul_spec g2, q2Mul_spec g1, hz, add_zero,
    getD_valF2 _ (by rw [l0]; exact Nat.mod_lt _ (by (clear * - L0 L1 H r; omega))), getD_valF2 _ (by rw [lH]; (clear * - r L0 L1 H hr; omega)),
    getD_valF2 _ (by rw [l1]; exact Nat.mod_lt _ (by (clear * - L0 L1 H r; omega))), getD_valF2 _ (by rw [lH]; exact Nat.mod_lt _ (by (clear * - L0 L1 H r; omega))),
    h0, h1, hH]
  simp [List.getD_eq_getElem?_getD, Nat.mod_lt _ (show 0 < 8 by (clear * - L0 L1 H r; omega)), show r / 8 < 8 by (clear * - r L0 L1 H hr; omega),
    Nat.mod_lt _ (show 0 < 8 by (clear * - L0 L1 H r; omega)), shiftLHG]

theorem q2LaneForm_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {B : List S2}
    (hB : 25 ≤ B.length) (R : Nat → S2) {l : Nat} (hl : l < 25) (n : Nat)
    (h : THold2 xv V n (q2LaneForm z B R l n).2) :
    (q2LaneForm z B R l n).1.valF xv V = laneFormF (vals2 xv V B) (fun s => (R s).valF xv V) l := by
  obtain ⟨g1, h'⟩ := (thold2_bind _ _).mp h
  obtain ⟨g2, g3⟩ := (thold2_bind _ _).mp h'
  have hp : ∀ x y, x < 5 → y < 5 → keccakPi (x + 5 * y) < B.length := fun x y hx hy =>
    lt_of_lt_of_le (kPi_lt _ (by (clear * - x y B l hx hy; omega))) hB
  rw [q2LaneForm, tb_bind, tb_bind, q2Dot_spec _ _ _ g3, q2Dot_spec _ _ _ g2, q2Mul_spec g1, hz, add_zero,
    laneFormF, sumF_eq_sum, sumF_eq_sum, getD_valF2 _ (lt_of_lt_of_le (kPi_lt _ hl) hB)]
  simp only [List.map_map, Function.comp_def]
  congr 2
  · congr 1
    apply List.map_congr_left
    intro y hy
    rw [getD_valF2 _ (hp _ _ (Nat.mod_lt _ (by (clear * - B l; omega))) (List.mem_range.mp hy))]
  · apply List.map_congr_left
    intro y hy
    rw [getD_valF2 _ (hp _ _ (Nat.mod_lt _ (by (clear * - B l; omega))) (List.mem_range.mp hy))]

theorem q2Flip_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {B A : List S2}
    (hB : 25 ≤ B.length) (hA : A.length = 64) (i n : Nat) (h : THold2 xv V n (q2Flip z B A i n).2) :
    (q2Flip z B A i n).1.valF xv V = flipFormG (vals2 xv V B) (fun s => (vals2 xv V A).getD s 0) i := by
  rw [q2Flip, q2LaneForm_spec hz hB _ (by (clear * - B A; omega)) n h, flipFormG]
  congr 1
  funext s
  rw [getD_valF2 _ (by rw [hA]; exact Nat.mod_lt _ (by (clear * - B A; omega)))]

theorem q2LaneW_spec {xv : Src → FE} {V : Nat → FE} {eL : List S2} (hL : 25 ≤ eL.length) (beta : S2) (n : Nat)
    (h : THold2 xv V n (q2LaneW eL beta n).2) :
    vals2 xv V (q2LaneW eL beta n).1 = (List.range 25).map fun l => (vals2 xv V eL).getD l 0 + beta.valF xv V *
      ((vals2 xv V eL).getD (keccakAlong (64 * l) 4 / 64) 0 + beta.valF xv V *
        (vals2 xv V eL).getD (keccakAlong (64 * l) 3 / 64) 0) := by
  refine forall₂_map_eq2 (mapT2_spec_mem (P := fun l x => S2.valF xv V x = _) _ (fun l hl m hm => ?_) n h)
  have hl' := List.mem_range.mp hl
  obtain ⟨g1, g2⟩ := (thold2_bind _ _).mp hm
  rw [tb_bind, q2Mul_spec g2, q2Mul_spec g1, getD_valF2 (i := l) eL (by (clear * - l eL hL hl'; omega)),
    getD_valF2 (i := keccakAlong (64 * l) 3 / 64) eL (lt_of_lt_of_le (along_lt l hl').1 hL),
    getD_valF2 (i := keccakAlong (64 * l) 4 / 64) eL (lt_of_lt_of_le (along_lt l hl').2 hL)]
  ring

theorem q2IndexStep_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) (k : Nat) (acc r : S2)
    (n : Nat) (h : THold2 xv V n (q2IndexStep z k acc r n).2) :
    (q2IndexStep z k acc r n).1.valF xv V = acc.valF xv V * (1 + r.valF xv V * (1 + gx ^ (2 ^ k))) := by
  obtain ⟨g1, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨g2, g3⟩ := (thold2_bind _ _).mp h
  rw [q2IndexStep, tb_bind, tb_bind, q2Mul_spec g3, q2One_spec g2, q2Scale_spec g1, hz, add_zero, fe2_ofK_add,
    fe2_ofK_one, fe2_ofK_pow, gx]
  ring

/-- `indexProdG` of `rs` from coordinate `k`: `Π_t (1 + r_t·(1 + g^(2^(k + t))))`. -/
theorem q2Index_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) :
    ∀ (rs : List S2) (k : Nat) (acc : S2) (n : Nat), THold2 xv V n (q2Index z k acc rs n).2 →
      (q2Index z k acc rs n).1.valF xv V =
        acc.valF xv V * ∏ t ∈ Finset.range rs.length, (1 + (vals2 xv V rs).getD t 0 * (1 + gx ^ (2 ^ (k + t))))
  | [], k, acc, n, _ => by simp [q2Index, tb_pure]
  | r :: rs, k, acc, n, h => by
    obtain ⟨g1, g2⟩ := (thold2_bind _ _).mp h
    have e1 := q2IndexStep_spec hz k acc r n g1
    have e2 := q2Index_spec hz rs (k + 1) _ _ g2
    rw [e1] at e2
    show (q2Index z (k + 1) (q2IndexStep z k acc r n).1 rs (n + (q2IndexStep z k acc r n).2.length)).1.valF xv V = _
    rw [e2, List.length_cons, Finset.prod_range_succ']
    simp only [vals2, List.map_cons, List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    conv_rhs => rw [Finset.prod_congr rfl (fun t _ => by rw [show k + (t + 1) = k + 1 + t by (clear * - k t; omega)])]
    ring

/-! ## The stream -/

/-- Lanes `q`, `q + 1` of a loop's iteration fixed by `xv`, as an `E2` value. -/
def lv2 (xv : Src → FE) (str : List Nat) (q : Nat) : FE2 :=
  ⟨(xv (.ext ⟨.K, q, str⟩)).c₀, (xv (.ext ⟨.K, q + 1, str⟩)).c₀⟩

theorem lane2_valF (xv : Src → FE) (V : Nat → FE) (q : Nat) (str : List Nat) :
    (lane2 q str).valF xv V = lv2 xv str q := rfl

/-- **`V`'s `packRoundsD` on a view** (`v` the `E2` view, `va` the `E` answers' view): value, scale, challenges,
end position, proof-of-work flags. Round `14` lanes: `c₁, c₂`, the nonce, the answer. -/
def packSpec2 (v : Nat → FE2) (va : Nat → FE) (g : Nat) : List FE2 → FE2 → FE2 → Nat → FE2 × FE2 × List FE2 × Nat × Bool
  | [], value, scale, p => (value, scale, [], p, true)
  | r :: rs, value, scale, p =>
    let msg := (value + r * sumF (scalars2 v (p + 40) 2)) :: scalars2 v (p + 40) 2
    let ch := e2OfFE (va (p + 80))
    let res := packSpec2 v va g rs ((1 + r + ch) * polyEvalF msg ch) (scale * (1 + r + ch)) (p + 112)
    (res.1, res.2.1, ch :: res.2.2.1, res.2.2.2.1, powOKR g (va (p + 80)) && res.2.2.2.2)

theorem packSpec2_pos (v : Nat → FE2) (va : Nat → FE) (g : Nat) : ∀ (pt : List FE2) (value scale : FE2) (p : Nat),
    (packSpec2 v va g pt value scale p).2.2.2.1 = p + 112 * pt.length
  | [], _, _, p => by simp [packSpec2]
  | r :: rs, value, scale, p => by
    simp only [packSpec2, List.length_cons]
    rw [packSpec2_pos v va g rs]
    ring

theorem packSpec2_length (v : Nat → FE2) (va : Nat → FE) (g : Nat) : ∀ (pt : List FE2) (value scale : FE2) (p : Nat),
    (packSpec2 v va g pt value scale p).2.2.1.length = pt.length
  | [], _, _, _ => rfl
  | r :: rs, value, scale, p => by
    simp only [packSpec2, List.length_cons]
    rw [packSpec2_length v va g rs]

theorem q2PackRound_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {v : Nat → FE2}
    {va : Nat → FE} (hva : ∀ o, e2OfFE (va o) = v o)
    {off q N : Nat} {str : List Nat} (hv : ∀ m < N, lv2 xv str m = v (8 * m + off)) (hN : q + 5 < N) {p : Nat}
    (hp : p + 40 = 8 * q + off)
    (r value scale : S2) (n : Nat) (h : THold2 xv V n (q2PackRound z q str r value scale n).2) :
    (q2PackRound z q str r value scale n).1.1.valF xv V =
        (1 + r.valF xv V + e2OfFE (va (p + 80))) *
          polyEvalF ((value.valF xv V + r.valF xv V * sumF (scalars2 v (p + 40) 2)) :: scalars2 v (p + 40) 2)
            (e2OfFE (va (p + 80))) ∧
    (q2PackRound z q str r value scale n).1.2.1.valF xv V = scale.valF xv V * (1 + r.valF xv V + e2OfFE (va (p + 80))) ∧
    (q2PackRound z q str r value scale n).1.2.2.valF xv V = e2OfFE (va (p + 80)) := by
  unfold q2PackRound at h ⊢
  obtain ⟨h4, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h5, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h6, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h7, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h8, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h9, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h10, -⟩ := (thold2_bind _ _).mp h
  have e4 := q2Add_spec h4
  have e5 := q2Mul_spec h5
  have e6 := q2Mul_spec h6
  have e7 := q2Mul_spec h7
  have e8 := q2Lin_spec h8
  have e9 := q2Mul_spec h9
  have e10 := q2Mul_spec h10
  have c1 : (lane2 q str).valF xv V = v (p + 40) := by rw [lane2_valF, hv _ (by (clear * - q N off hN p; omega))]; congr 1; (clear * - q off p N hp; omega)
  have c2 : (lane2 (q + 2) str).valF xv V = v (p + 56) := by rw [lane2_valF, hv _ (by (clear * - q N off hN p; omega))]; congr 1; (clear * - q off p N hp; omega)
  have c3 : (lane2 (q + 5) str).valF xv V = e2OfFE (va (p + 80)) := by
    rw [lane2_valF, hv _ (by (clear * - hN; omega)), hva]; congr 1; (clear * - q off p N hp; omega)
  simp only [tb_bind, tb_pure]
  rw [c1, c2] at e4
  simp only [scalars2, List.range_succ, List.range_zero, List.map_append, List.map_nil, List.nil_append,
    List.map_cons, sumF, polyEvalF, List.cons_append, List.singleton_append, List.foldl_cons, List.foldl_nil,
    List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [e9, e8, e7, e6, e5, e4, c1, c2, c3, hz, fe2_ofK_one]
    ring
  · rw [e10, e8, c3, hz, fe2_ofK_one]
    ring
  · exact c3

/-- **The pack rounds are `V`'s `packSpec2`** (values, scale, challenges). -/
theorem q2PackRounds_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {v : Nat → FE2}
    {va : Nat → FE} (hva : ∀ o, e2OfFE (va o) = v o) (g : Nat)
    {off N : Nat} {str : List Nat} (hv : ∀ m < N, lv2 xv str m = v (8 * m + off)) :
    ∀ (rs : List S2) (q p : Nat), q + 14 * rs.length ≤ N → p + 40 = 8 * q + off → ∀ (value scale : S2) (n : Nat),
      THold2 xv V n (q2PackRounds z str q rs value scale n).2 →
      (q2PackRounds z str q rs value scale n).1.1.valF xv V =
          (packSpec2 v va g (vals2 xv V rs) (value.valF xv V) (scale.valF xv V) p).1 ∧
      (q2PackRounds z str q rs value scale n).1.2.1.valF xv V =
          (packSpec2 v va g (vals2 xv V rs) (value.valF xv V) (scale.valF xv V) p).2.1 ∧
      vals2 xv V (q2PackRounds z str q rs value scale n).1.2.2 =
          (packSpec2 v va g (vals2 xv V rs) (value.valF xv V) (scale.valF xv V) p).2.2.1
  | [], q, p, _, _, value, scale, n, _ => by simp [q2PackRounds, tb_pure, packSpec2]
  | r :: rs, q, p, hN, hp, value, scale, n, h => by
    simp only [q2PackRounds] at h ⊢
    obtain ⟨h1, h⟩ := (thold2_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold2_bind _ _).mp h
    obtain ⟨e1, e2, e3⟩ := q2PackRound_spec hz hva hv (by simp at hN; (clear * - q N off rs p hN; omega)) hp r value scale n h1
    have ih := q2PackRounds_spec hz hva g hv rs (q + 14) (p + 112) (by simp at hN; (clear * - q rs N off p hN; omega)) (by (clear * - p q off N r rs hp; omega)) _ _ _ h2
    simp only [tb_bind, tb_pure, vals2, List.map_cons, packSpec2]
    rw [e1, e2] at ih
    exact ⟨ih.1, ih.2.1, congrArg₂ List.cons e3 ih.2.2⟩

theorem q2LocalRound_spec {xv : Src → FE} {V : Nat → FE} {v : Nat → FE2} {va : Nat → FE}
    (hva : ∀ o, e2OfFE (va o) = v o)
    {off q N : Nat} {str : List Nat} (hv : ∀ m < N, lv2 xv str m = v (8 * m + off)) (hN : q + 7 < N) {p : Nat}
    (hp : p + 40 = 8 * q + off)
    (value : S2) (n : Nat) (h : THold2 xv V n (q2LocalRound q str value n).2) :
    (q2LocalRound q str value n).1.1.valF xv V =
        polyEvalF (roundPoly2 v p 4 (value.valF xv V)) (e2OfFE (va (ansAt2 p 4))) ∧
    (q2LocalRound q str value n).1.2.valF xv V = e2OfFE (va (ansAt2 p 4)) := by
  unfold q2LocalRound at h ⊢
  obtain ⟨h5, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h6, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h7, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h8, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h9, -⟩ := (thold2_bind _ _).mp h
  have e5 := q2Add_spec h5
  have e6 := q2Add_spec h6
  have e7 := q2Mul_spec h7
  have e8 := q2Mul_spec h8
  have e9 := q2Mul_spec h9
  have c0 : (lane2 q str).valF xv V = v (p + 40) := by rw [lane2_valF, hv _ (by (clear * - q N off hN p; omega))]; congr 1; (clear * - q off p N hp; omega)
  have c2 : (lane2 (q + 2) str).valF xv V = v (p + 56) := by rw [lane2_valF, hv _ (by (clear * - q N off hN p; omega))]; congr 1; (clear * - q off p N hp; omega)
  have c3 : (lane2 (q + 4) str).valF xv V = v (p + 56 + 16) := by
    rw [lane2_valF, hv _ (by (clear * - q N off hN p; omega))]; congr 1; (clear * - q off p N hp; omega)
  have ch : (lane2 (q + 7) str).valF xv V = e2OfFE (va (ansAt2 p 4)) := by
    rw [lane2_valF, hv _ (by (clear * - hN; omega)), hva]; congr 1; simp only [ansAt2]; (clear * - q off p N hp; omega)
  simp only [tb_bind, tb_pure]
  refine ⟨?_, ch⟩
  simp only [roundPoly2, scalars2, show (4 - 2 : Nat) = 2 from rfl, List.range_succ, List.range_zero,
    List.map_append, List.map_nil, List.nil_append, List.map_cons, sumF, polyEvalF, List.cons_append,
    List.singleton_append, List.foldl_cons, List.foldl_nil, List.foldr_cons, List.foldr_nil, Nat.mul_zero,
    Nat.add_zero, Nat.mul_one]
  rw [e9, e8, e7, e6, e5, c0, c2, c3, ch]
  ring

/-- **The position rounds are `V`'s `scSpec2` with four coefficients.** -/
theorem q2LocalRounds_spec {xv : Src → FE} {V : Nat → FE} {v : Nat → FE2} {va : Nat → FE}
    (hva : ∀ o, e2OfFE (va o) = v o) (g : Nat)
    {off N : Nat} {str : List Nat} (hv : ∀ m < N, lv2 xv str m = v (8 * m + off)) :
    ∀ (k q p : Nat), q + 16 * k ≤ N → p + 40 = 8 * q + off → ∀ (value : S2) (n : Nat),
      THold2 xv V n (q2LocalRounds str k q value n).2 →
      (q2LocalRounds str k q value n).1.1.valF xv V = (scSpec2 v va g 4 p (value.valF xv V) k).2.1 ∧
      vals2 xv V (q2LocalRounds str k q value n).1.2 = (scSpec2 v va g 4 p (value.valF xv V) k).1
  | 0, q, p, _, _, value, n, _ => by simp [q2LocalRounds, tb_pure, scSpec2]
  | k + 1, q, p, hN, hp, value, n, h => by
    simp only [q2LocalRounds] at h ⊢
    obtain ⟨h1, h⟩ := (thold2_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold2_bind _ _).mp h
    obtain ⟨e1, e2⟩ := q2LocalRound_spec hva hv (by (clear * - q N off k p hN; omega)) hp value n h1
    have ih := q2LocalRounds_spec hva g hv k (q + 16) (p + roundLen2 4) (by (clear * - q k N off p hN; omega)) (by simp [roundLen2]; (clear * - p q off N k hp; omega)) _ _ h2
    simp only [tb_bind, tb_pure, vals2, List.map_cons, scSpec2]
    rw [e1] at ih
    exact ⟨ih.1, congrArg₂ List.cons e2 ih.2⟩

/-! ## No assertions -/

theorem noA_emit2 (f : E2Fn) (xs : List S2) : NoA (emit2 f xs) := by
  intro xv V n k hk ha
  simp only [emit2, e2I, List.length_cons, List.length_nil] at hk
  rcases (show k = 0 ∨ k = 1 by (clear * - k hk; omega)) with rfl | rfl <;> simp [emit2, e2I] at ha

theorem noA_q2Mul (a b d : S2) : NoA (q2Mul a b d) := noA_emit2 _ _
theorem noA_q2Lin (k : FK) (k' : FE2) (a b : S2) : NoA (q2Lin k k' a b) := noA_emit2 _ _
theorem noA_q2Add (a b : S2) : NoA (q2Add a b) := noA_q2Lin _ _ _ _
theorem noA_q2One (a : S2) : NoA (q2One a) := noA_q2Lin _ _ _ _
theorem noA_q2Scale (k : FK) (a : S2) : NoA (q2Scale k a) := noA_q2Lin _ _ _ _
theorem noA_q2Copy (a : S2) : NoA (q2Copy a) := noA_q2Lin _ _ _ _
theorem noA_kLin (k k' : FK) (a b : Src) : NoA (kLin k k' a b) := noA_emit nofun

theorem noA_q2Base (b : Src) : NoA (q2Base b) :=
  noA_bind (noA_kLin _ _ _ _) fun _ => noA_bind (noA_kLin _ _ _ _) fun _ => noA_pure _

theorem noA_mapT2 {α β : Type} {f : α → TB β} (hf : ∀ a, NoA (f a)) : ∀ l : List α, NoA (mapT2 f l)
  | [] => noA_pure _
  | a :: as => noA_bind (hf a) fun _ => noA_bind (noA_mapT2 hf as) fun _ => noA_pure _

theorem noA_q2Sum : ∀ (s : S2) (cs : List S2), NoA (q2Sum s cs)
  | _, [] => noA_pure _
  | s, c :: cs => noA_bind (noA_q2Add s c) fun s' => noA_q2Sum s' cs

theorem noA_q2Dot : ∀ (acc : S2) (cds : List (S2 × S2)), NoA (q2Dot acc cds)
  | _, [] => noA_pure _
  | acc, _ :: rest => noA_bind (noA_q2Mul _ _ acc) fun a => noA_q2Dot a rest

theorem noA_q2Horner (x : S2) : ∀ (h : S2) (cs : List S2), NoA (q2Horner x h cs)
  | _, [] => noA_pure _
  | h, c :: cs => noA_bind (noA_q2Mul h x c) fun h' => noA_q2Horner x h' cs

theorem noA_q2EqStep (z : S2) (tab : List S2) (r : S2) : NoA (q2EqStep z tab r) :=
  noA_bind (noA_q2One r) fun _ => noA_bind (noA_mapT2 (fun _ => noA_q2Mul _ _ _) _) fun _ =>
    noA_bind (noA_mapT2 (fun _ => noA_q2Mul _ _ _) _) fun _ => noA_pure _

theorem noA_q2EqTab (z : S2) : ∀ (tab pt : List S2), NoA (q2EqTab z tab pt)
  | _, [] => noA_pure _
  | tab, r :: rs => noA_bind (noA_q2EqStep z tab r) fun t => noA_q2EqTab z t rs

theorem noA_q2SumMap (z : S2) (k : Nat) {f : Nat → TB S2} (hf : ∀ c, NoA (f c)) : NoA (q2SumMap z k f) :=
  noA_bind (noA_mapT2 hf _) fun ts => noA_q2Sum z ts

theorem noA_q2Proj (z : S2) (masks : List Nat) (mu prod : List S2) : NoA (q2Proj z masks mu prod) :=
  noA_q2SumMap _ _ fun _ => noA_bind (noA_q2Sum _ _) fun _ => noA_q2Mul _ _ _

theorem noA_q2Powers (z s : S2) : ∀ (acc : S2) (k : Nat), NoA (q2Powers z s acc k)
  | _, 0 => noA_pure _
  | acc, k + 1 => noA_bind (noA_q2Mul acc s z) fun nx => noA_bind (noA_q2Powers z s nx k) fun _ => noA_pure _

theorem noA_q2Inst (z one s : S2) (embs : List Nat) : NoA (q2Inst z one s embs) :=
  noA_bind (noA_q2Powers _ _ _ _) fun _ => noA_bind (noA_mapT2 (fun _ => noA_q2Sum _ _) _) fun _ =>
    noA_bind (noA_q2Sum _ _) fun _ => noA_pure _

theorem noA_q2SumL (z : S2) : ∀ (cs : List S2), NoA (q2SumL z cs)
  | [] => noA_pure _
  | a :: as => noA_q2Sum a as

theorem noA_q2TabStep (v tab : List S2) (m : Nat) : NoA (q2TabStep v tab m) := by
  unfold q2TabStep; split
  · exact noA_pure _
  · exact noA_bind (noA_q2Add _ _) fun _ => noA_pure _

theorem noA_q2TabGo (v : List S2) : ∀ (tab : List S2) (m k : Nat), NoA (q2TabGo v tab m k)
  | _, _, 0 => noA_pure _
  | tab, m, k + 1 => noA_bind (noA_q2TabStep v tab m) fun t => noA_q2TabGo v t (m + 1) k

theorem noA_q2Tab (z : S2) (v : List S2) : NoA (q2Tab z v) := noA_q2TabGo _ _ _ _

theorem noA_q2ProjAcc (z : S2) (masks : List Nat) (tabs : List (List S2)) :
    ∀ (ps : List S2) (c : Nat) (acc : S2), NoA (q2ProjAcc z masks tabs ps c acc)
  | [], _, _ => noA_pure _
  | p :: ps, c, acc => by
    unfold q2ProjAcc; split
    · exact noA_q2ProjAcc z masks tabs ps (c + 1) acc
    · exact noA_bind (noA_q2SumL _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ => noA_q2ProjAcc z masks tabs ps _ _

theorem noA_q2Proj4 (z : S2) (masks : List Nat) (mu prod : List S2) : NoA (q2Proj4 z masks mu prod) :=
  noA_bind (noA_mapT2 (fun _ => noA_q2Tab _ _) _) fun _ => noA_q2ProjAcc _ _ _ _ _ _

theorem noA_q2Inst4 (z one s : S2) (embs : List Nat) : NoA (q2Inst4 z one s embs) :=
  noA_bind (noA_q2Powers _ _ _ _) fun _ => noA_bind (noA_mapT2 (fun _ => noA_q2Tab _ _) _) fun _ =>
    noA_bind (noA_mapT2 (fun _ => noA_q2SumL _ _) _) fun _ => noA_bind (noA_q2SumL _ _) fun _ => noA_pure _

theorem noA_q2LowTab (z : S2) (ta tb : List S2) (c rl : Nat) : NoA (q2LowTab z ta tb c rl) :=
  noA_q2SumMap _ _ fun zz => by
    by_cases h : (zz + rl) / 8 = c
    · simp only [h, ite_true]; exact noA_q2Mul _ _ _
    · simp only [h, ite_false]; exact noA_pure _

theorem noA_q2HighTab (z : S2) (ta tb : List S2) (k : Nat) : NoA (q2HighTab z ta tb k) :=
  noA_q2SumMap _ _ fun _ => noA_q2Mul _ _ _

theorem noA_q2Shift (z : S2) (L0 L1 H : List S2) (r : Nat) : NoA (q2Shift z L0 L1 H r) :=
  noA_bind (noA_q2Mul _ _ _) fun _ => noA_q2Mul _ _ _

theorem noA_q2LaneForm (z : S2) (B : List S2) (R : Nat → S2) (l : Nat) : NoA (q2LaneForm z B R l) :=
  noA_bind (noA_q2Mul _ _ _) fun _ => noA_bind (noA_q2Dot _ _) fun _ => noA_q2Dot _ _

theorem noA_q2Flip (z : S2) (B A : List S2) (i : Nat) : NoA (q2Flip z B A i) := noA_q2LaneForm _ _ _ _

theorem noA_q2LaneW (eL : List S2) (beta : S2) : NoA (q2LaneW eL beta) :=
  noA_mapT2 (fun _ => noA_bind (noA_q2Mul _ _ _) fun _ => noA_q2Mul _ _ _) _

theorem noA_q2IndexStep (z : S2) (k : Nat) (acc r : S2) : NoA (q2IndexStep z k acc r) :=
  noA_bind (noA_q2Scale _ _) fun _ => noA_bind (noA_q2One _) fun _ => noA_q2Mul _ _ _

theorem noA_q2Index (z : S2) : ∀ (k : Nat) (acc : S2) (rs : List S2), NoA (q2Index z k acc rs)
  | _, _, [] => noA_pure _
  | k, acc, r :: rs => noA_bind (noA_q2IndexStep z k acc r) fun acc' => noA_q2Index z (k + 1) acc' rs

theorem noA_q2PackRound (z : S2) (q : Nat) (str : List Nat) (r value scale : S2) :
    NoA (q2PackRound z q str r value scale) :=
  noA_bind (noA_q2Add _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ =>
  noA_bind (noA_q2Mul _ _ _) fun _ => noA_bind (noA_q2Lin _ _ _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ =>
  noA_bind (noA_q2Mul _ _ _) fun _ => noA_pure _

theorem noA_q2PackRounds (z : S2) (str : List Nat) :
    ∀ (q : Nat) (rs : List S2) (value scale : S2), NoA (q2PackRounds z str q rs value scale)
  | _, [], _, _ => noA_pure _
  | q, r :: rs, value, scale => noA_bind (noA_q2PackRound z q str r value scale) fun a =>
    noA_bind (noA_q2PackRounds z str (q + 14) rs a.1 a.2.1) fun _ => noA_pure _

theorem noA_q2LocalRound (q : Nat) (str : List Nat) (value : S2) : NoA (q2LocalRound q str value) :=
  noA_bind (noA_q2Add _ _) fun _ => noA_bind (noA_q2Add _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ =>
  noA_bind (noA_q2Mul _ _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ => noA_pure _

theorem noA_q2LocalRounds (str : List Nat) : ∀ (k q : Nat) (value : S2), NoA (q2LocalRounds str k q value)
  | 0, _, _ => noA_pure _
  | k + 1, q, value => noA_bind (noA_q2LocalRound q str value) fun a =>
    noA_bind (noA_q2LocalRounds str k (q + 16) a.1) fun _ => noA_pure _

/-! ## Walking an `E2` template -/

/-- `TInv` on `THold2`: the rows of the rest `R` hold (twin rows included), the whole has length `L`, and the
whole's assertions `TA` hold iff the rest's do and `Q`. -/
def TInv2 (xv : Src → FE) (V : Nat → FE) (TA : Prop) (L : Nat) (Q : Prop) {α : Type} (R : TB α) (n : Nat) :
    Prop :=
  THold2 xv V n (R n).2 ∧ L = n + (R n).2.length ∧ (TA ↔ TAssert xv V (R n).2 ∧ Q)

theorem inv_start2 {xv : Src → FE} {V : Nat → FE} {α : Type} {R : TB α} (h : THold2 xv V 0 (R 0).2) :
    TInv2 xv V (TAssert xv V (R 0).2) (R 0).2.length True R 0 :=
  ⟨h, (Nat.zero_add _).symm, ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩⟩

/-- Read a gadget without assertions. -/
theorem peelN2 {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {α β : Type} {m : TB α}
    {f : α → TB β} {n : Nat} (h : TInv2 xv V TA L Q (m >>= f) n) (hm : NoA m) :
    ∃ a n', (m n).1 = a ∧ THold2 xv V n (m n).2 ∧ TInv2 xv V TA L Q (f a) n' := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [thold2_bind] at h1
  refine ⟨(m n).1, n + (m n).2.length, rfl, h1.1, h1.2, ?_, ?_⟩
  · rw [h2, tb_bind, List.length_append]; (clear * - n α m β f L; omega)
  · rw [h3, tassert_bind]
    exact ⟨fun ⟨⟨_, h⟩, hq⟩ => ⟨h, hq⟩, fun ⟨h, hq⟩ => ⟨⟨hm _ _ _, h⟩, hq⟩⟩

/-- Read the last gadget (its position kept). -/
theorem peelL2 {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {α β : Type} {m : TB α}
    {f : α → TB β} {n : Nat} (h : TInv2 xv V TA L Q (m >>= f) n) (hm : NoA m) :
    THold2 xv V n (m n).2 ∧ TInv2 xv V TA L Q (f (m n).1) (n + (m n).2.length) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [thold2_bind] at h1
  refine ⟨h1.1, h1.2, ?_, ?_⟩
  · rw [h2, tb_bind, List.length_append]; (clear * - n α m β f L; omega)
  · rw [h3, tassert_bind]
    exact ⟨fun ⟨⟨_, h⟩, hq⟩ => ⟨h, hq⟩, fun ⟨h, hq⟩ => ⟨⟨hm _ _ _, h⟩, hq⟩⟩

theorem tassert_q2Assert {xv : Src → FE} {V : Nat → FE} {n : Nat} {a : S2} {g : Src} :
    TAssert xv V (q2Assert a g n).2 ↔ g.valF xv V * a.1.valF xv V = 0 ∧ g.valF xv V * a.2.valF xv V = 0 := by
  refine ⟨q2Assert_spec, fun ⟨h1, h2⟩ => (tassert_bind _ _).mpr ⟨tassert_gAssert.mpr h1, tassert_gAssert.mpr h2⟩⟩

/-- Read a coordinatewise assertion. -/
theorem peelA2 {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {β : Type} {a : S2} {g : Src}
    {f : Unit → TB β} {n : Nat} (h : TInv2 xv V TA L Q (q2Assert a g >>= f) n) :
    ∃ n', TInv2 xv V TA L (Q ∧ (g.valF xv V * a.1.valF xv V = 0 ∧ g.valF xv V * a.2.valF xv V = 0)) (f ()) n' := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : (q2Assert a g n).1 = () := rfl
  rw [thold2_bind, e] at h1
  rw [tb_bind, e] at h2
  rw [tassert_bind, e] at h3
  refine ⟨n + (q2Assert a g n).2.length, h1.2, ?_, ?_⟩
  · rw [h2, List.length_append]; (clear * - n a g β f L; omega)
  · rw [h3, tassert_q2Assert]
    exact ⟨fun ⟨⟨h, h'⟩, hq⟩ => ⟨h', hq, h⟩, fun ⟨h', hq, h⟩ => ⟨⟨h, h'⟩, hq⟩⟩

theorem inv_end2 {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {n : Nat}
    (h : TInv2 xv V TA L Q (pure () : TB Unit) n) : L = n ∧ (TA ↔ Q) := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨by simpa [tb_pure] using h2, ?_⟩
  rw [h3]
  exact ⟨fun h => h.2, fun h => ⟨noA_pure () xv V n, h⟩⟩

/-- An `E2` value is `0` iff both coordinates are. -/
theorem s2_zero_iff {xv : Src → FE} {V : Nat → FE} (a : S2) :
    a.valF xv V = 0 ↔ (a.1.valF xv V).c₀ = 0 ∧ (a.2.valF xv V).c₀ = 0 := by
  constructor
  · intro h
    exact ⟨congrArg FE2.re h, congrArg FE2.im h⟩
  · rintro ⟨h1, h2⟩
    show (⟨(a.1.valF xv V).c₀, (a.2.valF xv V).c₀⟩ : FE2) = ⟨0, 0⟩
    rw [h1, h2]

/-! ## Copy rows -/

theorem mapT2_q2Copy_fst : ∀ (l : List S2) (n : Nat), (mapT2 q2Copy l n).1 =
    (List.range l.length).map fun j => ((.loc (n + 2 * j), .loc (n + 2 * j + 1)) : S2)
  | [], _ => rfl
  | a :: as, n => by
    simp only [mapT2, tb_bind, tb_pure, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [mapT2_q2Copy_fst as]
    simp only [Function.comp_def, q2Copy, q2Lin, emit2, e2I, List.length_cons, List.length_nil, Nat.mul_zero,
      Nat.add_zero]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    congr 2 <;> (clear * - n j; omega)

theorem mapT2_q2Copy_length (l : List S2) (n : Nat) : (mapT2 q2Copy l n).2.length = 2 * l.length := by
  induction l generalizing n with
  | nil => rfl
  | cons a as ih =>
    simp only [mapT2, tb_bind, tb_pure, List.append_nil, List.length_append, ih, List.length_cons]
    simp only [q2Copy, q2Lin, emit2, e2I, List.length_cons, List.length_nil]
    (clear * - as; omega)

/-- **The copy rows**: value `j` of `l` sits in the twin cells `n + 2j`, `n + 2j + 1`. -/
theorem cp2_get {xv : Src → FE} {V : Nat → FE} {n : Nat} {l : List S2} (h : THold2 xv V n (mapT2 q2Copy l n).2) :
    ∀ j < l.length, (⟨(V (n + 2 * j)).c₀, (V (n + 2 * j + 1)).c₀⟩ : FE2) = (vals2 xv V l).getD j 0 := by
  intro j hj
  have k := mapT2_spec (P := fun a s => S2.valF xv V s = a.valF xv V) (fun a m hm => q2Copy_spec hm) l n h
  have e := forall₂_map_eq2 k
  rw [mapT2_q2Copy_fst] at e
  have := congrArg (fun L : List FE2 => L.getD j 0) e
  simp only [List.map_map, Function.comp_def] at this
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range] at this
  rw [← this]
  rfl

end Lvm.Q1
