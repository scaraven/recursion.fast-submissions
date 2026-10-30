-- New for `flock-recursive` (PACK-4.4 §6.2, R1's route (a); track C1b).
import FRVIRTplRepLD
import FRVerifierImplNode4F

/-!
# The replay template of a node's `evalL`: correctness

**`tplEvL_ok`**: with `e.one = 1`, the inputs `rL ++ r4` and the gate equations, the outputs of
`tplEvL ν rL.size r4.size` (`FRVIRTplRepLD`) are `evalL4I ν rL r4`'s three values (CF2: by the carry
automata's `GS` values, `ok_autoG`, `GS_eq`).
-/

namespace FR
namespace Tpl
open Circ Finset NI4 NI4F Impl

variable {e : Env}

/-- An `eq` table over `n` coordinates `g 0 … g (n−1)` at an index below `2^n`. -/
theorem eqTable_getD_map (n : ℕ) (g : ℕ → F) {x : ℕ} (hx : x < 2 ^ n) :
    (eqTable ((List.range n).map g)).getD x 0 = eqAtR (fun l : Fin n => g l) x := by
  rw [eqTable_getD _ (by simpa using hx)]
  unfold eqAtR ptOf
  rw [Fin.prod_univ_eq_prod_range
      (fun l => if x.testBit l then ((List.range n).map g).getD l 0 else 1 - ((List.range n).map g).getD l 0),
    Fin.prod_univ_eq_prod_range (fun l => if x.testBit l then g l else 1 - g l)]
  simp only [List.length_map, List.length_range]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getElem_range]

theorem nJL_eq : nJL = nJ := rfl

/-- `evalL4I`'s three values as sums over the slots and their bits. -/
theorem evalL4I_sums (ν : Rev4.NodeKind) (rL r4 : Array F) :
    evalL4I ν rL r4 =
      (∑ σ ∈ range ν.vslots, eqAtR (hiK 14 (ν.m - 7) r4) (ν.lBase * 128 / 2 ^ 14 + σ) *
          ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) *
            (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0,
       (∑ σ ∈ range ν.vslots, ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j)) *
          eqAtR (ptA (ν.m - 7) r4) ν.oneCell -
        ∑ σ ∈ range ν.vslots, eqAtR (hiK 14 (ν.m - 7) r4) (ν.lBase * 128 / 2 ^ 14 + σ) *
          ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) *
            (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0,
       0) := by
  simp only [evalL4I, slotL, sumTo_eq, Prod.fst_sum, Prod.snd_sum]

/-! ## The bit factors' values -/

/-- The bit factors of a block's values `v` (`n` coordinates, padded). -/
def fE (v : ℕ → F) (n l : ℕ) (bit : Bool) : F := if l < n then (if bit then v l else 1 - v l) else (if bit then 0 else 1)

def fO (_ : ℕ) (_ : Bool) : F := 1

theorem qE_ev (h1 : e.one = 1) {c : ℕ → LinT} {v : ℕ → F} (hc : ∀ l, (c l).ev e = v l) (n l : ℕ) (bit : Bool) :
    (qE c n l bit).ev e = fE v n l bit := by
  unfold qE fE
  split_ifs <;> simp [ev_append, ev_sc, ev_C, h1, hc] <;> ring

theorem qO_ev (h1 : e.one = 1) (l : ℕ) (bit : Bool) : (qO l bit).ev e = fO l bit := by
  simp [qO, fO, ev_C, h1]

theorem PF_fO (L x : ℕ) : PF fO L x = if x < 2 ^ L then 1 else 0 := by
  unfold PF fO; simp

/-- **Padded factors are `gN`** of the block. -/
theorem PF_fE (v : ℕ → F) {n L : ℕ} (h : n ≤ L) (x : ℕ) : PF (fE v n) L x = TEval.gN n v x := by
  obtain ⟨d, rfl⟩ : ∃ d, L = n + d := ⟨L - n, by omega⟩
  unfold PF TEval.gN TEval.eqN
  by_cases hx : x < 2 ^ n
  · have hx' : x < 2 ^ (n + d) := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [if_pos hx', if_pos hx, prod_range_add]
    have h2 : ∏ l ∈ range d, fE v n (n + l) (x.testBit (n + l)) = 1 := prod_eq_one fun l _ => by
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp [fE]
    rw [h2, mul_one]
    exact prod_congr rfl fun l hl => by simp [fE, mem_range.1 hl]
  · rw [if_neg hx]
    split_ifs with hx'
    · have hne : x / 2 ^ n ≠ 0 := by
        rw [Ne, Nat.div_eq_zero_iff_lt (by positivity)]; exact hx
      obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
      have hlt : x / 2 ^ n < 2 ^ d := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm]; exact hx'
      have hid : i < d := by
        by_contra hc
        exact absurd hi (by rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]; simp)
      rw [prod_range_add]
      refine mul_eq_zero_of_right _ (prod_eq_zero (mem_range.2 hid) ?_)
      rw [show n + i = i + n by ring, ← Nat.testBit_div_two_pow, hi]
      simp [fE]
    · rfl

theorem eqAtR_gN {n : ℕ} (g : ℕ → F) {x : ℕ} (hx : x < 2 ^ n) : eqAtR (fun l : Fin n => g l) x = TEval.gN n g x := by
  unfold eqAtR TEval.gN TEval.eqN
  rw [if_pos hx, Fin.prod_univ_eq_prod_range (fun l => if x.testBit l then g l else 1 - g l)]

theorem lsumR (n : ℕ) (f : ℕ → F) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem flatten_ev (l : List LinT) : LinT.ev e l.flatten = (l.map (LinT.ev e)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatten_cons, ev_append, ih]; simp

theorem getD_ev {α : Type} {l : List LinT} {m : List α} {g : α → F} (h : l.map (LinT.ev e) = m.map g) {i : ℕ}
    (hi : i < m.length) : (l.getD i []).ev e = g m[i] := by
  have hl : l.length = m.length := by simpa using congrArg List.length h
  have := congrArg (fun x => x.getD i 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (hl ▸ hi),
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ hi), Option.getD_some]
  exact this

section Proof
variable {ν : Rev4.NodeKind} {rL r4 : Array F} (hi : InpIs e (rL.toList ++ r4.toList))
include hi

set_option maxHeartbeats 1000000 in
/-- **The node kind `ν`'s `evalL` template computes `evalL4I ν`.** -/
theorem tplEvL_ok (h1 : e.one = 1) (h : Eqns e (tplEvL ν rL.size r4.size).gates 0) :
    (tplEvL ν rL.size r4.size).outs.map (LinT.ev e) =
      [(evalL4I ν rL r4).1, (evalL4I ν rL r4).2.1, (evalL4I ν rL r4).2.2] := by
  obtain ⟨hfit, hlo, h3, hVJ, h9, hhi⟩ := lCells_fit ν
  have hNJ : nJL = nJ := rfl
  have hnJ : nJ = 8220 := rfl
  have hq1 := qE_ev h1 (cT_ev hi) ν.dims.logL
  have hq2 := qE_ev h1 (cR_ev hi) 14
  have hq3 := qE_ev h1 (c := fun l => cR rL.size r4.size (14 + l)) (v := fun l => r4.getD (14 + l) 0)
    (fun l => cR_ev hi (14 + l)) (ν.m - 7 - 14)
  have hL14 : 14 ≤ ν.dims.logL := by
    have : nJ ≤ 2 ^ ν.dims.logL := le_trans (Nat.le_mul_of_pos_left _ (by cases ν <;> decide)) hVJ
    by_contra hc
    have : 2 ^ ν.dims.logL ≤ 2 ^ 13 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hnJ] at *; omega
  have hpow : 2 ^ (ν.m - 7) = 2 ^ (ν.m - 7 - 14) * 2 ^ 14 := by rw [← pow_add, Nat.sub_add_cancel hhi]
  -- the four automata's values
  have hok : GM.Ok e (evGM ν rL.size r4.size) fun outs => outs.map (LinT.ev e) =
      [(evalL4I ν rL r4).1, (evalL4I ν rL r4).2.1, (evalL4I ν rL r4).2.2] := by
    unfold evGM
    refine GM.ok_bind (ok_autoG h1 _ _ _ _ _ _ hq1 hq2) fun S hS => ?_
    refine GM.ok_bind (ok_autoG h1 _ _ _ _ _ _ hq1 (qO_ev h1)) fun E hE => ?_
    refine GM.ok_bind (ok_autoG h1 _ _ _ _ _ _ hq2 (qO_ev h1)) fun O1 hO1 => ?_
    refine GM.ok_bind (ok_autoG h1 _ _ _ _ _ _ hq3 (qO_ev h1)) fun H hH => ?_
    refine GM.ok_bind (GM.ok_mapL (E := LinT.ev e) (v := fun σ => (H.getD σ []).ev e * (S.getD σ []).ev e) _
      fun σ _ => ok_mulF _ _) fun Q hQ => ?_
    refine GM.ok_bind (ok_mulF _ _) fun O hO => GM.ok_map (ok_mulF _ _) fun EO hEO => ?_
    -- slot values
    have hSg : ∀ σ < ν.vslots, GS (fE (fun l => rL.getD l 0) ν.dims.logL) (fE (fun l => r4.getD l 0) 14) ν.dims.logL
        nJL (σ * nJL) 299 = ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) *
          (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0 := fun σ hσ => by
      rw [GS_eq, hNJ]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.1 hj
      have hx : σ * nJ + j < 2 ^ ν.dims.logL := lt_of_lt_of_le (by nlinarith) hVJ
      have hy : 299 + j < 2 ^ 14 := by rw [hnJ] at hj'; norm_num; omega
      have e1 : TEval.gN ν.dims.logL (fun l => rL.getD l 0) (σ * nJ + j) = (bt ν.dims.logL rL).eq (σ * nJ + j) := by
        rw [bt_eq h9 _ hx, ← eqAtR_gN (fun l => rL.getD l 0) hx]; rfl
      have e2 : TEval.gN 14 (fun l => r4.getD l 0) (299 + j) = (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0 := by
        rw [ofFn_eq_range (ptA 14 r4) (fun l => r4.getD l 0) fun l => rfl, eqTable_getD_map 14 _ hy,
          eqAtR_gN (fun l => r4.getD l 0) hy]
      rw [PF_fE _ le_rfl, PF_fE _ hL14, e1, e2]
    have hEg : ∀ σ < ν.vslots, GS (fE (fun l => rL.getD l 0) ν.dims.logL) fO ν.dims.logL nJL (σ * nJL) 0 =
        ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) := fun σ hσ => by
      rw [GS_eq, hNJ]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.1 hj
      have hx : σ * nJ + j < 2 ^ ν.dims.logL := lt_of_lt_of_le (by nlinarith) hVJ
      have hy : 0 + j < 2 ^ ν.dims.logL := lt_of_lt_of_le (by nlinarith) hVJ
      have e1 : TEval.gN ν.dims.logL (fun l => rL.getD l 0) (σ * nJ + j) = (bt ν.dims.logL rL).eq (σ * nJ + j) := by
        rw [bt_eq h9 _ hx, ← eqAtR_gN (fun l => rL.getD l 0) hx]; rfl
      rw [PF_fE _ le_rfl, PF_fO, if_pos hy, mul_one, e1]
    have hSv : ∀ σ < ν.vslots, (S.getD σ []).ev e = ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) *
        (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0 := fun σ hσ => by
      rw [getD_ev hS (by simpa using hσ)]
      simp only [List.getElem_map, List.getElem_range]
      exact hSg σ hσ
    have hb : ∀ σ < ν.vslots, evHb ν + σ < 2 ^ (ν.m - 7 - 14) := fun σ hσ => by
      have h2 := hpow ▸ hlo
      unfold evHb
      generalize 2 ^ (ν.m - 7 - 14) = X at h2 ⊢
      rw [show (2 : ℕ) ^ 14 = 16384 from rfl] at h3 hfit h2 ⊢
      omega
    have hq : ν.oneCell / 2 ^ 14 < 2 ^ (ν.m - 7 - 14) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← hpow]; exact hlo
    have hHv : ∀ σ < ν.vslots, (H.getD σ []).ev e = eqAtR (hiK 14 (ν.m - 7) r4) (evHb ν + σ) := fun σ hσ => by
      rw [getD_ev hH (by simpa using Nat.lt_succ_of_lt hσ)]
      rw [List.getElem_append_left (by simpa using hσ)]
      simp only [List.getElem_map, List.getElem_range, GS_eq, sum_range_one, add_zero, PF_fE _ le_rfl, PF_fO]
      rw [if_pos (by positivity), mul_one, ← eqAtR_gN (fun l => r4.getD (14 + l) 0) (hb σ hσ)]; rfl
    have hHo : (H.getD ν.vslots []).ev e = eqAtR (hiK 14 (ν.m - 7) r4) (ν.oneCell / 2 ^ 14) := by
      rw [getD_ev hH (by simp)]
      rw [List.getElem_append_right (by simp)]
      simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem_cons_zero, GS_eq, sum_range_one,
        add_zero, PF_fE _ le_rfl, PF_fO]
      rw [if_pos (by positivity), mul_one, ← eqAtR_gN (fun l => r4.getD (14 + l) 0) hq]; rfl
    have hO1v : (O1.getD 0 []).ev e = eqAtR (ptA 14 r4) (ν.oneCell % 2 ^ 14) := by
      rw [getD_ev hO1 (by simp)]
      simp only [List.getElem_cons_zero, GS_eq, sum_range_one, add_zero, PF_fE _ le_rfl, PF_fO]
      rw [if_pos (by positivity), mul_one, ← eqAtR_gN (fun l => r4.getD l 0) (Nat.mod_lt _ (by positivity))]; rfl
    have hQs : LinT.ev e Q.flatten = (evalL4I ν rL r4).1 := by
      rw [flatten_ev, hQ, evalL4I_sums, lsumR]
      exact sum_congr rfl fun σ hσ => by rw [hHv σ (mem_range.1 hσ), hSv σ (mem_range.1 hσ), evHb]
    have hEs : LinT.ev e E.flatten = ∑ σ ∈ range ν.vslots, ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) := by
      rw [flatten_ev, hE, List.map_map, lsumR]
      exact sum_congr rfl fun σ hσ => hEg σ (mem_range.1 hσ)
    have hOv : O.ev e = eqAtR (ptA (ν.m - 7) r4) ν.oneCell := by
      rw [hO, hO1v, hHo, eqAtR_splitK hhi]
    simp only [List.map_cons, List.map_nil, ev_append, ev_sc, ev_nil, hEO, hEs, hOv, hQs]
    rw [evalL4I_sums]
    simp only [List.cons.injEq, and_true, true_and]
    ring
  have hg : (tplEvL ν rL.size r4.size).gates = (evGM ν rL.size r4.size 0).1 := rfl
  have ho : (tplEvL ν rL.size r4.size).outs = (evGM ν rL.size r4.size 0).2 := rfl
  rw [hg] at h
  rw [ho]
  exact hok 0 h

end Proof

end Tpl
end FR
