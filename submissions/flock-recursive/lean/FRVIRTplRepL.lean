-- New for `flock-recursive` (PACK-4.4 §6.2, R1's route (a); track C1b).
import FRVIRTplRepLD
import FRVerifierImplNode4F

/-!
# The replay template of a node's `evalL`: correctness

**`tplEvL_ok`**: with `e.one = 1`, the inputs `rL ++ r4` and the gate equations, the outputs of
`tplEvL ν rL.size r4.size` (`FRVIRTplRepLD`) are `evalL4I ν rL r4`'s three values.
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

section Proof
variable {ν : Rev4.NodeKind} {rL r4 : Array F} (hi : InpIs e (rL.toList ++ r4.toList))
include hi

/-- **The four tables.** -/
theorem evE_ev (h1 : e.one = 1) (h : Eqns e (evT ν rL.size r4.size).1 0) (i : ℕ) :
    (evE ν rL.size r4.size 0 i).ev e = (bt ν.dims.logL rL).A.getD i 0 ∧
    (evE ν rL.size r4.size 1 i).ev e = (bt ν.dims.logL rL).B.getD i 0 ∧
    (evE ν rL.size r4.size 2 i).ev e = (eqTable ((List.range 14).map fun l => r4.getD l 0)).getD i 0 ∧
    (evE ν rL.size r4.size 3 i).ev e =
      (eqTable ((List.range (ν.m - 7 - 14)).map fun l => r4.getD (14 + l) 0)).getD i 0 := by
  have ht := fun j hj => tabsG_ev h1 (evCs ν rL.size r4.size) 0 h j hj
  simp only [evE, evT]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ht _ (by simp [evCs])] <;> congr 2 <;>
    simp only [evCs, List.getD_cons_zero, List.getD_cons_succ, List.map_map, Function.comp_def,
      cT_ev hi, cR_ev hi] <;>
    first | rfl | exact (ofFn_eq_range _ _ fun l => rfl).symm

set_option maxHeartbeats 1000000 in
/-- **The node kind `ν`'s `evalL` template computes `evalL4I ν`.** -/
theorem tplEvL_ok (h1 : e.one = 1) (h : Eqns e (tplEvL ν rL.size r4.size).gates 0) :
    (tplEvL ν rL.size r4.size).outs.map (LinT.ev e) =
      [(evalL4I ν rL r4).1, (evalL4I ν rL r4).2.1, (evalL4I ν rL r4).2.2] := by
  simp only [tplEvL, tplEvLx, Eqns.append, mulsG_nlocs, zero_add] at h
  rw [← mkEvCx_k1] at h
  obtain ⟨hT, hE, hF, hQ, hO, hM⟩ := h
  have eE := mulsG_eqns (k := (mkEvCx ν rL.size r4.size).k1) hE
  have eF := mulsG_eqns (k := evK2 ν (mkEvCx ν rL.size r4.size)) hF
  have eQ := mulsG_eqns (k := evK3 ν (mkEvCx ν rL.size r4.size)) hQ
  have eO := mulsG_eqns (k := evK4 ν (mkEvCx ν rL.size r4.size)) hO
  have eM : e.loc (evK4 ν (mkEvCx ν rL.size r4.size) + 1) =
      (sumG (evN ν) fun i => L ((mkEvCx ν rL.size r4.size).k1 + i)).ev e * e.loc (evK4 ν (mkEvCx ν rL.size r4.size)) +
        (sc (-1) (evS2 ν (mkEvCx ν rL.size r4.size))).ev e := by
    have := (Eqns.cons.1 hM).1
    simp only [Gate.Eqn, ev_L] at this
    exact this
  have hT4' := evE_ev hi h1 hT
  have hT4 : ∀ i, ((mkEvCx ν rL.size r4.size).E 0 i).ev e = (bt ν.dims.logL rL).A.getD i 0 ∧
      ((mkEvCx ν rL.size r4.size).E 1 i).ev e = (bt ν.dims.logL rL).B.getD i 0 ∧
      ((mkEvCx ν rL.size r4.size).E 2 i).ev e = (eqTable ((List.range 14).map fun l => r4.getD l 0)).getD i 0 ∧
      ((mkEvCx ν rL.size r4.size).E 3 i).ev e = (eqTable ((List.range (ν.m - 7 - 14)).map fun l => r4.getD (14 + l) 0)).getD i 0 :=
    fun i => by simp only [mkEvCx_E]; exact hT4' i
  obtain ⟨hfit, hlo, h3, -, -, hhi⟩ := lCells_fit ν
  -- the high table's entries are `eq(r4_hi, ·)`
  have hpow : 2 ^ (ν.m - 7) = 2 ^ (ν.m - 7 - 14) * 2 ^ 14 := by
    rw [← pow_add, Nat.sub_add_cancel hhi]
  have hH : ∀ x < 2 ^ (ν.m - 7 - 14), ((mkEvCx ν rL.size r4.size).E 3 x).ev e = eqAtR (hiK 14 (ν.m - 7) r4) x :=
    fun x hx => by rw [(hT4 x).2.2.2, eqTable_getD_map _ _ hx]; rfl
  have htY : ∀ x, ((mkEvCx ν rL.size r4.size).E 2 x).ev e = (eqTable (List.ofFn (ptA 14 r4))).getD x 0 :=
    fun x => by rw [(hT4 x).2.2.1, ofFn_eq_range (ptA 14 r4) (fun l => r4.getD l 0) fun l => rfl]
  -- the `E` and `F` locals
  have hNJ : nJL = 8220 := rfl
  have hidx : ∀ σ < ν.vslots, ∀ j < nJ, σ * nJL + j < evN ν := fun σ hσ j hj => by
    simp only [evN, hNJ, nJ] at hj ⊢
    have : σ + 1 ≤ ν.vslots := hσ
    nlinarith
  have hEv : ∀ σ < ν.vslots, ∀ j < nJ,
      e.loc ((mkEvCx ν rL.size r4.size).k1 + (σ * nJL + j)) = (bt ν.dims.logL rL).eq (σ * nJ + j) :=
    fun σ hσ j hj => by rw [eE _ (hidx σ hσ j hj), (hT4 _).1, (hT4 _).2.1]; rfl
  have hFv : ∀ σ < ν.vslots, ∀ j < nJ, e.loc (evK2 ν (mkEvCx ν rL.size r4.size) + (σ * nJL + j)) =
      (bt ν.dims.logL rL).eq (σ * nJ + j) * (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0 :=
    fun σ hσ j hj => by
      have hm : (σ * nJL + j) % nJL = j := by simp only [hNJ, nJ] at hj ⊢; omega
      rw [eF _ (hidx σ hσ j hj), ev_L, hEv σ hσ j hj, htY, hm]
  -- the slot products
  have hQv : ∀ σ < ν.vslots, e.loc (evK3 ν (mkEvCx ν rL.size r4.size) + σ) =
      eqAtR (hiK 14 (ν.m - 7) r4) (ν.lBase * 128 / 2 ^ 14 + σ) *
        ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) *
          (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0 := fun σ hσ => by
    have hb : ν.lBase * 128 / 2 ^ 14 + σ < 2 ^ (ν.m - 7 - 14) := by
      have h2 := hpow ▸ hlo
      generalize 2 ^ (ν.m - 7 - 14) = X at h2 ⊢
      rw [show (2 : ℕ) ^ 14 = 16384 from rfl] at h3 hfit h2 ⊢
      omega
    rw [eQ σ hσ, evHb, hH _ hb, sumG_ev]
    exact congrArg _ (Finset.sum_congr rfl fun j hj => by
      rw [ev_L, ← hFv σ hσ j (Finset.mem_range.1 hj)])
  -- `one`'s factor
  have hOv : e.loc (evK4 ν (mkEvCx ν rL.size r4.size)) = eqAtR (ptA (ν.m - 7) r4) ν.oneCell := by
    have h0 := eO 0 (by norm_num)
    rw [add_zero] at h0
    have hq : ν.oneCell / 2 ^ 14 < 2 ^ (ν.m - 7 - 14) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← hpow]; exact hlo
    rw [h0, (hT4 _).2.2.1, hH _ hq, eqAtR_splitK hhi, eqTable_getD_map 14 _ (Nat.mod_lt _ (by positivity))]
    rfl
  -- the sums
  have hS2 : (evS2 ν (mkEvCx ν rL.size r4.size)).ev e = (evalL4I ν rL r4).1 := by
    rw [evalL4I_sums, evS2, sumG_ev]
    exact Finset.sum_congr rfl fun σ hσ => by rw [ev_L, hQv σ (Finset.mem_range.1 hσ)]
  have hS1 : (sumG (evN ν) fun i => L ((mkEvCx ν rL.size r4.size).k1 + i)).ev e =
      ∑ σ ∈ range ν.vslots, ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) := by
    rw [sumG_ev, evN, nJL_eq, sum_range_mul]
    exact Finset.sum_congr rfl fun σ hσ => Finset.sum_congr rfl fun j hj => by
      rw [ev_L, ← nJL_eq, hEv σ (Finset.mem_range.1 hσ) j (Finset.mem_range.1 hj)]; rfl
  simp only [tplEvL, tplEvLx, List.map_cons, List.map_nil, ev_L, ev_nil]
  rw [hS2, eM, hS1, hOv, ev_sc, hS2]
  rw [evalL4I_sums]
  simp only [List.cons.injEq, and_true, true_and]
  ring

end Proof

end Tpl
end FR
