-- New for lvm2 E2F (slice S1, E2F-QH2): the row switch's target gadget replays V's `rowSwitchD`: on a streamed memory
-- where `rowG`'s rows hold and the free row words are the slices' bit transpose (`rowAux_sound`), the gadget's
-- `eq(r'', ·)` and target are V's.
import LvmQRingRowSem
import LvmE2QPinSem
import LvmE2QLRun

/-!
# `rowSwitch_replays`

* `hs_eqTabE`, `hs_dotE`: the `E`-row `eq` table and dot;
* `rowG_spec`: `rr` = the seven answers at `qr + 9 k`, `eqR = eqKernel rr`, `target = Σ_j eqR_j·t_j`;
* `rowValD`, `rowSwitchD_run`: V's `rowSwitchD` from a cursor is `rowValD` of the answers' `eq` table;
* **`rowSwitch_replays`**: with `8 qr = P + 40` and `t_j = rowWordD sv j`, V's run is `rowValD` of the gadget's
  `eq(r'', ·)`, and its target is the gadget's.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q1 DM

variable {c : Ctx} {M : Mem}

/-- `eqKernel`'s step on `E3`. -/
def eqStepE (out : List FE) (r : FE) : List FE := out.map (· * (1 + r)) ++ out.map (· * r)

theorem ofK1 : FE.ofK 1 = 1 := rfl
theorem ofK0 : FE.ofK 0 = 0 := rfl

theorem hs_eqTabE {z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1) : ∀ (tab rs : List Cell),
    Hs c M (eqTabE (ec z) (ec o) tab rs)
      (fun t => t.map (Cell.val M) = (rs.map (Cell.val M)).foldl eqStepE (tab.map (Cell.val M)))
  | tab, [] => hs_pure rfl
  | tab, r :: rs => by
    unfold eqTabE
    refine hs_bind (hs_lin _ 1 0 r (ec o)) fun r1 hr1 => ?_
    rw [Cell.val_E, ho, ofK1, ofK0, one_mul, add_zero, add_comm] at hr1
    refine hs_bind (hs_mapBC (fun e => mulAdd .E e r1 (ec z)) (fun e => e.val M * (1 + r.val M)) tab
      fun e _ => hs_mono (hs_mulAdd _ _ _ _) fun x hx => by rw [hx, hr1, Cell.val_E, hz, add_zero]) fun lo hlo => ?_
    refine hs_bind (hs_mapBC (fun e => mulAdd .E e r (ec z)) (fun e => e.val M * r.val M) tab
      fun e _ => hs_mono (hs_mulAdd _ _ _ _) fun x hx => by rw [hx, Cell.val_E, hz, add_zero]) fun hi hhi => ?_
    refine hs_mono (hs_eqTabE hz ho (lo ++ hi) rs) fun t ht => ?_
    rw [ht, List.map_append, hlo, hhi, List.map_cons, List.foldl_cons, eqStepE, List.map_map, List.map_map]
    rfl

theorem hs_dotE : ∀ (acc : Cell) (l : List (Cell × Cell)),
    Hs c M (dotE acc l) (fun r => r.val M = acc.val M + (l.map fun e => e.1.val M * e.2.val M).sum)
  | acc, [] => hs_pure (by simp)
  | acc, (a, b) :: l => hs_bind (hs_mulAdd _ a b acc) fun s hs => hs_mono (hs_dotE s l) fun r hr => by
    rw [hr, hs, List.map_cons, List.sum_cons]; ring

theorem eqKernel_fold (rs : List FE) : eqKernel rs = rs.foldl eqStepE [1] := rfl

/-- **The target gadget's cells**: the answers, `eq(r'', ·)`, the target over the free words. -/
theorem rowG_spec {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {qr tB z o : Nat} (hz : M.e z = 0)
    (ho : M.e o = 1) (hT : qr + 9 * 6 + 2 < T) :
    Hs c M (rowG qr tB z o) (fun ro =>
      ro.eqR.map (Cell.val M) = eqKernel ((List.range 7).map fun k => feAt sig (8 * (qr + 9 * k))) ∧
      ro.target.val M = ((List.range 128).map fun j =>
        (eqKernel ((List.range 7).map fun k => feAt sig (8 * (qr + 9 * k)))).getD j 0 * FE.ofK (M.k (tB + j))).sum) := by
  unfold rowG
  refine hs_bind (hs_mapBC _ (fun q => feAt sig (8 * q)) (rowLanes qr) fun q hq => hs_loadLane hS (by
    simp only [rowLanes, List.mem_map, List.mem_range] at hq; obtain ⟨k, hk, rfl⟩ := hq; omega)) fun rr hrr => ?_
  refine hs_bind (hs_eqTabE hz ho [ec o] rr) fun eqR heq => ?_
  have hE : eqR.map (Cell.val M) = eqKernel ((List.range 7).map fun k => feAt sig (8 * (qr + 9 * k))) := by
    rw [heq, hrr, rowLanes, List.map_map, eqKernel_fold]
    simp only [List.map_cons, List.map_nil, Cell.val_E, ho]; rfl
  refine hs_bind (hs_dotE (ec z) _) fun t ht => hs_pure ⟨hE, ?_⟩
  rw [ht, Cell.val_E, hz, zero_add, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj' := List.mem_range.mp hj
  simp only [Function.comp_apply, Cell.val_K]
  congr 1
  have hl : eqR.length = 128 := by
    have := congrArg List.length hE
    rw [List.length_map, eqKernel_length_lk] at this
    simpa using this
  rw [← getD_map_val eqR (by omega)]
  show (eqR.map (Cell.val M)).getD j 0 = _
  rw [hE]

/-- `rowSwitchD`'s value from `eq(r'', ·)` (`eqR`): the target over the slices' row words, the weight. -/
def rowValD (zz sv : List FE2) (eqR : List FE) : (FE × (List FE → FE)) × List FE :=
  ((sumE ((List.range 128).map fun j => eqR.getD j 0 * FE.ofK (rowWordD sv j)),
    fun r => let t := tensorWD zz r; sumE ((List.range 128).map fun j => eqR.getD j 0 * t.getD j 0)), eqR)

/-- **V's `rowSwitchD`** from a cursor at `P`: the seven answers at `P + 40 + 72 k`, position `P + 504`, `ok` kept. -/
theorem rowSwitchD_run (zz sv : List FE2) (sig : ByteArray) (s : RS) :
    rowSwitchD zz sv sig s =
      (rowValD zz sv (eqKernel ((List.range 7).map fun k => feAt sig (rpos s + 40 + 72 * k))), ⟨rpos s + 504, 0, s.ok⟩) := by
  have e : rowSwitchD zz sv = (DM.samples 7 >>= fun rr => pure (rowValD zz sv (eqKernel rr))) := rfl
  rw [e, dbind_run, dpure_run, samples_run sig 7 s (by norm_num)]
  rfl

/-- **The row switch replays V's `rowSwitchD`**: with the first answer at lane `qr` (`8 qr = P + 40`) and the free
row words the slices' transpose (`rowAux_sound`), V's run is the gadget's `eq(r'', ·)` and its target the gadget's. -/
theorem rowSwitch_replays {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {qr tB z o : Nat} (hz : M.e z = 0)
    (ho : M.e o = 1) (hT : qr + 9 * 6 + 2 < T) (s : RS) (hP : 8 * qr = rpos s + 40) (zz sv : List FE2)
    (ht : ∀ j < 128, M.k (tB + j) = rowWordD sv j) :
    Hs c M (rowG qr tB z o) (fun ro =>
      rowSwitchD zz sv sig s = (rowValD zz sv (ro.eqR.map (Cell.val M)), ⟨rpos s + 504, 0, s.ok⟩) ∧
      (rowValD zz sv (ro.eqR.map (Cell.val M))).1.1 = ro.target.val M) :=
  hs_mono (rowG_spec hS hz ho hT) fun ro ⟨hE, hT'⟩ => by
    have hrr : ((List.range 7).map fun k => feAt sig (rpos s + 40 + 72 * k)) =
        (List.range 7).map fun k => feAt sig (8 * (qr + 9 * k)) :=
      List.map_congr_left fun k _ => congrArg _ (by omega)
    rw [rowSwitchD_run, hrr, ← hE]
    refine ⟨rfl, ?_⟩
    rw [hT', rowValD, sumE_eq, hE]
    exact congrArg List.sum (List.map_congr_left fun j hj => by rw [ht j (List.mem_range.mp hj)])

end Lvm.Q2
