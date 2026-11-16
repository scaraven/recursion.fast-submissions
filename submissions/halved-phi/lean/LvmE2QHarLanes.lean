-- New for lvm2 E2-FT (E2F-C4): the lanes of the front's ground challenges and scalars at every index (E2F-QH6's
-- `LvmE2QHarPos` gives the first ones): a run of `n` ground challenges inside a phase puts the `i`-th answer
-- `80 i + 48` bytes after the run's start; the gadgets read the schedule's lanes through `(itemLanes p).toArray`.
import LvmE2QHarPos

/-!
# The lanes of the front's challenge runs

* **`gsmp_lane`**: in a phase whose items are `pre ++ gsmpN n ++ post`, the `i`-th answer (`i < n`) has
  `8 · lane = posOf (start of the run) + 80 i + 48`;
* **`tape_ri`**, **`ks_ri`**: the tape's `r_i` and `KS`'s instance coordinates (QH5's `samplesG_phase` lanes
  `q + 10 i`);
* **`getD_toArray`**: the gadgets' `(itemLanes p).toArray.getD` is `laneOf`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm

theorem gsmpN_add (a b : Nat) : gsmpN (a + b) = gsmpN a ++ gsmpN b := by
  simp only [gsmpN, List.replicate_add, List.flatten_append]

/-- The gadgets' lane lookup is `laneOf`. -/
theorem getD_toArray (p : Params) (k : Nat) : (itemLanes p).toArray.getD k 0 = laneOf p k := by
  simp only [laneOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

section Runs

variable {p : Params} (h : StE2 p) (hA : alignB p = true)
include h hA

/-- **A run of ground challenges**: in phase `ph` with items `pre ++ gsmpN n ++ post` (`|pre| = a`), the `i`-th
answer (`i < n`, item `a + 2 i + 1`) has its lane `80 i + 48` bytes after the run's start. -/
theorem gsmp_lane {ph : Phase} {its pre post : List Item} {n a i : Nat} (hm : (ph, its) ∈ phasesE2 p)
    (hs : its = pre ++ gsmpN n ++ post) (ha : pre.length = a) (ho : NoOpen its) (hi : i < n) :
    8 * laneOf p (phaseItem0 p ph + (a + 2 * i + 1)) = posOf p (phaseItem0 p ph + a) + 80 * i + 48 := by
  have hl : its.length = a + 2 * n + post.length := by
    rw [hs, List.length_append, List.length_append, length_gsmpN, ha]
  have hs' : its = pre ++ gsmpN i ++ (gsmpN (n - i) ++ post) := by
    rw [hs, List.append_assoc, List.append_assoc, ← List.append_assoc (gsmpN i), ← gsmpN_add,
      Nat.add_sub_cancel' (Nat.le_of_lt hi)]
  have e1 := posOf_run h hA (a := a) (b := 2 * i) hm hs' ha (length_gsmpN i) (noOpen_gsmpN i)
    (phase_lt h hm (by omega)) (notOpen_in h hm ho (by omega))
  rw [wsum_gsmpN] at e1
  -- item `a + 2 i` is the `i`-th nonce
  have hn : (schedule p).getD (phaseItem0 p ph + (a + 2 * i)) default = .readW 1 nonceBytes := by
    rw [sched_phase h hm (by omega), hs', List.getD_append_right _ _ _ _ (by
      simp [ha, length_gsmpN])]
    rw [show a + 2 * i - (pre ++ gsmpN i).length = 0 by simp [ha, length_gsmpN]]
    obtain ⟨m, hm'⟩ : ∃ m, n - i = m + 1 := ⟨n - i - 1, by omega⟩
    rw [hm', gsmpN, List.replicate_succ, List.flatten_cons]
    rfl
  have hlt := phase_lt h hm (j := a + 2 * i + 1) (by omega)
  have e2 := posOf_succ hA (k := phaseItem0 p ph + (a + 2 * i)) (by omega) (notOpen_in h hm ho (by omega))
    (by rw [Nat.add_assoc]; exact notOpen_in h hm ho (by omega))
  rw [hn] at e2
  have l := lane_pos hA (k := phaseItem0 p ph + (a + 2 * i + 1)) (phase_lt h hm (by omega))
    (notOpen_in h hm ho (by omega))
  rw [l, show phaseItem0 p ph + (a + 2 * i + 1) = phaseItem0 p ph + (a + 2 * i) + 1 by omega, e2,
    show phaseItem0 p ph + (a + 2 * i) = phaseItem0 p ph + a + 2 * i by omega, e1]
  simp only [itemW, nonceBytes]

/-- **The tape's `r_i`** (`i < logN`): `8 · lane = posOf (tape + 1) + 80 i + 48`. -/
theorem tape_ri {i : Nat} (hi : i < p.logN) :
    8 * phaseLane p .tape (2 + 2 * i) = posOf p (phaseItem0 p .tape + 1) + 80 * i + 48 := by
  have e := gsmp_lane h hA (a := 1) (i := i) (mem_tape p) (pre := sepI)
    (post := List.flatten [rdE2 lanes, tapeLayersE2I p.logN]) (by simp [tapeIts, List.append_assoc]) rfl
    (noOpen_tape p) hi
  rw [phaseLane, show 2 + 2 * i = 1 + 2 * i + 1 by omega]
  exact e

/-- **`KS`'s instance coordinate `i`** (`i < ksLog`): `8 · lane = posOf ks + 80 i + 48`. -/
theorem ks_ri {i : Nat} (hi : i < p.ksLog) :
    8 * phaseLane p .ks (2 * i + 1) = posOf p (phaseItem0 p .ks) + 80 * i + 48 := by
  have e := gsmp_lane h hA (a := 0) (i := i) (mem_ks p) (pre := [])
    (post := rdE2 lanes ++ keccakE2I p.ksLog ++ smp rowSwitchStages)
    (by rw [ks_split]; simp [List.append_assoc]) rfl (noOpen_ks p) hi
  rw [Nat.add_zero, Nat.zero_add] at e
  rw [phaseLane]
  exact e

end Runs

end Lvm.E2Q
