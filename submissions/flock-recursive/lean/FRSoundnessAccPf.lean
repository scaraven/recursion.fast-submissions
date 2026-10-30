-- New for `flock-recursive` (BLUEPRINT §3, A.9, A.10; stage S-G4, `hFin` steps 2b and 6).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessAccLvl
import FRSoundness4P4aSeg

/-!
# `hFin`: the finals' registers, by level, on the log

For a `FinIn` whose `outs` are the skeleton's (`fi.outs = skeleton.2.outs`), on an accepted
skeleton (`SkRun`), registers `R = #[] ++ y.1.toArray`, chain `es = fsOf tr items`:

* **`p1_facts`** (P1.i): `sRegs fi i` hold P1.i's challenges `sAt es i`, `p1Claim0` holds
  `rSum … 0`, `p1ClaimN` holds `rVal … (ℓᵢ − 1)`, the in-phase checks hold;
* **`pf_facts`** (Pf): `chals fi "Pf" 7` hold `pfP es`, `claim0`/`claimN` hold `rSum … 0` and
  `rVal … 6`, the in-phase checks hold;
* **`kc_facts`** (P3.i): `kcOf fi i` hold `kcAt es i`;
* **`ys_facts`** (Q.i): the fold registers `ysOf fi i` hold `dotKF (eqTab sᵢ) col_q`, the index
  registers below them `qPos κ es i q`, and each column has a path to its cap entry `capDig`
  on the log.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

/-! ## The levels' parameters (A.5's ladders) -/

/-- The ladder facts the views use (per kind and level, `decide` on the two ladders). -/
theorem lvl_facts (κ : Kind) {i : ℕ} (hi : i < 5) :
    (lvl κ i).t = (lvlStar i).t ∧ (lvl κ i).sib ≤ (lvlStar i).sib ∧
      (lvl κ i).cap = (lvlStar i).cap ∧ (lvl κ i).cap ≤ (lvl κ i).logN ∧
      ((lvl κ i).t - 1) / (lvl κ i).per < (lvlStar i).sq ∧ 0 < (lvl κ i).per ∧
      2 ^ hEll i ≤ colBytes i / 16 ∧ (lvl κ i).t < 2 ^ 9 ∧ 0 < (lvlStar i).sq := by
  cases κ <;> interval_cases i <;> decide

variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem lvOuts_eq {fi : FinIn} (hfi : fi.outs = skeleton.2.outs) (i k : ℕ) :
    lvOuts fi i k = skeleton.2.outs.getD (26 + 5 * i + k) [] := by
  rw [lvOuts, hfi, phaseIx_P1]

theorem phase_lvl_shape {i k : ℕ} (hi : i < 5) (hk : k < 5) :
    phases[26 + 5 * i + k]'(by rw [phases_length]; omega) = (levelPhases i)[k] := phases_lvl hi hk

theorem sAt_eq (es : Log) (i j : ℕ) : sAt es i j = chK (ansAt es (phStart (26 + 5 * i) + 2 * j + 1)) :=
  rfl

/-- **P1.i's registers on the log.** -/
theorem p1_facts (h : SkRun impl κ inp tr y) {fi : FinIn} (hfi : fi.outs = skeleton.2.outs)
    {i : ℕ} (hi : i < 5) :
    ∃ b, sRegs fi i = (List.range (hEll i)).map (fun j => b + 13 * j + 6) ∧
      (cAt (27 + 5 * i)).foldR = (List.range (hEll i)).map (fun j => b + 13 * j + 6) ∧
      (∀ j < hEll i, rd (#[] ++ y.1.toArray) (b + 13 * j + 6) = .k (sAt (fsOf tr items) i j)) ∧
      rd (#[] ++ y.1.toArray) (p1Claim0 fi i) = .k (rSum (p1Start i) (fsOf tr items) 0) ∧
      rd (#[] ++ y.1.toArray) (p1ClaimN fi i) =
        .k (rVal (p1Start i) (fsOf tr items) (hEll i - 1)) ∧
      (∀ x ∈ lvOuts fi i 0, x < (#[] ++ y.1.toArray).size) ∧
      ∀ l, l + 1 < hEll i → rSum (p1Start i) (fsOf tr items) (l + 1) =
        rVal (p1Start i) (fsOf tr items) l := by
  have hn : 26 + 5 * i < phases.length := by rw [phases_length]; omega
  have hp : phases[26 + 5 * i] = ⟨"P1", .rounds fP1 (hEll i) 2 true fun k => (lvl k i).ell⟩ := by
    have := phase_lvl_shape hi (show 0 < 5 by norm_num)
    simp only [Nat.add_zero] at this; rw [this]; rfl
  have hsh : phases[26 + 5 * i].shape = .rounds fP1 (hEll i) 2 true fun k => (lvl k i).ell := by
    rw [hp]
  have hnm : initClaim phases[26 + 5 * i].name = .free := by rw [hp]; rfl
  obtain ⟨b, hout, hfold, -, h0, hrs, hlast, hchk⟩ := rounds_view h hn hsh hnm (by decide)
    (hEll_pos hi) (by rw [lvl_ell κ hi]) (by omega)
  have hl0 : lvOuts fi i 0 = (b + 2) :: (List.range (hEll i)).map (fun j => b + 13 * j + 6) ++
      [b + 13 * hEll i + 2] := by rw [lvOuts_eq hfi, Nat.add_zero, hout]
  refine ⟨b, ?_, ?_, fun j hj => ?_, ?_, ?_, ?_, hchk⟩
  · rw [sRegs, hl0, List.cons_append, List.drop_one, List.tail_cons]; exact take_rs b (hEll i) _
  · rw [show 27 + 5 * i = 26 + 5 * i + 1 by ring, hfold]
  · rw [hrs j hj]; rfl
  · rw [p1Claim0, hl0, List.cons_append, List.headD_cons, h0]; rfl
  · rw [p1ClaimN, hl0, List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_singleton]
    simpa [p1Start] using hlast
  · rw [lvOuts_eq hfi]; exact skeleton_out_lt h.ref _

/-- **Pf's registers on the log.** -/
theorem pf_facts (h : SkRun impl κ inp tr y) {fi : FinIn} (hfi : fi.outs = skeleton.2.outs) :
    (∀ v < 7, rd (#[] ++ y.1.toArray) ((chals fi "Pf" 7).getD v 0) = .k (pfP (fsOf tr items) v)) ∧
      (chals fi "Pf" 7).length = 7 ∧
      rd (#[] ++ y.1.toArray) (claim0 fi "Pf") = .k (rSum pfStart (fsOf tr items) 0) ∧
      rd (#[] ++ y.1.toArray) (claimN fi "Pf") = .k (rVal pfStart (fsOf tr items) 6) ∧
      (∀ x ∈ outsOf fi "Pf", x < (#[] ++ y.1.toArray).size) ∧
      ∀ l, l + 1 < 7 → rSum pfStart (fsOf tr items) (l + 1) = rVal pfStart (fsOf tr items) l := by
  have hn : 51 < phases.length := by rw [phases_length]; omega
  have hsh : phases[51].shape = .rounds fPf 7 2 true fun _ => 7 := by rw [phases_pf]; rfl
  have hnm : initClaim phases[51].name = .free := by rw [phases_pf]; rfl
  obtain ⟨b, hout, -, -, h0, hrs, hlast, hchk⟩ := rounds_view h hn hsh hnm (by decide)
    (by norm_num) le_rfl (by norm_num)
  have ho : outsOf fi "Pf" = (b + 2) :: (List.range 7).map (fun j => b + 13 * j + 6) ++
      [b + 13 * 7 + 2] := by rw [outsOf, hfi, phaseIx_Pf, hout]
  have hc : chals fi "Pf" 7 = (List.range 7).map (fun j => b + 13 * j + 6) := by
    rw [chals, ho, List.cons_append, List.drop_one, List.tail_cons]; exact take_rs b 7 _
  refine ⟨fun v hv => ?_, by rw [hc]; simp, ?_, ?_, ?_, hchk⟩
  · rw [hc, List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map, List.getElem_range,
      hrs v hv]
    simp [pfP, rchs2, List.getD_eq_getElem?_getD, hv, rch2, pfStart]
  · rw [claim0, ho, List.cons_append, List.headD_cons, h0]; rfl
  · rw [claimN, ho, List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_singleton]
    simpa [pfStart] using hlast
  · rw [outsOf, hfi, phaseIx_Pf]; exact skeleton_out_lt h.ref _

/-- **P3.i's first nine coordinates on the log** (`κ_c`). -/
theorem kc_facts (h : SkRun impl κ inp tr y) {fi : FinIn} (hfi : fi.outs = skeleton.2.outs)
    {i : ℕ} (hi : i < 5) :
    (kcOf fi i).map (fun x => (rd (#[] ++ y.1.toArray) x).toF) =
        (List.range 9).map (kcAt (fsOf tr items) i) ∧
      ∀ x ∈ kcOf fi i, x < (#[] ++ y.1.toArray).size := by
  have hn : 26 + 5 * i + 4 < phases.length := by rw [phases_length]; omega
  have hsh : phases[26 + 5 * i + 4].shape = .squeezes 5 (.coords fun _ => 9) := by
    rw [phase_lvl_shape hi (by norm_num)]; rfl
  obtain ⟨b, hout, -, hv⟩ := coords_view h hn hsh (by norm_num)
  have hk : kcOf fi i = (List.range 9).map (fun x => b + 3 * (x / 2) + 1 + x % 2) := by
    rw [kcOf, lvOuts_eq hfi, hout, List.drop_one, List.tail_cons, ← List.map_take,
      List.take_range]; rfl
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hk, List.map_map]
    refine List.map_congr_left fun v hvm => ?_
    have hv9 := List.mem_range.1 hvm
    simp only [Function.comp_apply]
    rw [hv v (by omega), kcAt, coordAt, fAt]
    have hp := phStart_pos (n := 30 + 5 * i) (by omega) (by rw [phases_length]; omega)
    rw [show phStart (30 + 5 * i) - 1 + 1 + v / 2 = phStart (26 + 5 * i + 4) + v / 2 by
      rw [show 26 + 5 * i + 4 = 30 + 5 * i by ring]; omega]
    rfl
  · rw [kcOf] at hx
    exact skeleton_out_lt h.ref _ x (by
      rw [lvOuts_eq hfi] at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx))

end FR.Snd
