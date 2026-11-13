-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's A23 phase at `Φ_Q`: `qaccT` replays V_S's `dAccT` (AC-Q's
-- `qacc_sound` with the typed instance: `dk = 2`, 43 variables, `b = κ ++ r_x ++ r_y`, no `PUB` table).
import LvmQTypedHarB

/-!
# A23 at `Φ_Q` in the circuit

**`qaccT_replays`**: wherever `qaccT (aP P / 8) pb r_x r_y v`'s rows hold and assert (gate on: `PUB` lane 0 is
`1`), `dAccT` on the child's `PUB` (`pubOf vk c_L Σ'`), the point `r_x ++ r_y` and the matrix values `v` from any
state at `aP P` with `ok` keeps `ok` (`h(0) = acc_in'.y`, `h(1) = Σ_o eq(κ, o)·v_o`, the zero scalar), ends at
`mbP P`, and folds to the current proof's `acc_in` (`accC M pb`, its `PUB` cells).

* **`qaccT_facts`** (AC-Q's `qacc_facts` for `qaccT`): from lane `L`, the gadget's rows and assertions give the
  five equations on the stream view `feAt Σ` (`h₀`, `Σh`, the line, `h(t)`, the zero scalar).
* **`dAccT_run`**: `dAccT` from any state at position `Q`, as a function of `Q` (`accFold_run`'s form).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM

section helpers
open Lvm.QAcc Lvm.QSig

attribute [local irreducible] Lvm.QAcc.horner Lvm.QAcc.macChain Lvm.QAcc.linePts in
set_option maxHeartbeats 1000000 in
/-- **`qaccT`'s facts** (gate on, the child's stream bound): the five equations of A23 on `feAt Σ`. -/
theorem qaccT_facts {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} {L pb : Nat} {p : Ptr}
    (hS : Streamed M sig T) (hT : L + 166 < T) (hH : 11 + pubLanes ≤ T) (hg : M.k pb = 1)
    (rx ry v : List Cell) (hrx : rx.length = 20) (hry : ry.length = 21) (hv : v.length = 4)
    (h : Lvm.QSig.Ok c M (qaccT L pb rx ry v) p) :
    let K := (List.range 2).map fun i => feAt sig (8 * (L + 5 + 9 * i))
    let H := (List.range 44).map fun j => feAt sig (8 * (L + 18 + 5 + 3 * j))
    let t := feAt sig (8 * (L + 18 + 3 * 44 + 5))
    H.headD 0 = feAt sig (8 * accLane 43) ∧ sumE H = Lvm.dot (eqKernel K) (vs M v) ∧
      accLine ((List.range 43).map fun i => feAt sig (8 * accLane i)) (K ++ vs M (rx ++ ry)) t =
        (accC M pb).pt ∧
      polyEval H t = (accC M pb).y ∧ feAt sig (8 * (L + 18 + 3 * 44 + 9 + 5)) = 0 := by
  have hD : tVars = 43 := rfl
  have hA : accVars = 43 := rfl
  have hPL : pubLanes = 747 := rfl
  have hgv : (kc pb).val M = 1 := kc_val_one hg
  unfold qaccT at h
  obtain ⟨zo, p1, evo1, epo1, o1, h⟩ := okBindE h
  obtain ⟨hz1, hz2, hz0, hone⟩ := consts_spec o1.1
  have hzv : (consts pb p).1.1.val M = 0 := by rw [hz1]; exact hz0
  have hov : M.e (consts pb p).1.2.n = 1 := by rw [hz2]; exact hone
  have hov' : (consts pb p).1.2.val M = 1 := by rw [hz2]; exact hone
  rw [evo1] at hzv hov hov'
  -- κ
  obtain ⟨kb, p2, evo2, epo2, o2, h⟩ := okBindE h
  have hk := ldEsB_spec hS (qs := (List.range 2).map fun i => L + 5 + 9 * i)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq; omega) o2.1
  rw [evo2] at hk
  -- y'
  obtain ⟨y, p5, evo5, epo5, o5, h⟩ := okBindE h
  have hy := qyown_spec (by omega : 1 ≤ 2) (by rw [hv]; decide) hzv hov o5.1
  rw [evo5] at hy
  -- h', acc_in'
  obtain ⟨hb, p6, evo6, epo6, o6, h⟩ := okBindE h
  have hh := ldEsB_spec hS (qs := (List.range (tVars + 1)).map fun j => L + 18 + 5 + 3 * j)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq; omega) o6.1
  rw [evo6] at hh
  obtain ⟨ab, p7, evo7, epo7, o7, h⟩ := okBindE h
  have ha := ldEsB_spec hS (qs := (List.range (tVars + 1)).map accLane)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq
        simp only [accLane]; omega) o7.1
  rw [evo7] at ha
  obtain ⟨_vo8, p8, evo8, epo8, o8, h⟩ := okBindE h
  have e8 := assertEqE_spec o8 hgv
  obtain ⟨sh, p9, evo9, epo9, o9, h⟩ := okBindE h
  have hsh := macChain_spec _ _ _ o9.1
  rw [evo9] at hsh
  obtain ⟨_vo10, p10, evo10, epo10, o10, h⟩ := okBindE h
  have e10 := assertEqE_spec o10 hgv
  -- t', h'(t'), the line
  obtain ⟨t, p11, evo11, epo11, o11, h⟩ := okBindE h
  have ht := ldE_feAt hS (q := L + 18 + 3 * (tVars + 1) + 5) (by omega) o11.1
  rw [evo11] at ht
  obtain ⟨hv', p12, evo12, epo12, o12, h⟩ := okBindE h
  have hhv := horner_spec (c := c) (M := M) t zo.1 hzv ((List.range (tVars + 1)).map fun j => ec (hb + j)) p11 o12.1
  rw [evo12] at hhv
  obtain ⟨pts, p13, evo13, epo13, o13, h⟩ := okBindE h
  have hpt := linePts_spec (c := c) (M := M) t ((List.range tVars).map fun i =>
    (ec (ab + i), (((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).getD i (ec 0)))) p12 o13.1
  rw [evo13] at hpt
  -- the current acc_in
  obtain ⟨pc, p14, evo14, epo14, o14, h⟩ := okBindE h
  have hpc := ldEsB_val (c := c) (M := M) (qs := (List.range (tVars + 1)).map fun j => pb + 615 + 3 * j) (p := p13) o14.1
  rw [evo14] at hpc
  obtain ⟨_vo15, p15, evo15, epo15, o15, h⟩ := okBindE h
  have e15 := assertEqs_spec (c := c) (M := M) hgv ((List.range tVars).map fun i => (pts.getD i default, ec (pc + i))) p14 o15
  obtain ⟨_vo16, p16, evo16, epo16, o16, h⟩ := okBindE h
  have e16 := assertEqE_spec o16 hgv
  obtain ⟨zz, _qo17, evo17, epo17, o17, h⟩ := okBindE h
  have hz := ldE_feAt hS (q := L + 18 + 3 * (tVars + 1) + 9 + 5) (by omega) o17.1
  rw [evo17] at hz
  have e17 := assert0_spec h.2
  rw [hgv, one_mul] at e17
  have h44 : tVars + 1 = 44 := rfl
  rw [h44] at hh ha hpc ht hz hhv
  rw [hD] at e8 hpt e15 e16
  have hkv : ∀ i < 2, M.e (kb + i) = feAt sig (8 * (L + 5 + 9 * i)) := by
    intro i hi; rw [hk i (by simpa using hi)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]
  have hhv' : ∀ j < 44, M.e (hb + j) = feAt sig (8 * (L + 18 + 5 + 3 * j)) := by
    intro j hj; rw [hh j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hav : ∀ j < 44, M.e (ab + j) = feAt sig (8 * accLane j) := by
    intro j hj; rw [ha j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hHl : (List.range 44).map (fun j => feAt sig (8 * (L + 18 + 5 + 3 * j))) =
      ((List.range 44).map fun j => ec (hb + j)).map (Cell.val M) := by
    rw [List.map_map]; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp [hhv' j hj]
  have hKv : (List.range 2).map (fun i => M.e (kb + i)) = (List.range 2).map fun i => feAt sig (8 * (L + 5 + 9 * i)) := by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi; exact hkv i hi
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.range_succ_eq_map, List.map_cons, List.headD_cons]
    have := hhv' 0 (by omega)
    rw [Nat.add_zero] at this
    rw [← this, ← hav 43 (by omega)]; exact e8
  · have hsum : sh.val M = ((List.range 44).map fun j => feAt sig (8 * (L + 18 + 5 + 3 * j))).sum := by
      rw [hsh, hzv, zero_add, List.map_map, hHl, List.map_map]
      congr 1; apply List.map_congr_left; intro j _
      simp [hov']
    rw [sumE_eq, ← hsum, e10, hy, dot_eqKernel _ _ (by simp [vs, hv]), hKv]
    simp only [vs, List.length_map]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
  · have hbc : ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).map (Cell.val M) =
        (List.range 2).map (fun i => feAt sig (8 * (L + 5 + 9 * i))) ++ vs M (rx ++ ry) := by
      rw [← hKv, List.append_assoc, List.map_append, List.map_map]; rfl
    have hbl : ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).length = 43 := by
      simp [hrx, hry]
    rw [← hbc, ← ht]
    apply List.ext_getElem
    · simp [accLine, accC, List.length_zipWith, hrx, hry, hA]
    intro i h1 h2
    have hi : i < 43 := by simpa [accC, hA] using h2
    have hpi := hpt.2 i (by simpa using hi)
    rw [List.getD_eq_getElem ((List.range 43).map fun i =>
        (ec (ab + i), ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).getD i (ec 0))) _ (by simpa using hi),
      List.getElem_map, List.getElem_range,
      List.getD_eq_getElem ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry) _ (by rw [hbl]; exact hi)] at hpi
    have hq := e15 ((pts.getD i default, ec (pc + i))) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hpci : M.e (pc + i) = ⟨M.k (pb + 615 + 3 * i), M.k (pb + 615 + 3 * i + 1),
        M.k (pb + 615 + 3 * i + 2)⟩ := by
      rw [hpc i (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_range (by omega : i < 44)]
    simp only [Cell.val_E] at hq hpi
    rw [hq, hpci, hav i (by omega)] at hpi
    simp only [accLine, List.getElem_zipWith, List.getElem_map, List.getElem_range, accC]
    exact hpi.symm
  · rw [hHl, ← ht, ← hhv, e16, Cell.val_E, hpc 43 (by simp)]
    simp [accC, List.getD_eq_getElem?_getD, hA]
  · exact hz.symm.trans e17

/-- **`dAccT` from position `Q = ent + msg`**: `κ`, `h`, `t`, the zero scalar at fixed offsets. -/
theorem dAccT_run (pub : Pub) (rxy w : List FE) (sig : ByteArray) (s : RS) :
    TypedV.dAccT pub rxy w sig s =
      let K := (List.range 2).map fun i => feAt sig (s.ent + s.msg + 40 + 72 * i)
      let H := (List.range 44).map fun j => feAt sig (s.ent + s.msg + 184 + 24 * j)
      let t := feAt sig (s.ent + s.msg + 1240)
      (⟨accLine pub.accIn.pt (K ++ rxy) t, polyEval H t⟩,
        ⟨s.ent + s.msg + 1272, 24, (feAt sig (s.ent + s.msg + 1312) == 0) &&
          ((sumE H == Lvm.dot (eqKernel K) w) && ((H.headD 0 == pub.accIn.y) && s.ok))⟩) := by
  unfold TypedV.dAccT
  rw [Lvm.Q1.bind_run, Lvm.Q1.samples_run sig 2 _ (by norm_num), Lvm.Q1.bind_run, Lvm.Q1.readEs_run,
    Lvm.Q1.bind_run, Lvm.Q1.sampleE_run, Lvm.Q1.bind_run, Lvm.Q1.readE_run, Lvm.Q1.bind_run, require_run_lk,
    Lvm.Q1.bind_run, require_run_lk, Lvm.Q1.bind_run, require_run_lk, Lvm.Q1.pure_run]
  dsimp only [scalarsAt]
  rfl

/-- The child's `acc_in` (`pubOf`'s header) at the stream lanes `accLane`. -/
theorem pubOf_accIn (vk cL : Vector UInt8 32) (sig : ByteArray) :
    (pubOf vk cL sig).accIn.y = feAt sig (8 * accLane 43) ∧
      (pubOf vk cL sig).accIn.pt = (List.range 43).map fun i => feAt sig (8 * accLane i) := by
  have hacc : ∀ i, headerAt (offAcc + eBytes * i) = 8 * accLane i := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes, accLane]; omega
  refine ⟨?_, ?_⟩
  · show feAt sig (headerAt (offAcc + eBytes * 43)) = _; rw [hacc]
  · show (List.range 43).map (fun i => feAt sig (headerAt (offAcc + eBytes * i))) = _
    simp only [hacc]

end helpers

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **A23 at `Φ_Q` replayed** (soundness direction). -/
theorem qaccT_replays (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanes ≤ T) {pb : Nat}
    (hg : M.k pb = 1) {P : Nat} (hP : P % 8 = 0) (hT : mbP P + 40 ≤ 8 * T) (rx ry v : List Cell)
    (hrx : rx.length = 20) (hry : ry.length = 21) (hv : v.length = 4) (hE : ∀ x ∈ rx ++ ry ++ v, x.ty = .E)
    (ptr : Ptr) :
    Replays c M sig (TypedV.dAccT (pubOf vk cL sig) (vs M (rx ++ ry)) (vs M v)) (qaccT (aP P / 8) pb rx ry v) ptr
      (aP P) (mbP P) fun a _ => a = Lvm.QAcc.accC M pb := by
  intro h s hs hok
  have hD : tVars = 43 := rfl
  have h8 : 8 * (aP P / 8) = aP P := by
    have : aP P % 8 = 0 := by simp only [aP, rVP, rRP, wVP, wRP, wGP, zAbcP, zRP]; omega
    omega
  have hmb : mbP P = aP P + 1296 := by unfold mbP; rw [hD]
  obtain ⟨F1, F2, F3, F4, F5⟩ := qaccT_facts hS (by omega) hH hg rx ry v hrx hry hv h
  obtain ⟨hy, hpt⟩ := pubOf_accIn vk cL sig
  have hQ : s.ent + s.msg = 8 * (aP P / 8) := by rw [h8]; exact hs
  rw [dAccT_run]
  dsimp only
  rw [hQ]
  -- the reader's positions as the gadget's lanes
  have eK : (List.range 2).map (fun i => feAt sig (8 * (aP P / 8) + 40 + 72 * i)) =
      (List.range 2).map fun i => feAt sig (8 * (aP P / 8 + 5 + 9 * i)) :=
    List.map_congr_left fun i _ => congrArg _ (by omega)
  have eH : (List.range 44).map (fun j => feAt sig (8 * (aP P / 8) + 184 + 24 * j)) =
      (List.range 44).map fun j => feAt sig (8 * (aP P / 8 + 18 + 5 + 3 * j)) :=
    List.map_congr_left fun j _ => congrArg _ (by omega)
  have et : feAt sig (8 * (aP P / 8) + 1240) = feAt sig (8 * (aP P / 8 + 18 + 3 * 44 + 5)) :=
    congrArg _ (by omega)
  have ez : feAt sig (8 * (aP P / 8) + 1312) = feAt sig (8 * (aP P / 8 + 18 + 3 * 44 + 9 + 5)) :=
    congrArg _ (by omega)
  rw [eK, eH, et, ez]
  refine ⟨?_, ?_, ?_⟩
  · rw [F5, F1, hy, F2]
    simp [hok]
  · show 8 * (aP P / 8) + 1272 + 24 = mbP P
    omega
  · rw [hpt, F3, F4]

end

end Lvm.Har
