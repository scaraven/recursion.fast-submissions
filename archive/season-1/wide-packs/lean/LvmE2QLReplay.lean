-- New for lvm2 E2F (slice S1, E2F-QH2): the `KS` link gadget replays V's `ksLinkD` (soundness direction): on a
-- streamed memory where its rows and assertion hold (gate on), V's phase from the matching cursor returns the gadget's
-- values, and keeps `ok` exactly when the ground answers pass `powOK`.
import LvmE2QLSem
import LvmE2QLRun

/-!
# `ksLink_replays`

With the first challenge's answer at lane `qa` (`8 qa = P + 48`, `P` the cursor's position) and the stream cells
`Σ`'s lanes (`Streamed`): V's `ksLinkD hk xl (rowsBK B K)` returns `(kchal, (ρ', final), vals)` = the gadget's
values, ends at `P + 80 (hk + 5) + 112 hk + 64`, and its `ok` is `okG ∧ okS ∧ ok` (the challenges' `powOK`s; the
check itself holds by `ksLinkG2_sound`).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q1 DM Lvm.E2V

variable {c : Ctx} {M : Mem}

theorem ld2_val {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {q : Nat} (hq : q + 1 < T) :
    (ld2 q).val M = fe2At sig (8 * q) := by
  show (⟨(FE.ofK (M.k q)).c₀, (FE.ofK (M.k (q + 1))).c₀⟩ : FE2) = ⟨kAt sig (8 * q), kAt sig (8 * q + 8)⟩
  rw [hS q (by omega), hS (q + 1) (by omega), show 8 * (q + 1) = 8 * q + 8 by ring]
  rfl

/-- **The `KS` link replays V's phase.** -/
theorem ksLink_replays {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {hk xl B K qa : Nat} {gate : Cell}
    (hg : gate.val M = 1) (hB : B - 1 < 2 ^ hk) (hK : K + 31 < 2 ^ hk) (s : RS) (hP : 8 * qa = rpos s + 48)
    (hT : ksLinkQV hk qa + 8 < T) :
    HsA c M (ksLinkG2 hk xl B K qa gate) (fun o =>
      (ksLinkD hk xl (rowsBK B K) sig s).1 =
          (o.kchal.map (C2.val M), (o.shift.map (C2.val M), o.final.val M), o.vals.map (C2.val M)) ∧
        (ksLinkD hk xl (rowsBK B K) sig s).2.ok =
          (okG gC1 sig (rpos s) (hk + 5) && (okS gC2 sig (rpos s + 80 * (hk + 5)) hk && s.ok)) ∧
        rpos (ksLinkD hk xl (rowsBK B K) sig s).2 = rpos s + 80 * (hk + 5) + 112 * hk + 64) := by
  refine hsA_mono (ksLinkG2_sound (xl := xl) (qa := qa) hg hB hK) fun o h => ?_
  obtain ⟨hk1, hs1, hv1, hf1, -, -, hchk⟩ := h
  have q1lt : ksLinkQ1 hk qa + 14 * hk ≤ ksLinkQV hk qa := by simp [ksLinkQV, roundLanes2]
  -- V's run
  have e : ksLinkD hk xl (rowsBK B K) = (samplesG gC1 (hk + 5) >>= fun kchal =>
      sumcheckD gC2 0 3 (List.replicate hk none) >>= fun kshift => readE2s 4 >>= fun vals =>
      require (kshift.2 == contShiftF (rowsBK B K) (kchal.take hk) kshift.1 * vals.getD 0 0 +
        eqEvalF (kchal.take hk) kshift.1 * (vals.getD 1 0 + vals.getD 2 0 + selXF xl kshift.1 * vals.getD 3 0)) >>=
      fun _ => pure (kchal, kshift, vals)) := rfl
  obtain ⟨g1, g2, g3⟩ := samplesG_run gC1 sig (hk + 5) s
  set s1 := (samplesG gC1 (hk + 5) sig s).2
  obtain ⟨u1, u2, u3⟩ := sumcheckD_run gC2 sig hk 0 s1 (ksLinkQ1 hk qa) (by rw [g2]; simp [ksLinkQ1]; omega)
  set s2 := (sumcheckD gC2 0 3 (List.replicate hk none) sig s1).2
  have hr := readE2s_run sig 4 s2
  -- the values
  have hKc : o.kchal.map (C2.val M) = (List.range (hk + 5)).map (fun i => fe2At sig (rpos s + 48 + 80 * i)) := by
    rw [hk1, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [ld2_val hS (by simp [ksLinkQV, ksLinkQ1, roundLanes2] at hT; omega)]
    congr 1; omega
  have hSh : o.shift.map (C2.val M) = (List.range hk).map (fun k => fe2At sig (rpos s1 + 80 + 112 * k)) := by
    rw [hs1, List.map_map, sc2Ans, List.map_map]
    refine List.map_congr_left fun k hk' => ?_
    have := List.mem_range.mp hk'
    simp only [Function.comp_apply]
    rw [ld2_val hS (by simp [ksLinkQV, roundLanes2] at hT ⊢; omega), g2]
    congr 1; simp [ksLinkQ1, roundLanes2]; omega
  have hFi : o.final.val M = scFold2 (fun k => fe2At sig (8 * k)) hk (ksLinkQ1 hk qa) 0 := by
    rw [hf1]
    refine scFold2_congr _ _ hk _ 0 fun j hj => ⟨?_, ?_, ?_⟩ <;>
      exact ld2_val hS (by simp [ksLinkQV, roundLanes2] at hT ⊢; omega)
  have hVa : o.vals.map (C2.val M) = (List.range 4).map (fun i => fe2At sig (rpos s2 + 40 + 16 * i)) := by
    rw [hv1, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [ld2_val hS (by omega), u2, g2]
    congr 1; simp [ksLinkQV, ksLinkQ1, roundLanes2]; omega
  have hreq : ∀ (b : Bool) (t : RS), require b sig t = ((), { t with ok := b && t.ok }) := fun _ _ => rfl
  have hgd : ∀ i < 4, (o.vals.getD i default).val M = (o.vals.map (C2.val M)).getD i 0 := by
    intro i hi
    rw [hv1]; simp [List.getD_eq_getElem?_getD, hi]
  have htk : (o.kchal.take hk).map (C2.val M) = (o.kchal.map (C2.val M)).take hk := List.map_take ..
  rw [htk, hgd 0 (by omega), hgd 1 (by omega), hgd 2 (by omega), hgd 3 (by omega), hKc, hSh, hVa, hFi] at hchk
  rw [hKc, hSh, hVa, hFi, e, dbind_run, g1, dbind_run, u1, dbind_run, hr, dbind_run, hreq, dpure_run]
  dsimp only
  rw [← hchk, beq_self_eq_true, Bool.true_and]
  refine ⟨rfl, ?_, ?_⟩
  swap
  · show s2.ent + (s2.msg + 16 * 4) = _
    have := u2; simp only [rpos] at this g2 ⊢; omega
  show s2.ok = _
  rw [u3, g3, g2]
  generalize okG gC1 sig (rpos s) (hk + 5) = a
  generalize okS gC2 sig (rpos s + 80 * (hk + 5)) hk = b
  cases a <;> cases b <;> rfl

end Lvm.Q2
