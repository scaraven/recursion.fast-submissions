-- New for lvm2 E2F (slice S1, E2F-QH2): the CHwire gadget against V's `wireD` (`LvmDecideE2`): the target block's
-- closed form is V's `wireTargetD`, given the tape claim's meaning in the cells.
import LvmE2QWSem
import LvmE2QLRun
import LvmE2QLReplay
import LvmE2QPinSem
import LvmQRingRowReplay

/-!
# The wire against V

* `padDot_split2`: `⟨ω, Pad43(y)⟩ = c43(ω) + Σ_{p<256} ω_{8+p}·y_p` (V's `padDotF_split` with the constant positions
  `0, 1, 6, 264, 1087`);
* **`targetF_eq`**: with the claim's value, `μ`, point and weights (`hω`: `weights_j = ω_j`, H1's tape output) in the
  cells and `s'`'s bits in `sbv`, `targetF … (n − 1) = wireTargetD (sBitsD s) n claim`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.E2V Finset DM

theorem pad43Bit_false2 (j : ℕ) :
    Lvm.KG.pad43Bit (fun _ ↦ false) j = decide (j ∈ ({0, 1, 6, 264, 1087} : Finset ℕ)) := by
  unfold Lvm.KG.pad43Bit
  by_cases h1 : j < 8
  · rw [ite_eq_left h1]
    interval_cases j <;> rfl
  · rw [ite_eq_right h1]
    by_cases h2 : j < 264
    · rw [ite_eq_left h2]
      exact (decide_eq_false (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)).symm
    · rw [ite_eq_right h2]
      exact decide_eq_decide.2 (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)

theorem padDot_false2 (ω : List FE2) :
    E2V.padDotF ω (fun _ ↦ false) = ω.getD 0 0 + ω.getD 1 0 + ω.getD 6 0 + ω.getD 264 0 + ω.getD 1087 0 := by
  have hb : ∀ j, ω.getD j 0 * (E2V.bitF (Lvm.KG.pad43Bit (fun _ ↦ false) j) : FE2) =
      if j ∈ ({0, 1, 6, 264, 1087} : Finset ℕ) then ω.getD j 0 else 0 := by
    intro j
    rw [pad43Bit_false2]
    by_cases h : j ∈ ({0, 1, 6, 264, 1087} : Finset ℕ) <;> simp [h, E2V.bitF]
  rw [E2V.padDotF, sumF_eq_sum, lsum_range, Finset.sum_congr rfl fun j _ ↦ hb j, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 fun x hx ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega]
  simp [add_assoc]

theorem padDot_split2 (ω : List FE2) (y : ℕ → Bool) :
    E2V.padDotF ω y = E2V.padDotF ω (fun _ ↦ false) + ∑ p ∈ range 256, ω.getD (8 + p) 0 * E2V.bitF (y p) := by
  have hj : ∀ j, (E2V.bitF (Lvm.KG.pad43Bit y j) : FE2) = E2V.bitF (Lvm.KG.pad43Bit (fun _ ↦ false) j) +
      if 8 ≤ j ∧ j < 264 then E2V.bitF (y (j - 8)) else 0 := by
    intro j
    unfold Lvm.KG.pad43Bit
    split_ifs <;> first | omega | simp [E2V.bitF]
  rw [E2V.padDotF, E2V.padDotF, sumF_eq_sum, sumF_eq_sum, lsum_range, lsum_range,
    Finset.sum_congr rfl fun j _ ↦ by rw [hj j, mul_add], Finset.sum_add_distrib]
  refine congrArg (HAdd.hAdd _) ?_
  rw [show 1600 = 8 + (256 + 1336) from rfl, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ j ∈ range 8, ω.getD j 0 * (if 8 ≤ j ∧ j < 264 then (E2V.bitF (y (j - 8)) : FE2) else 0) = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [if_neg (by have := Finset.mem_range.1 hj; omega), mul_zero]
  have h3 : ∑ j ∈ range 1336, ω.getD (8 + (256 + j)) 0 *
      (if 8 ≤ 8 + (256 + j) ∧ 8 + (256 + j) < 264 then (E2V.bitF (y (8 + (256 + j) - 8)) : FE2) else 0) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by rw [if_neg (by omega), mul_zero]
  rw [h1, h3, zero_add, add_zero]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [if_pos (by have := Finset.mem_range.1 hp; omega), Nat.add_sub_cancel_left]

variable {M : Mem}

/-- **The target block computes V's `wireTargetD`.** -/
theorem targetF_eq (P : ℕ) (cv : ℕ → C2) (claim : E2V.KClaim FE2) (s : List FK) (n : ℕ) (sbv : List FE2)
    (hv : claim.value = (cv 0).val M) (hmu : claim.mu = cvMu M cv) (hpt : claim.point = cvRho M P cv)
    (hω : ∀ j < 1600, claim.weights.getD j 0 = omegaF M P cv j)
    (hsb : sbv = (List.range 256).map fun p => E2V.bitF (sBitsD s p)) :
    targetF M P cv sbv (n - 1) = wireTargetD (sBitsD s) n claim := by
  have hi : E2V.iotaF claim.point claim.mu 0 = io0F M P cv := by
    rw [E2V.iotaF, hpt, hmu, io0F]
  rw [wireTargetD, hi, padDot_split2, padDot_false2, hω 0 (by norm_num), hω 1 (by norm_num), hω 6 (by norm_num),
    hω 264 (by norm_num), hω 1087 (by norm_num), hv, hpt, hmu, targetF, c43F]
  have hs : ((List.range 256).map fun p => omegaF M P cv (8 + p) * sbv.getD p 0).sum =
      ∑ p ∈ range 256, claim.weights.getD (8 + p) 0 * E2V.bitF (sBitsD s p) := by
    rw [lsum_range]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.mem_range.1 hp
    rw [hω (8 + p) (by omega), hsb]
    simp [List.getD_eq_getElem?_getD, hp']
  rw [hs]

/-- The slot weights from `eq(τ, ·)`'s table (`|τ| = 2`) are V's `E2V.slotWF 2 (E2V.dWF ω)`. -/
theorem slotW_eq (τ ω : List FE2) (hτ : τ.length = 2) (f : ℕ → FE2) (hω : ∀ j < 1600, ω.getD j 0 = f j)
    (zz : ℕ) (hzz : zz < 64) :
    ((List.range 4).map fun o => (eqKernelF τ).getD o 0 * f (8 + 64 * o + zz)).sum =
      E2V.slotWF 2 (E2V.dWF ω) τ zz := by
  rw [E2V.slotWF, sumF_eq_sum]
  refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
  have ho' := List.mem_range.mp ho
  rw [eqKernelF_getD, if_pos (by rw [hτ]; norm_num; omega), E2V.dWF, hω _ (by omega)]

open Lvm.Q1 in
/-- **The wire gadget replays V's `wireD`** (gate on): from the cursor whose first message is at lane `qw`, V's wiring
sumcheck, `g_D`, slot sumcheck and slices are the gadget's; V's two checks hold; `ok` gains only the rounds' `powOK`s.
The claim's meaning in the cells (`hv`, `hmu`, `hpt`, `hω`), `n − 1`'s bits in `mb` and `s'`'s bits in `sb` are
hypotheses (H4's tape output, Q_sig's bits). -/
theorem wire_replays {c : Ctx} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {P qw : ℕ} {cv : ℕ → C2}
    {mb sb : List Cell} {zk gate : Cell} (claim : E2V.KClaim FE2) (s' : List FK) (n sbsel dsel : ℕ)
    (hzk : zk.val M = 0) (hg : gate.val M = 1) (hsb : sb.length = 256)
    (hmb : (mb.map fun b => kC2 b zk).map (C2.val M) = bitsF (n - 1) (P + 5)) (hn : n - 1 < 2 ^ (P + 5))
    (hsbv : (sb.map fun b => kC2 b zk).map (C2.val M) = (List.range 256).map fun p => E2V.bitF (sBitsD s' p))
    (hv : claim.value = (cv 0).val M) (hmu : claim.mu = cvMu M cv) (hpt : claim.point = cvRho M P cv)
    (hω : ∀ j < 1600, claim.weights.getD j 0 = omegaF M P cv j)
    (s : RS) (hP : 8 * qw = rpos s + 40) (hT : (wireLanes (P + 5) qw).slices + 128 < T) :
    HsA c M (wireG2 P qw cv mb sb zk gate) (fun o =>
      (wireD (P + 5) sbsel dsel s' n claim sig s).1.1 = (o.sigma.map (C2.val M), o.final.val M) ∧
      (wireD (P + 5) sbsel dsel s' n claim sig s).1.2.1 = [o.gD.val M] ∧
      (wireD (P + 5) sbsel dsel s' n claim sig s).1.2.2.1.1 = (o.tau.map (C2.val M)) ∧
      (wireD (P + 5) sbsel dsel s' n claim sig s).1.2.2.2.1 = o.slices.map (C2.val M) ∧
      (wireD (P + 5) sbsel dsel s' n claim sig s).2.ok =
        (okS gC2 sig (rpos s) (P + 5) && (okS gC2 sig (rpos s + 112 * (P + 5) + 16) 2 && s.ok)) ∧
      (wireD (P + 5) sbsel dsel s' n claim sig s).1.2.2.1.2 =
        scFold2 (fun k => fe2At sig (8 * k)) 2 (wireLanes (P + 5) qw).slot (o.gD.val M) ∧
      (wireD (P + 5) sbsel dsel s' n claim sig s).1.2.2.2.2 =
        rowValD (o.sigma.map (C2.val M) ++ o.tau.map (C2.val M) ++ selPtF dsel sbsel) (o.slices.map (C2.val M))
          (eqKernel ((List.range 7).map fun k => feAt sig (rpos s + 112 * (P + 5) + 1304 + 72 * k))) ∧
      rpos (wireD (P + 5) sbsel dsel s' n claim sig s).2 = rpos s + 112 * (P + 5) + 1768) := by
  refine hsA_mono (wireG2_sound P qw cv mb sb zk gate (n - 1) hzk hg hsb hmb hn) fun o h => ?_
  obtain ⟨hσ, hfin, hgD, hfin2, hτ, hsl, hslot⟩ := h
  set w := P + 5 with hw
  set L := wireLanes w qw with hL
  have ldv : ∀ q, q + 1 < T → (ld2 q).val M = fe2At sig (8 * q) := fun q hq => ld2_val hS hq
  -- V's run
  have e : wireD w sbsel dsel s' n claim = (sumcheckD gC2 (wireTargetD (sBitsD s') n claim) 3 (List.replicate w none) >>=
      fun sc => readE2s 1 >>= fun g => require (sc.2 == E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0) >>=
      fun _ => slotD 2 sbsel dsel (E2V.dWF claim.weights) sc.1 (g.getD 0 0) >>= fun d => pure (sc, g, d)) := rfl
  have es : ∀ (W : ℕ → ℕ → FE2) (pt : List FE2) (v : FE2), slotD 2 sbsel dsel W pt v =
      (sumcheckD gC2 v 3 (List.replicate 2 none) >>= fun sl => readE2s 64 >>= fun sv =>
        require (sl.2 == E2V.sumF ((List.range 64).map fun z => E2V.slotWF 2 W sl.1 z * sv.getD z 0)) >>= fun _ =>
        rowSwitchD (pt ++ sl.1 ++ selPtF dsel sbsel) sv >>= fun row => pure (sl, sv, row)) := fun _ _ _ => rfl
  have hreq : ∀ (b : Bool) (t : RS), require b sig t = ((), { t with ok := b && t.ok }) := fun _ _ => rfl
  obtain ⟨u1, u2, u3⟩ := sumcheckD_run gC2 sig w (wireTargetD (sBitsD s') n claim) s qw hP
  -- the wiring sumcheck's values
  have hlanes : ∀ k < w, qw + 14 * k + 5 + 1 < T := by
    intro k hk; simp only [hL, wireLanes, roundLanes2] at hT; omega
  have hSig : o.sigma.map (C2.val M) = (List.range w).map (fun k => fe2At sig (rpos s + 80 + 112 * k)) := by
    rw [hσ, List.map_map, sc2Ans, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hk' := List.mem_range.mp hk
    simp only [Function.comp_apply]
    rw [ldv _ (by simp only [hL, wireLanes, roundLanes2] at hT ⊢; omega),
      show 8 * (qw + roundLanes2 * k + 5) = rpos s + 80 + 112 * k by simp only [roundLanes2]; omega]
  have hFin : o.final.val M = scFold2 (fun k => fe2At sig (8 * k)) w qw (wireTargetD (sBitsD s') n claim) := by
    rw [hfin, hsbv, targetF_eq P cv claim s' n _ hv hmu hpt hω rfl]
    refine scFold2_congr _ _ w qw _ fun j hj => ⟨?_, ?_, ?_⟩ <;>
      exact ldv _ (by simp only [hL, wireLanes, roundLanes2] at hT ⊢; omega)
  rw [e, dbind_run, dbind_run, readE2s_run, dbind_run, hreq, dbind_run, es, dbind_run, dbind_run, readE2s_run,
    dbind_run, hreq, dbind_run, dpure_run, dpure_run]
  dsimp only
  generalize hR : sumcheckD gC2 (wireTargetD (sBitsD s') n claim) 3 (List.replicate w none) sig s = R at u1 u2 u3 ⊢
  obtain ⟨⟨l1, f1⟩, st1⟩ := R
  simp only [Prod.mk.injEq] at u1 u2 u3 ⊢
  obtain ⟨rfl, rfl⟩ := u1
  have hgv : fe2At sig (rpos st1 + 40) = o.gD.val M := by
    rw [hgD, ldv _ (by simp only [hL, wireLanes, roundLanes2] at hT ⊢; omega), u2,
      show 8 * L.gD = rpos s + 112 * w + 40 by simp only [hL, wireLanes, roundLanes2]; omega]
  have hg1 : ((List.range 1).map fun i => fe2At sig (rpos st1 + 40 + 16 * i)) = [o.gD.val M] := by
    simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, Nat.add_zero, hgv]
  rw [hg1]
  simp only [List.getD_cons_zero]
  have hc1 : (scFold2 (fun k => fe2At sig (8 * k)) w qw (wireTargetD (sBitsD s') n claim) ==
      E2V.msEvalF claim.point claim.mu ((List.range w).map fun k => fe2At sig (rpos s + 80 + 112 * k)) 0 (n - 1) *
        o.gD.val M) = true := by
    rw [beq_iff_eq, ← hFin, hfin2, hpt, hmu, hSig]
  rw [hc1, Bool.true_and]
  refine ⟨⟨hSig.symm, hFin.symm⟩, trivial, ?_⟩
  have hst2 : rpos (⟨st1.ent, st1.msg + 16 * 1, st1.ok⟩ : RS) = rpos s + 112 * w + 16 := by
    simp only [rpos] at u2 ⊢; omega
  obtain ⟨v1, v2, v3⟩ := sumcheckD_run gC2 sig 2 (o.gD.val M) ⟨st1.ent, st1.msg + 16 * 1, st1.ok⟩ L.slot
    (by rw [hst2]; simp only [hL, wireLanes, roundLanes2]; omega)
  generalize hR2 : sumcheckD gC2 (o.gD.val M) 3 (List.replicate 2 none) sig ⟨st1.ent, st1.msg + 16 * 1, st1.ok⟩ = R2
    at v1 v2 v3 ⊢
  obtain ⟨⟨l2, f2⟩, st3⟩ := R2
  simp only [Prod.mk.injEq] at v1 v2 v3 ⊢
  obtain ⟨rfl, rfl⟩ := v1
  have hTau : ((List.range 2).map fun k => fe2At sig (rpos (⟨st1.ent, st1.msg + 16 * 1, st1.ok⟩ : RS) + 80 + 112 * k)) =
      o.tau.map (C2.val M) := by
    rw [hτ, List.map_map, sc2Ans, List.map_map, hst2]
    refine List.map_congr_left fun k hk => ?_
    have hk' := List.mem_range.mp hk
    simp only [Function.comp_apply]
    rw [ldv _ (by simp only [hL, wireLanes, roundLanes2] at hT ⊢; omega),
      show 8 * (L.slot + roundLanes2 * k + 5) = rpos s + 112 * w + 16 + 80 + 112 * k by
        simp only [hL, wireLanes, roundLanes2]; omega]
  have hSv : ((List.range 64).map fun i => fe2At sig (rpos st3 + 40 + 16 * i)) = o.slices.map (C2.val M) := by
    rw [hsl, slices2, List.map_map, v2, hst2]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [ldv _ (by omega), show 8 * (L.slices + 2 * i) = rpos s + 112 * w + 16 + 112 * 2 + 40 + 16 * i by
        simp only [hL, wireLanes, roundLanes2]; omega]
  rw [hTau, hSv]
  have hτl : (o.tau.map (C2.val M)).length = 2 := by rw [hτ]; simp [sc2Ans]
  have hc2 : (scFold2 (fun k => fe2At sig (8 * k)) 2 L.slot (o.gD.val M) ==
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 2 (E2V.dWF claim.weights) (o.tau.map (C2.val M)) z *
        (o.slices.map (C2.val M)).getD z 0)) = true := by
    rw [beq_iff_eq, sumF_eq_sum]
    have hl : scFold2 (fun k => fe2At sig (8 * k)) 2 L.slot (o.gD.val M) =
        scFold2 (fun k => (ld2 k).val M) 2 L.slot (o.gD.val M) := by
      refine scFold2_congr _ _ 2 _ _ fun j hj => ⟨?_, ?_, ?_⟩ <;>
        exact (ldv _ (by simp only [hL, wireLanes, roundLanes2] at hT ⊢; omega)).symm
    rw [hl, hslot]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [slotW_eq _ _ hτl (omegaF M P cv) hω zz hzz', hsl]
    simp [slices2, List.getD_eq_getElem?_getD, hzz']
  rw [hc2, Bool.true_and, rowSwitchD_run]
  dsimp only
  have hp3 : rpos (⟨st3.ent, st3.msg + 16 * 64, st3.ok⟩ : RS) = rpos s + 112 * w + 1264 := by
    simp only [rpos] at v2 hst2 ⊢; omega
  refine ⟨rfl, rfl, ?_, rfl, ?_, ?_⟩
  · rw [v3, hst2, u3]
    generalize okS gC2 sig (rpos s + 112 * w + 16) 2 = a
    generalize okS gC2 sig (rpos s) w = b
    cases a <;> cases b <;> cases s.ok <;> rfl
  · rw [hp3, ← hSig]
  · rw [show rpos (⟨rpos ⟨st3.ent, st3.msg + 16 * 64, st3.ok⟩ + 504, 0, _⟩ : RS) =
      rpos ⟨st3.ent, st3.msg + 16 * 64, st3.ok⟩ + 504 from Nat.add_zero _, hp3]

end Lvm.Q2
