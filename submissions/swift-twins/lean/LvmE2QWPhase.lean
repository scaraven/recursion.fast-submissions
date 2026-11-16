-- New for lvm2 E2-FT (E2F-QH5): the `PhaseAt` facts of QH2's front gadgets for `harithF20` (E2F-C's SPEC, in roll 11's
-- `LvmQAsmHarP47.tape_phase`/`wire_phase` form): the root pin, the wiring with its row switch, `KS`'s row switch, the
-- `KS` link; and `tapeD`/`callerD` cut into the GKR part (E2F-QH4's) and these.
import LvmE2QKTapeEq
import LvmQAsmHarTop
import LvmE2QWSem
import LvmE2QLRun
import LvmE2QLReplay
import LvmE2QPinSem
import LvmQRingRowReplay

-- ===== merged from `LvmE2QWReplay` (VQ module merge: `LvmE2QWReplay.lean` removed) =====
section
-- New for lvm2 E2F (slice S1, E2F-QH2): the CHwire gadget against V's `wireD` (`LvmDecideE2`): the target block's
-- closed form is V's `wireTargetD`, given the tape claim's meaning in the cells.

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
end
-- ===== end of `LvmE2QWReplay` =====

/-!
# The front gadgets' phases at S2GF

Every lemma takes the gadget's rows at its pointer (`SegsHold`, and `SegsAssert` where the gadget asserts), the stream
cells (`Streamed`), the gate, the inputs' meaning, and the proof-of-work answers (`PowOkV` on the gadget's
`(answer lane, g)` list, which the PoW blocks give: `powBlk_ok`); it concludes V's phase as `PhaseAt` with a fixed
value, and the gadget's output cells as that value's fields.

* combinators: `phaseAt_bind`, `phaseAt_pure`, `phaseAt_require`; the reads (`sepE2_phase`, `samplesG_phase`,
  `readE2s_phase`);
* **`pin_phase`**: `pinD ν`;
* **`rowSwitch_phase`**: `rowSwitchD z sv` (`KS`'s: the row words `t_j = rowWordD sv j` from `rowAux_sound`);
* **`wire_phase`**: `wireD (P + 5) …` with the wiring's row switch, the claim represented (`Rep2`, E2F-QH4's);
* **`ksLink_phase`**: `ksLinkD hk xl contRowsF` (`contRowsF_eq`);
* **`tapeD_phase`**, **`callerD_phase`**: `tapeD` from the separator, `r`, the scalars, `tapeGkrD`'s phase
  (E2F-QH4's `tape_phase2`), `n`'s range and `wire_phase`; `callerD` from `r`, the scalars, `verifyKeccakD`'s phase
  (E2F-QH4's) and `rowSwitch_phase`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q1 DM Lvm.E2V

variable {c : Ctx} {M : Mem}

/-! ## Combinators -/

theorem phaseAt_bind {α β : Type} {m : DM α} {f : α → DM β} {sig : ByteArray} {P P' P'' : Nat} {a : α} {b : β}
    (hm : PhaseAt m sig P P' a) (hf : PhaseAt (f a) sig P' P'' b) : PhaseAt (m >>= f) sig P P'' b := by
  intro s hs hok
  obtain ⟨h1, h2, h3⟩ := hm s hs hok
  rw [dbind_run, h1]
  exact hf _ h3 h2

theorem phaseAt_pure {α : Type} {a : α} {sig : ByteArray} {P : Nat} : PhaseAt (pure a : DM α) sig P P a :=
  fun _ hs hok => ⟨rfl, hok, hs⟩

theorem phaseAt_require {b : Bool} (hb : b = true) {sig : ByteArray} {P : Nat} : PhaseAt (require b) sig P P () :=
  fun s hs hok => ⟨rfl, by show (b && s.ok) = true; rw [hb, hok]; rfl, hs⟩

/-- The values of `n` ground challenges from position `P` (answers at `P + 48 + 80 i`). -/
def sampsG (sig : ByteArray) (P n : Nat) : List FE2 := (List.range n).map fun i => fe2At sig (P + 48 + 80 * i)

/-- `n` `E2` scalars from position `P`. -/
def readsE2 (sig : ByteArray) (P n : Nat) : List FE2 := (List.range n).map fun i => fe2At sig (P + 40 + 16 * i)

/-- `n` ground challenges (`g`) from the answer lane `q`, `(answer lane, g)` (lanes `q + 10 i`). -/
def chalsG (q g n : Nat) : List (Nat × Nat) := (List.range n).map fun i => (q + 10 * i, g)

/-! ## The pin -/

theorem pinD_st (sig : ByteArray) (s : RS) {nu : Nat} (hn : 1 ≤ nu) :
    (pinD nu sig s).2 = ⟨s.ent + s.msg + 72 * nu, 24, s.ok⟩ := by
  show (readE sig (samples nu sig s).2).2 = _
  rw [samples_run sig nu s hn, readE_run]

/-- **The pin's phase**: from `P` (`8 qz = P + 40`, value lane `qa = qz + 9 ν`) V's `pinD ν` ends at
`P + 72 ν + 24`; the gadget's claim is its value. -/
theorem pin_phase {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {nu qz qa P : Nat} (hn : 1 ≤ nu)
    (hP : 8 * qz = P + 40) (hqa : qa = qz + 9 * nu) (hz : qz + 9 * nu + 2 < T) (ha : qa + 2 < T) {p : Ptr}
    (hh : SegsHold c M p (pinG nu qz qa p).2) :
    PhaseAt (pinD nu) sig P (P + 72 * nu + 24) (pinD nu sig ⟨P, 0, true⟩).1 ∧
      (pinG nu qz qa p).1.val M = (.main, (pinD nu sig ⟨P, 0, true⟩).1) := by
  refine ⟨fun s hs hok => ⟨?_, ?_, ?_⟩, pin_replays hS ⟨P, 0, true⟩ hn hP hqa hz ha p hh⟩
  · have hs' : s.ent + s.msg = P := hs
    rw [pinD_run sig s hn, pinD_run sig _ hn, hs']
    rfl
  · rw [pinD_st sig s hn]; exact hok
  · rw [pinD_st sig s hn]; show s.ent + s.msg + 72 * nu + 24 = _; rw [show s.ent + s.msg = P from hs]

/-! ## The row switch -/

/-- **A row switch's phase**: from `P` (`8 qr = P + 40`) V's `rowSwitchD z sv` ends at `P + 504` with the value
`rowValD z sv` of the gadget's `eq(r'', ·)`, whose target is the gadget's; `t_j = rowWordD sv j` (`rowAux_sound`). -/
theorem rowSwitch_phase {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {qr tB z o : Nat} (hz : M.e z = 0)
    (ho : M.e o = 1) (hT : qr + 9 * 6 + 2 < T) {p : Ptr} (hh : SegsHold c M p (rowG qr tB z o p).2) {P : Nat}
    (hP : 8 * qr = P + 40) (zz sv : List FE2) (ht : ∀ j < 128, M.k (tB + j) = rowWordD sv j) :
    PhaseAt (rowSwitchD zz sv) sig P (P + 504) (rowValD zz sv ((rowG qr tB z o p).1.eqR.map (Cell.val M))) ∧
      (rowValD zz sv ((rowG qr tB z o p).1.eqR.map (Cell.val M))).1.1 = (rowG qr tB z o p).1.target.val M := by
  refine ⟨fun s hs hok => ?_, (rowSwitch_replays hS hz ho hT ⟨P, 0, true⟩ hP zz sv ht p hh).2⟩
  have hs' : rpos s = P := hs
  rw [(rowSwitch_replays hS hz ho hT s (by rw [hs']; exact hP) zz sv ht p hh).1]
  exact ⟨rfl, hok, by show rpos s + 504 + 0 = _; rw [hs']⟩

/-! ## The wiring -/

/-- The wiring's ground answers `(answer lane, g)`: the wiring rounds', then the slot rounds'. -/
def wireChals (w qw : Nat) : List (Nat × Nat) := (sc2Ans w qw ++ sc2Ans 2 (wireLanes w qw).slot).map fun q => (q, gC2)

/-- **The wiring's phase** (`wireD (P + 5)` with its row switch): from `P5` (`8 qw = P5 + 40`) to
`P5 + 112 (P + 5) + 1768`, on a represented claim (`Rep2`, the tape phase's output); the value is read off the
gadgets (`wireG2` at `p`, the row switch `rowG` at `pr`, its row words the slices' transpose). -/
theorem wire_phase {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {P qw : ℕ} {cv : ℕ → C2}
    {mb sb : List Cell} {zk gate : Cell} (claim : E2V.KClaim FE2) (s' : List FK) (n sbsel dsel : ℕ)
    (hzk : zk.val M = 0) (hg : gate.val M = 1) (hsb : sb.length = 256)
    (hmb : (mb.map fun b => kC2 b zk).map (C2.val M) = bitsF (n - 1) (P + 5)) (hn : n - 1 < 2 ^ (P + 5))
    (hsbv : (sb.map fun b => kC2 b zk).map (C2.val M) = (List.range 256).map fun p => E2V.bitF (sBitsD s' p))
    (hR : Rep2 P (fun j => (cv j).val M) claim false) {P5 : Nat} (hP : 8 * qw = P5 + 40)
    {p : Ptr} (hh : SegsHold c M p (wireG2 P qw cv mb sb zk gate p).2)
    (ha : SegsAssert M p (wireG2 P qw cv mb sb zk gate p).2)
    {tB z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1) {pr : Ptr}
    (hhr : SegsHold c M pr (rowG (wireLanes (P + 5) qw).ring tB z o pr).2)
    (ht : ∀ j < 128, M.k (tB + j) = rowWordD ((wireG2 P qw cv mb sb zk gate p).1.slices.map (C2.val M)) j)
    (hT : (wireLanes (P + 5) qw).ring + 9 * 6 + 2 < T)
    (hpow : PowOkV (feAt sig) (wireChals (P + 5) qw)) :
    let wo := (wireG2 P qw cv mb sb zk gate p).1
    let ro := (rowG (wireLanes (P + 5) qw).ring tB z o pr).1
    let row := rowValD (wo.sigma.map (C2.val M) ++ wo.tau.map (C2.val M) ++ selPtF dsel sbsel)
      (wo.slices.map (C2.val M)) (ro.eqR.map (Cell.val M))
    PhaseAt (wireD (P + 5) sbsel dsel s' n claim) sig P5 (P5 + 112 * (P + 5) + 1768)
      ((wo.sigma.map (C2.val M), wo.final.val M), [wo.gD.val M],
        ((wo.tau.map (C2.val M), scFold2 (fun k => fe2At sig (8 * k)) 2 (wireLanes (P + 5) qw).slot (wo.gD.val M)),
          wo.slices.map (C2.val M), row)) ∧
      row.1.1 = ro.target.val M := by
  intro wo ro row
  have hE := (rowG_spec (c := c) hS hz ho hT pr hhr).1
  have hL : (wireLanes (P + 5) qw).slices + 128 < T := by simp only [wireLanes] at hT ⊢; omega
  have hrow : row.1.1 = ro.target.val M := by
    show (rowValD _ _ _).1.1 = _
    rw [(rowG_spec (c := c) hS hz ho hT pr hhr).2, rowValD, sumE_eq, hE]
    exact congrArg List.sum (List.map_congr_left fun j hj => by rw [ht j (List.mem_range.mp hj)])
  refine ⟨fun s hs hok => ?_, hrow⟩
  have hs' : rpos s = P5 := hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := wire_replays hS claim s' n sbsel dsel hzk hg hsb hmb hn hsbv
    hR.value.symm hR.mu.symm hR.point.symm (fun j hj => rep2_lt_posF hR hj) s (by rw [hs']; exact hP) hL p hh ha
  have hok2 : okS gC2 sig (rpos s) (P + 5) = true := okS_true _ _ fun k hk => by
    have := hpow (qw + roundLanes2 * k + 5, gC2) (List.mem_map.mpr ⟨_, List.mem_append_left _
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), rfl⟩)
    rwa [show 8 * (qw + roundLanes2 * k + 5) = rpos s + 80 + 112 * k by simp only [roundLanes2]; omega] at this
  have hok3 : okS gC2 sig (rpos s + 112 * (P + 5) + 16) 2 = true := okS_true _ _ fun k hk => by
    have := hpow ((wireLanes (P + 5) qw).slot + roundLanes2 * k + 5, gC2) (List.mem_map.mpr ⟨_,
      List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), rfl⟩)
    rwa [show 8 * ((wireLanes (P + 5) qw).slot + roundLanes2 * k + 5) = rpos s + 112 * (P + 5) + 16 + 80 + 112 * k by
      simp only [wireLanes, roundLanes2]; omega] at this
  have hq : ((List.range 7).map fun k => feAt sig (rpos s + 112 * (P + 5) + 1304 + 72 * k)) =
      (List.range 7).map fun k => feAt sig (8 * ((wireLanes (P + 5) qw).ring + 9 * k)) :=
    List.map_congr_left fun k _ => congrArg _ (by simp only [wireLanes, roundLanes2]; omega)
  rw [hq, ← hE] at h7
  refine ⟨?_, by rw [h5, hok2, hok3, hok]; rfl, by show rpos _ = _; rw [h8, hs']⟩
  generalize (wireD (P + 5) sbsel dsel s' n claim sig s).1 = X at h1 h2 h3 h4 h6 h7
  obtain ⟨⟨xσ, xf⟩, xg, ⟨xτ, xf'⟩, xsv, xrow⟩ := X
  simp only at h1 h2 h3 h4 h6 h7 ⊢
  rw [h1, h2, h3, h4, h6, h7]

/-! ## The `KS` link -/

/-- `contRowsF` in the link gadget's form. -/
theorem contRowsF_eq : E2V.contRowsF = rowsBK (spongeBlocksF P20F accVF) (ksSplit P20 + 399) := rfl

/-- The link's ground answers `(answer lane, g)`: the `hk + 5` challenges, then the shift sumcheck's rounds. -/
def ksLinkChals (hk qa : Nat) : List (Nat × Nat) :=
  chalsG qa gC1 (hk + 5) ++ (sc2Ans hk (ksLinkQ1 hk qa)).map fun q => (q, gC2)

/-- **The `KS` link's phase**: from `P` (`8 qa = P + 48`) V's `ksLinkD hk xl (rowsBK B K)` ends at
`P + 80 (hk + 5) + 112 hk + 64` with the gadget's challenges, shift point, final claim and values. -/
theorem ksLink_phase {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {hk xl B K qa : Nat} {gate : Cell}
    (hg : gate.val M = 1) (hB : B - 1 < 2 ^ hk) (hK : K + 31 < 2 ^ hk) {P : Nat} (hP : 8 * qa = P + 48)
    (hT : ksLinkQV hk qa + 8 < T) {p : Ptr} (hh : SegsHold c M p (ksLinkG2 hk xl B K qa gate p).2)
    (ha : SegsAssert M p (ksLinkG2 hk xl B K qa gate p).2)
    (hpow : PowOkV (feAt sig) (ksLinkChals hk qa)) :
    let o := (ksLinkG2 hk xl B K qa gate p).1
    PhaseAt (ksLinkD hk xl (rowsBK B K)) sig P (P + 80 * (hk + 5) + 112 * hk + 64)
      (o.kchal.map (C2.val M), (o.shift.map (C2.val M), o.final.val M), o.vals.map (C2.val M)) := by
  intro o s hs hok
  have hs' : rpos s = P := hs
  obtain ⟨h1, h2, h3⟩ := ksLink_replays hS hg hB hK s (by rw [hs']; exact hP) hT p hh ha
  have hg1 : okG gC1 sig (rpos s) (hk + 5) = true := okG_true _ _ fun i hi => by
    have := hpow (qa + 10 * i, gC1) (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    rwa [show 8 * (qa + 10 * i) = rpos s + 48 + 80 * i by omega] at this
  have hg2 : okS gC2 sig (rpos s + 80 * (hk + 5)) hk = true := okS_true _ _ fun k hk' => by
    have := hpow (ksLinkQ1 hk qa + roundLanes2 * k + 5, gC2) (List.mem_append_right _
      (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩, rfl⟩))
    rwa [show 8 * (ksLinkQ1 hk qa + roundLanes2 * k + 5) = rpos s + 80 * (hk + 5) + 80 + 112 * k by
      simp only [ksLinkQ1, roundLanes2]; omega] at this
  exact ⟨h1, by rw [h2, hg1, hg2, hok]; rfl, by show rpos _ = _; rw [h3, hs']⟩

/-! ## `tapeD` and `callerD` from the GKR phases -/

theorem sepE2_phase {sig : ByteArray} {P : Nat} : PhaseAt sepE2 sig P (P + 72) () :=
  fun s hs hok => ⟨rfl, hok, by show s.ent + 72 + s.msg + 0 = _; rw [← hs]; simp only [pos]; omega⟩

theorem samplesG_phase {sig : ByteArray} {g n P q : Nat} (hq : 8 * q = P + 48)
    (hpow : PowOkV (feAt sig) (chalsG q g n)) : PhaseAt (samplesG g n) sig P (P + 80 * n) (sampsG sig P n) := by
  intro s hs hok
  have hs' : rpos s = P := hs
  obtain ⟨h1, h2, h3⟩ := Lvm.Q2.samplesG_run g sig n s
  have hg : okG g sig (rpos s) n = true := okG_true _ _ fun i hi => by
    have := hpow (q + 10 * i, g) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    rwa [show 8 * (q + 10 * i) = rpos s + 48 + 80 * i by omega] at this
  exact ⟨by rw [h1, hs']; rfl, by rw [h3, hg, hok]; rfl, by show rpos _ = _; rw [h2, hs']⟩

theorem readE2s_phase {sig : ByteArray} {n P : Nat} : PhaseAt (readE2s n) sig P (P + 16 * n) (readsE2 sig P n) := by
  intro s hs hok
  have hs' : rpos s = P := hs
  rw [Lvm.Q2.readE2s_run, hs']
  exact ⟨rfl, hok, by show s.ent + (s.msg + 16 * n) = _; rw [← hs']; simp only [rpos]; omega⟩

/-- **`tapeD` from its parts**: the separator, `r` (`w` ground challenges, answer lanes `qr + 10 i`,
`8 qr = P4 + 120`), the 25 scalars, then the tape GKR's phase (E2F-QH4's `tape_phase2`), `n`'s range and the
wiring's phase (`wire_phase`). -/
theorem tapeD_phase {w sb dsel : Nat} {s : List FK} {n : Nat} {sig : ByteArray} {P4 P5 P6 qr : Nat}
    {claim : KClaim FE2}
    {wo : (List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))}
    (hqr : 8 * qr = P4 + 120) (hpow : PowOkV (feAt sig) (chalsG qr gC1 w))
    (htg : PhaseAt (tapeGkrD w (sampsG sig (P4 + 72) w) (readsE2 sig (P4 + 72 + 80 * w) 25)) sig
      (P4 + 72 + 80 * w + 400) P5 claim)
    (hn : 1 ≤ n ∧ n ≤ 2 ^ w) (hw : PhaseAt (wireD w sb dsel s n claim) sig P5 P6 wo) :
    PhaseAt (tapeD w sb dsel s n) sig P4 P6
      (sampsG sig (P4 + 72) w, readsE2 sig (P4 + 72 + 80 * w) 25, claim, wo) :=
  phaseAt_bind sepE2_phase (phaseAt_bind (samplesG_phase (by omega) hpow) (phaseAt_bind readE2s_phase
    (phaseAt_bind htg (phaseAt_bind (phaseAt_require (decide_eq_true hn)) (phaseAt_bind hw phaseAt_pure)))))

/-- **`callerD` from its parts**: `h` ground challenges (answer lanes `qr + 10 i`, `8 qr = P3 + 48`), the 25
scalars, `verify_keccak`'s phase (E2F-QH4's), then the row switch's (`rowSwitch_phase`). -/
theorem callerD_phase {h : Nat} {sig : ByteArray} {P3 P3' P4 qr : Nat}
    {res : List (List FE2 × FE2) × List FE2 × List FE2} {row : (FE × (List FE → FE)) × List FE}
    (hqr : 8 * qr = P3 + 48) (hpow : PowOkV (feAt sig) (chalsG qr gC1 h))
    (hk : PhaseAt (verifyKeccakD h (sampsG sig P3 h) (readsE2 sig (P3 + 80 * h) 25)) sig (P3 + 80 * h + 400) P3' res)
    (hr : PhaseAt (rowSwitchD res.2.1 res.2.2) sig P3' P4 row) :
    PhaseAt (callerD h) sig P3 P4 (sampsG sig P3 h, readsE2 sig (P3 + 80 * h) 25, res, row) :=
  phaseAt_bind (samplesG_phase hqr hpow) (phaseAt_bind readE2s_phase
    (phaseAt_bind hk (phaseAt_bind hr phaseAt_pure)))

end Lvm.Q2
