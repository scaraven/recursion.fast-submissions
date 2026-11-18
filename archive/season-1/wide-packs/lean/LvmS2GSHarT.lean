-- New for lvm2 σ_LEAF (SLF-C2, 2026-11-16): the typed phases of the S2GS node program (`typedGS`, item 7e's typed
-- half): the child's `PUB` without `σ_leaf` (110 lanes, `pubOfWS`), `virtGT` on it, the wiring and A23 at a header of
-- 18 lanes before `acc_in` (`qaccGS 18`), and `typedGS` replaying V_S's `dTypedLG` on `pubOfWS` (twins of S2GT's
-- `LvmE2QTypedKitT`/`LvmE2QTypedPhaseT` and S2GL's `typed_phaseTL`, `typedGL_shape`).
import LvmE2QAsmS
import LvmS2GLHar
import LvmS2GSHdr

/-!
# The typed phases at S2GS

* **`pubOfWS_hdrLanesT`**: S2GS's child `PUB` lanes (`pubOfWS`'s `hdrLanesT`, 110 lanes) are the stream's lanes from
  `11`, except the key lanes `1 … 4` (`pubG_hdrLanesT` without the 597 `σ_leaf` lanes).
* **`hs_virtGS`**: `virtGT`'s value is V_S's `virtD` on `pubOfWS` (`hs_virtGT`'s twin).
* **`wireGT_runS`**, **`qaccGS_run`**: the wiring and A23 (`acc_in` at stream lanes `29 + 2j`, the current proof's at
  `pb + 18 + 2j`, `accCS`) replay `dWiringT` and `dAccT` on `pubOfWS` (`wireGT_run`, `qaccGT_run`'s twins).
* **`typed_phaseTS`**: `typedGS` replays `dTypedLG` on `pubOfWS` in the `PhaseAt` form (`typed_phaseTL`'s twin).
* **`typedGS_shape`**: `typedGS`'s outputs (`typedGL_shape`'s twin).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q2 Lvm.QTyped Lvm.QShape
open Finset (range)

/-! ## S2GS's child `PUB` lanes -/

open Lvm.QAcc in
/-- The first 18 lanes and the rest (proof help: `range_splitT` without the 597 `σ_leaf` lanes). -/
theorem range_splitS (F : Nat → FK) (n : Nat) :
    (List.range (18 + n)).map F = [F 0] ++ ((List.range 4).map fun i => F (1 + i)) ++
      ((List.range 4).map fun i => F (5 + i)) ++ ((List.range 4).map fun i => F (9 + i)) ++ [F 13] ++
      ((List.range 4).map fun i => F (14 + i)) ++ ((List.range n).map fun i => F (18 + i)) := by
  rw [show 18 + n = 1 + 4 + 4 + 4 + 1 + 4 + n by omega]
  simp only [map_range_add, List.append_assoc]
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero, List.cons_append, List.nil_append,
    Nat.reduceAdd]

open Lvm.QAcc in
/-- **S2GS's child `PUB` lanes** (`pubOfWS`'s `hdrLanesT`, 110 lanes): the stream's lanes from `11`, except the key
lanes `1 … 4` (`pubG_hdrLanesT` without `σ_leaf`; `acc_in` from header byte `hdrFixS`, stream lane `29`). -/
theorem pubOfWS_hdrLanesT (vk c : Vector UInt8 32) (sig : ByteArray) :
    (Lvm.pubOfWS vk c sig).hdrLanesT = (List.range (18 + 2 * (Lvm.VEq.accVT + 1))).map (hdrLaneS vk sig) := by
  have pos (i : Nat) (h : ¬ (1 ≤ i ∧ i < 5)) : hdrLaneS vk sig i = kAt sig (8 * (11 + i)) := by
    simp only [hdrLaneS, h, ite_false]
  have e0 : (⟨(Lvm.pubOfWS vk c sig).b.toUInt64⟩ : FK) = hdrLaneS vk sig 0 := by
    rw [pos 0 (by omega)]
    simp only [Lvm.pubOfWS, pubOfW, pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e1 : (Lvm.pubOfWS vk c sig).vk = (List.range 4).map fun i => hdrLaneS vk sig (1 + i) := by
    show digestLanes vk = _
    conv_lhs => rw [list_eq_range_getD (digestLanes vk)]
    rw [show (digestLanes vk).length = 4 by simp [digestLanes]]
    apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi
    simp [hdrLaneS, show 1 ≤ 1 + i ∧ 1 + i < 5 by omega]
  have seg (o k n : Nat) (ho : 5 ≤ k) (hk : headerAt o = 8 * (11 + k)) :
      ((List.range n).map fun i => kAt sig (headerAt o + 8 * i)) =
        (List.range n).map fun i => hdrLaneS vk sig (k + i) := by
    apply List.map_congr_left; intro i _
    rw [pos _ (by omega), hk, show 8 * (11 + k) + 8 * i = 8 * (11 + (k + i)) by ring]
  have e4 : (⟨(Lvm.pubOfWS vk c sig).n.toUInt64⟩ : FK) = hdrLaneS vk sig 13 := by
    rw [pos 13 (by omega)]
    simp only [Lvm.pubOfWS, pubOfW, pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e7 : ((Lvm.pubOfWS vk c sig).accIn.pt ++ [(Lvm.pubOfWS vk c sig).accIn.y]).flatMap FE.lanes2 =
      (List.range (2 * (Lvm.VEq.accVT + 1))).map fun i => hdrLaneS vk sig (18 + i) := by
    have : (Lvm.pubOfWS vk c sig).accIn.pt ++ [(Lvm.pubOfWS vk c sig).accIn.y] =
        (List.range (Lvm.VEq.accVT + 1)).map fun j => fe16At sig (8 * 29 + 8 * 2 * j) := by
      simp only [Lvm.pubOfWS]
      rw [List.range_succ, List.map_append, List.map_singleton]
      refine congrArg₂ (· ++ ·) (List.map_congr_left fun j _ => congrArg (fe16At sig) ?_)
        (congrArg (fun o => [fe16At sig o]) ?_) <;> simp only [headerAt, hdrFixS] <;> omega
    rw [this, flatMap_lanes2 sig (8 * 29) (Lvm.VEq.accVT + 1)]
    apply List.map_congr_left; intro i _
    rw [pos _ (by omega), show 8 * 29 + 8 * i = 8 * (11 + (18 + i)) by ring]
  have e2 : (Lvm.pubOfWS vk c sig).cL = (List.range 4).map fun i => hdrLaneS vk sig (5 + i) :=
    seg 48 5 4 (by omega) rfl
  have e3 : (Lvm.pubOfWS vk c sig).s = (List.range 4).map fun i => hdrLaneS vk sig (9 + i) :=
    seg 80 9 4 (by omega) rfl
  have e5 : (Lvm.pubOfWS vk c sig).h = (List.range 4).map fun i => hdrLaneS vk sig (14 + i) :=
    seg 120 14 4 (by omega) rfl
  have e6 : (Lvm.pubOfWS vk c sig).sigLeaf = [] := rfl
  rw [range_splitS]
  simp only [Pub.hdrLanesT, Pub.hdrLanesW, List.append_assoc]
  rw [e0, e1, e2, e3, e4, e5, e6, e7, List.nil_append]

/-! ## `virtGT = virtD` on `pubOfWS` -/

section
variable {c : Ctx} {M : Mem}

/-- **`virtGT`'s value is V_S's `virtD`** at `r_y` on the child's `PUB` at S2GS (`pubOfWS`: the stream's header lanes,
the current proof's `vk` cells at `pb + 1`), on regions that are V_S's (`hs_virtGT`'s twin, 110 lanes). -/
theorem hs_virtGS (vk cL : Vector UInt8 32) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T)
    {z2 o2 : C2} (hz : z2.val M = 0) (ho : o2.val M = 1) (hz2K : KC2 z2) (ho2K : KC2 o2) {Td : TData}
    {N : Lvm.E2T.TNatT} (htd : TdOk Td N.toN) {pb n : Nat} (hn : n = 18 + 2 * (Lvm.VEq.accVT + 1))
    (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) (hH : 11 + n ≤ T) (ry : List C2)
    (hry : 10 ≤ ry.length) :
    Hs c M (virtGT z2 o2 Td pb n ry) (fun w => w.val M =
      Lvm.E2T.virtD N (Lvm.pubOfWS vk cL sig) (ry.map (C2.val M))) := by
  unfold virtGT regSel2
  simp only [htd.qlt]
  have hlen : (ry.take 10).length = 10 := List.length_take_of_le hry
  have hn' : n = 110 := by rw [hn]; rfl
  refine hs_bind (hs_eqConst2 hz ho ho2K _ _) fun sP ⟨_, hsP⟩ =>
    hs_bind (hs_eqDot2K hz ho hz2K ho2K (ry.take 10) 5 (by rw [hlen]; omega) _
      (fun x hx => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact pubLaneC_K _ _ _)
      (by rw [List.length_map, List.length_range, hlen, hn']; omega)) fun vP hvP =>
    hs_bind (hs_g2Mul sP vP z2) fun w hw => hs_bind (hs_eqConst2 hz ho ho2K ry Td.one) fun e1 ⟨_, he1⟩ =>
    hs_mono (hs_g2Add w e1) fun w' hw' => ?_
  rw [hw', hw, hz, add_zero, hsP, hvP, he1, virtD_td htd _ _ (by simpa using hry), pubOfWS_hdrLanesT]
  simp only [Lvm.E2T.hiWG, List.map_drop, Nat.shiftRight_zero, List.drop_zero, List.map_take]
  refine congrArg₂ (· + ·) (congrArg₂ (· * ·) rfl ?_) rfl
  rw [List.length_map, List.length_range]
  rw [← hn]
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ 10 = n + m := ⟨2 ^ 10 - n, by rw [hn']; norm_num⟩
  rw [hm, Finset.sum_range_add, Finset.sum_eq_zero (s := range m) fun j _ => by
    rw [Lvm.list_toArray_getD, List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega),
      show FE2.ofK 0 = 0 from rfl, zero_mul], add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [mul_comm, Lvm.list_toArray_getD, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  refine congrArg₂ (· * ·) (congrArg FE2.ofK ?_) rfl
  unfold Lvm.QAcc.pubLaneC Lvm.QAcc.hdrLaneS
  split_ifs with h
  · rw [Cell.val_K, show pb + 1 + (i - 1) = pb + 1 + (i - 1) from rfl, hvk _ (by omega)]; rfl
  · rw [Cell.val_K, hS _ (by omega)]; rfl

end

end Lvm.E2Q

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q1 Lvm.Q2 DM Lvm.E2V Lvm.QTyped

/-! ## The wiring and A23 at S2GS -/

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **The wiring at `E2` replayed at S2GS** (`wireGT_run`'s twin on `pubOfWS`, `pubLanesS P20S = 110` lanes): from the
cursor `P` after the zerocheck, `dWiringT` on the nine values keeps `ok`, ends at `P + 2688`; `r_y`, the twelve and
the four values are the gadget's cells'. -/
theorem wireGT_runS (vk cL : Vector UInt8 32) (hS : Streamed M sig T) {z2 o2 : C2} (hz2 : z2.val M = 0)
    (ho2 : o2.val M = 1) (hz2K : KC2 z2) (ho2K : KC2 o2) {g : Cell} (hg : g.val M = 1) {Td : TData}
    {N : Lvm.E2T.TNatT} (htd : TdOk Td N.toN) {pb : Nat} (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0)
    {L : Nat → Nat} {P qw : Nat} (hγ : 8 * L iGam = P + 48) (hqw : 8 * qw = P + 120)
    (hR : ∀ k < tY, L (iWR 0 + 3 * k) = qw + 14 * k ∧ L (iWR 0 + 3 * k + 2) = qw + 14 * k + 5)
    (hV : 8 * L iWV = P + 2472) (hV4 : 8 * L (iWV + 1) = P + 2664) (hT : P + 2736 ≤ 8 * T)
    (hH : 11 + pubLanesS P20S ≤ T)
    (hpγ : powOKR Lvm.E2T.gGamma (feAt sig (P + 48)) = true) (hpR : okS Lvm.E2T.gWire sig (P + 80) tY = true)
    (v : List C2) (hv : v.length = 9) :
    HsA c M (wireGT z2 o2 g Td pb (pubLanesS P20S) L v) (fun out => ∀ s : RS, rpos s = P → s.ok = true →
      (Lvm.E2T.dWiringT N (Lvm.pubOfWS vk cL sig) (v.map (C2.val M)) sig s).1 =
          (out.1.map (C2.val M), out.2.1.map (C2.val M), out.2.2.map (C2.val M)) ∧
        (Lvm.E2T.dWiringT N (Lvm.pubOfWS vk cL sig) (v.map (C2.val M)) sig s).2.ok = true ∧
        rpos (Lvm.E2T.dWiringT N (Lvm.pubOfWS vk cL sig) (v.map (C2.val M)) sig s).2 = P + 2688 ∧
        out.1.length = tY ∧ (∀ x ∈ out.1, KC2 x) ∧ out.2.1 = ld2s (L iWV) 12 ∧ out.2.2 = ld2s (L (iWV + 1)) 4) := by
  have hv9 : v.take 9 = v := List.take_of_length_le (by clear * - hv; omega)
  have hγv : (ld2 (L iGam)).val M = fe2At sig (P + 48) := by
    rw [ld2_val hS (q := L iGam) (by clear * - hγ hT; omega), hγ]
  unfold wireGT
  dsimp only
  rw [hv9]
  refine hsA_bind (hsA_of_hs (hs_powSum2 hz2 _ _)) fun c0 hc0 => ?_
  refine hsA_bind (hsA_of_hs (Lvm.QShape.hs_and (hs_plainRuns2 hS L tY (iWR 0) qw c0 hR
    (by show qw + 14 * 21 < T; clear * - hqw hT; omega))
    (hs_plainRuns2_fst L tY (iWR 0) c0))) fun rf ⟨⟨e1, e2⟩, e3⟩ => ?_
  refine hsA_bind (hsA_of_hs (hs_mapB _ (fun j => ((ld2s (L iWV) 12).getD (2 + 4 * j) z2).val M +
    ((ld2s (L iWV) 12).getD (3 + 4 * j) z2).val M) (fun j => hs_g2Add _ _) _)) fun d6 hd6 => ?_
  refine hsA_bind (hsA_of_hs (hs_powSum2 hz2 _ _)) fun m hm => ?_
  have hrl : rf.1.length = tY := by rw [e3]; simp
  refine hsA_bind (hsA_of_hs (hs_virtGS (c := c) vk cL hS hz2 ho2 hz2K ho2K htd (pb := pb) (n := pubLanesS P20S)
    rfl hvk hH rf.1 (by rw [hrl]; decide))) fun ve hve => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Sum ve _)) fun sm hsm => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul m sm z2)) fun pr hpr => ?_
  refine hsA_bind (hsA_assertEq2 _ _ hg) fun _ hA => hsA_pure ?_
  intro s hs hok
  -- the stream's values
  have hvs : (ld2s (L iWV) 12).map (C2.val M) = (List.range 12).map fun i => fe2At sig (P + 2432 + 40 + 16 * i) := by
    rw [ld2s_vals hS (by clear * - hV hT; omega), hV]
  have hrv : (ld2s (L (iWV + 1)) 4).map (C2.val M) =
      (List.range 4).map fun i => fe2At sig (P + 2624 + 40 + 16 * i) := by
    rw [ld2s_vals hS (by clear * - hV4 hT; omega), hV4]
  have hgd : ∀ j < 12, ((ld2s (L iWV) 12).getD j z2).val M = fe2At sig (P + 2432 + 40 + 16 * j) := fun j hj => by
    rw [← getD_val2 hz2, hvs, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  -- the circuit's final claim
  have hm' : m.val M =
      Lvm.E2T.wGD (fe2At sig (P + 48)) ((List.range 12).map fun i => fe2At sig (P + 2432 + 40 + 16 * i)) := by
    have hds : (((List.range 3).map fun j => (ld2s (L iWV) 12).getD (4 * j) z2) ++
        (List.range 3).map (fun j => (ld2s (L iWV) 12).getD (1 + 4 * j) z2) ++ d6).map (C2.val M) =
        [fe2At sig (P + 2472), fe2At sig (P + 2536), fe2At sig (P + 2600), fe2At sig (P + 2488), fe2At sig (P + 2552),
          fe2At sig (P + 2616), fe2At sig (P + 2504) + fe2At sig (P + 2520),
          fe2At sig (P + 2568) + fe2At sig (P + 2584), fe2At sig (P + 2632) + fe2At sig (P + 2648)] := by
      rw [List.map_append, List.map_append, hd6]
      simp only [show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append]
      rw [hgd 0 (by decide), hgd 4 (by decide), hgd 8 (by decide), hgd 1 (by decide), hgd 5 (by decide),
        hgd 9 (by decide), hgd 2 (by decide), hgd 3 (by decide), hgd 6 (by decide), hgd 7 (by decide),
        hgd 10 (by decide), hgd 11 (by decide)]
    have hdl : (((List.range 3).map fun j => (ld2s (L iWV) 12).getD (4 * j) z2) ++
        (List.range 3).map (fun j => (ld2s (L iWV) 12).getD (1 + 4 * j) z2) ++ d6).length = 9 := by
      rw [← List.length_map (f := C2.val M), hds]; rfl
    rw [hm, hdl, hds, hγv]
    simp only [Nat.reduceMul, Nat.reduceAdd, Lvm.E2T.wGD, show List.range 3 = [0, 1, 2] from rfl,
      show List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl,
      show List.range 12 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from rfl, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.getD_cons_succ, List.getD_cons_zero]
    ring
  -- V's run
  have hp1 : s.ent + 40 + (s.msg + 8) = P + 48 := by simp only [rpos] at hs; clear * - hs; omega
  unfold Lvm.E2T.dWiringT
  rw [dbind_run, Lvm.Q2.sampleG_run, hp1, dbind_run, Lvm.Q2.e2OfFE_feAt]
  have hp2 : rpos (⟨s.ent + 72 + (s.msg + 8), 0, powOKR Lvm.E2T.gGamma (feAt sig (P + 48)) && s.ok⟩ : RS) =
      P + 80 := by
    simp only [rpos] at hs ⊢; clear * - hs; omega
  obtain ⟨X, hX⟩ : ∃ X, sumcheckD Lvm.E2T.gWire (Lvm.E2T.wBatchD (fe2At sig (P + 48)) (v.map (C2.val M))) 3
      (List.replicate Lvm.Typed.yVars none) sig
      ⟨s.ent + 72 + (s.msg + 8), 0, powOKR Lvm.E2T.gGamma (feAt sig (P + 48)) && s.ok⟩ = X := ⟨_, rfl⟩
  obtain ⟨b1, b2, b3⟩ := Lvm.Q2.sumcheckD_run Lvm.E2T.gWire sig Lvm.Typed.yVars
    (Lvm.E2T.wBatchD (fe2At sig (P + 48)) (v.map (C2.val M)))
    ⟨s.ent + 72 + (s.msg + 8), 0, powOKR Lvm.E2T.gGamma (feAt sig (P + 48)) && s.ok⟩ qw
    (by rw [hp2]; clear * - hqw; omega)
  rw [hX, hp2] at b1 b2 b3
  rw [hX, dbind_run, Lvm.Q2.readE2s_run, dbind_run, Lvm.Q2.readE2s_run, dbind_run, requireT_run, dpure_run]
  have hpX : rpos X.2 = P + 2432 := by rw [b2]; show P + 80 + 112 * 21 = P + 2432; rfl
  have hpX' : rpos { X.2 with msg := X.2.msg + 16 * 12 } = P + 2624 := by
    simp only [rpos] at hpX ⊢; clear * - hpX; omega
  rw [hpX, hpX']
  -- the challenges and the final claim
  have hry : X.1.1 = rf.1.map (C2.val M) := by
    rw [b1, e1]
    exact List.map_congr_left fun k _ => congrArg _ (by clear * - hqw; omega)
  have hc0' : c0.val M = Lvm.E2T.wBatchD (fe2At sig (P + 48)) (v.map (C2.val M)) := by
    rw [hc0, hγv, Lvm.E2T.wBatchD, hv]
  have hfin : X.1.2 =
      Lvm.E2T.wGD (fe2At sig (P + 48)) ((List.range 12).map fun i => fe2At sig (P + 2432 + 40 + 16 * i)) *
      (E2V.sumF ((List.range 4).map fun i => fe2At sig (P + 2624 + 40 + 16 * i)) +
        Lvm.E2T.virtD N (Lvm.pubOfWS vk cL sig) (rf.1.map (C2.val M))) := by
    rw [b1]
    dsimp only
    rw [← hc0', ← e2, hA, hpr, hz2, add_zero, hsm, hve, hm', E2V.sumF_eq_sum, ← hrv]
    ring
  refine ⟨?_, ?_, ?_, hrl, by rw [e3]; exact kc2_range _ _ _, rfl, rfl⟩
  · rw [hry, hvs, hrv]
  · show ((X.1.2 == _) && _) = true
    rw [hry, hfin, beq_self_eq_true, Bool.true_and, b3, show Lvm.Typed.yVars = tY from rfl, hpR, hpγ, hok]; rfl
  · simp only [rpos] at hpX ⊢; clear * - hpX; omega

/-- The current proof's accumulator at S2GS: `PUB` lanes `18 + 2j` (`E2`, two lanes a scalar) as `E3` scalars with
`c₂ = 0` (`accCT` at a header of 18 lanes before `acc_in`). -/
def accCS (M : Mem) (pb : Nat) : Acc :=
  ⟨(List.range Lvm.VEq.accVT).map fun j => Lvm.E2T.fe2ToFE ((ld2 (pb + 18 + 2 * j)).val M),
    Lvm.E2T.fe2ToFE ((ld2 (pb + 18 + 2 * Lvm.VEq.accVT)).val M)⟩

/-- **A23 at `E2` replayed at S2GS** (`qaccGT_run`'s twin for `qaccGS 18`: `acc_in` at stream lanes `29 + 2j`, the
current proof's `PUB` at `pb + 18 + 2j`): from the cursor `P` after the relayout, `dAccT` on `pubOfWS` keeps `ok`,
ends at `P + 1152`, and folds to the current proof's `PUB` accumulator (`accCS`). -/
theorem qaccGS_run (vk cL : Vector UInt8 32) (hS : Streamed M sig T) {z2 o2 : C2} (hz2 : z2.val M = 0)
    (ho2 : o2.val M = 1) (hz2K : KC2 z2) (ho2K : KC2 o2) {pb : Nat} (hg : M.k pb = 1) {L : Nat → Nat} {P : Nat}
    (hκ : ∀ j < 4, 8 * L (iKap j) = P + 48 + 80 * j) (hh : 8 * L iH = P + 360) (ht : 8 * L iT = P + 1104)
    (hz : 8 * L iZ = P + 1176) (hT : P + 1192 ≤ 8 * T) (hH : 11 + pubLanesS P20S ≤ T)
    (hpκ : okG Lvm.E2T.gKappa sig P 4 = true) (hpt : powOKR Lvm.E2T.gT (feAt sig (P + 1104)) = true)
    (rx ry vs : List C2) (hrx : rx.length = tX) (hry : ry.length = tY) (hvs : vs.length = 12) :
    HsA c M (qaccGS 18 z2 o2 pb L rx ry vs) (fun _ => ∀ s : RS, rpos s = P → s.ok = true →
      (Lvm.E2T.dAccT (Lvm.pubOfWS vk cL sig) ((rx ++ ry).map (C2.val M)) (vs.map (C2.val M)) sig s).1 =
          accCS M pb ∧
        (Lvm.E2T.dAccT (Lvm.pubOfWS vk cL sig) ((rx ++ ry).map (C2.val M)) (vs.map (C2.val M)) sig s).2.ok = true ∧
        rpos (Lvm.E2T.dAccT (Lvm.pubOfWS vk cL sig) ((rx ++ ry).map (C2.val M)) (vs.map (C2.val M)) sig s).2 =
          P + 1152) := by
  have hgv : (kc pb).val M = 1 := Lvm.QAcc.kc_val_one hg
  unfold qaccGS
  dsimp only
  refine hsA_bind (hsA_assertEq2 _ _ hgv) fun _ hA0 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Sum z2 _)) fun sh hsh => ?_
  refine hsA_bind (hsA_of_hs (hs_eqDot2 hz2 ho2 ((List.range 4).map fun j => ld2 (L (iKap j))) 2 (by simp) vs
    (by simp [hvs]))) fun y hy => ?_
  refine hsA_bind (hsA_assertEq2 _ _ hgv) fun _ hA1 => ?_
  refine hsA_bind (hsA_assertEq2 _ _ hgv) fun _ hAz => ?_
  refine hsA_bind (hsA_of_hs (hs_mapB _ (fun i => (ld2 (L iT)).val M *
      ((((List.range (tVarsT + 1)).map fun j => ld2 (11 + 18 + 2 * j)).getD i z2).val M +
        ((((List.range 4).map fun j => ld2 (L (iKap j))) ++ rx ++ ry).getD i z2).val M) +
      (((List.range (tVarsT + 1)).map fun j => ld2 (11 + 18 + 2 * j)).getD i z2).val M)
    (fun i => hs_bind (hs_g2Add _ _) fun d hd => hs_mono (hs_g2Mul _ _ _) fun r hr => by rw [hr, hd]) _))
    fun pts hpts => ?_
  refine hsA_bind (hsA_of_hs (hs_powSum2 hz2 (ld2 (L iT)) (ld2s (L iH) (tVarsT + 1)) :
    Hs c M (horner2 (ld2 (L iT)) (ld2s (L iH) (tVarsT + 1)).reverse z2) _)) fun hv hhvv => ?_
  refine hsA_bind (hsA_mapB_all _ (fun i => (pts.getD i z2).val M =
      (((List.range (tVarsT + 1)).map fun j => ld2 (pb + 18 + 2 * j)).getD i z2).val M)
    (fun i => hsA_assertEq2 _ _ hgv) _) fun _ hAp => ?_
  refine hsA_mono (hsA_assertEq2 _ _ hgv) fun _ hAh => ?_
  intro s hs hok
  -- the circuit's values
  have hκv : ∀ j < 4, (ld2 (L (iKap j))).val M = fe2At sig (P + 48 + 80 * j) := fun j hj => by
    rw [ld2_val hS (q := L (iKap j)) (by have := hκ j hj; clear * - this hj hT; omega), hκ j hj]
  have hkap : ((List.range 4).map fun j => ld2 (L (iKap j))).map (C2.val M) =
      (List.range 4).map fun j => fe2At sig (P + 48 + 80 * j) := by
    rw [List.map_map]; exact List.map_congr_left fun j hj => hκv j (List.mem_range.mp hj)
  have hhl : (ld2s (L iH) (tVarsT + 1)).map (C2.val M) =
      (List.range (tVarsT + 1)).map fun i => fe2At sig (P + 360 + 16 * i) := by
    rw [ld2s_vals hS (by show L iH + 2 * 46 < T; clear * - hh hT; omega), hh]
  have htv : (ld2 (L iT)).val M = fe2At sig (P + 1104) := by
    rw [ld2_val hS (q := L iT) (by clear * - ht hT; omega), ht]
  have hzv : fe2At sig (P + 1176) = 0 := by rw [← hz, ← ld2_val hS (q := L iZ) (by clear * - hz hT; omega), hAz, hz2]
  have hain : ∀ j < 46, ((List.range (tVarsT + 1)).map fun j => ld2 (11 + 18 + 2 * j)).getD j z2 = ld2 (29 + 2 * j) :=
    fun j hj => by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj), List.getElem_map,
        List.getElem_range]
  have hainv : ∀ j < 46, (ld2 (29 + 2 * j)).val M = fe2At sig (8 * (29 + 2 * j)) := fun j hj =>
    ld2_val hS (by show 29 + 2 * j + 1 < T; have : 11 + 110 ≤ T := hH; clear * - this hj; omega)
  have hpc : ∀ j < 46,
      ((List.range (tVarsT + 1)).map fun j => ld2 (pb + 18 + 2 * j)).getD j z2 = ld2 (pb + 18 + 2 * j) :=
    fun j hj => by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj), List.getElem_map,
        List.getElem_range]
  -- the line and `h(t)`
  have hbc : (((List.range 4).map fun j => ld2 (L (iKap j))) ++ rx ++ ry).length = 45 := by
    simp only [List.length_append, List.length_map, List.length_range, hrx, hry]; rfl
  have hline : (Lvm.E2T.lineD ((Lvm.pubOfWS vk cL sig).accIn.pt.map Lvm.e2OfFE)
      ((List.range 4).map (fun j => fe2At sig (P + 48 + 80 * j)) ++ (rx ++ ry).map (C2.val M))
        (fe2At sig (P + 1104))) =
      (List.range 45).map fun j => (ld2 (pb + 18 + 2 * j)).val M := by
    have hA : (Lvm.pubOfWS vk cL sig).accIn.pt.map Lvm.e2OfFE =
        (List.range 45).map fun j => fe2At sig (8 * (29 + 2 * j)) := by
      simp only [Lvm.pubOfWS, List.map_map]
      exact List.map_congr_left fun j _ => congrArg (fe2At sig) (by simp only [headerAt, hdrFixS]; omega)
    have hB : (List.range 4).map (fun j => fe2At sig (P + 48 + 80 * j)) ++ (rx ++ ry).map (C2.val M) =
        (List.range 45).map fun j =>
          ((((List.range 4).map fun j => ld2 (L (iKap j))) ++ rx ++ ry).getD j z2).val M := by
      rw [← hbc, ← map_val_range2 hz2]
      simp only [List.map_append, hkap, List.append_assoc]
    rw [hA, hB, lineD_range]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < 45 := List.mem_range.mp hj
    have e1 := hAp j (List.mem_range.mpr hj')
    rw [← getD_val2 hz2, hpts, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj'),
      List.getElem_map, List.getElem_range,
      hain j (by clear * - hj'; omega), hainv j (by clear * - hj'; omega), htv,
      hpc j (by clear * - hj'; omega)] at e1
    rw [← e1]
    ring
  have hht : Lvm.E2T.hEvalD ((List.range (tVarsT + 1)).map fun i => fe2At sig (P + 360 + 16 * i))
      (fe2At sig (P + 1104)) = (ld2 (pb + 18 + 2 * tVarsT)).val M := by
    rw [← hhl, hEvalD_eq, List.length_map, ← htv, ← hhvv, hAh, hpc tVarsT (by decide)]
  -- V's run
  unfold Lvm.E2T.dAccT
  obtain ⟨a1, a2, a3⟩ := Lvm.Q2.samplesG_run Lvm.E2T.gKappa sig Lvm.Typed.selBitsT s
  obtain ⟨K, hK⟩ : ∃ K, samplesG Lvm.E2T.gKappa Lvm.Typed.selBitsT sig s = K := ⟨_, rfl⟩
  rw [hK] at a1 a2 a3
  rw [dbind_run, hK, dbind_run, Lvm.Q2.readE2s_run, dbind_run, Lvm.Q2.sampleG_run, dbind_run, Lvm.Q2.readE2_run,
    dbind_run, requireT_run, dbind_run, requireT_run, dbind_run, requireT_run, dpure_run]
  have hK1 : K.1 = (List.range 4).map fun j => fe2At sig (P + 48 + 80 * j) := by rw [a1, hs]
  have hpK : rpos K.2 = P + 320 := by rw [a2, hs]; rfl
  dsimp only
  have hpK' : K.2.ent + K.2.msg = P + 320 := hpK
  have hφ : Lvm.Typed.phiVarsT = 45 := rfl
  have q1 : K.2.ent + 40 + (K.2.msg + 16 * (Lvm.Typed.phiVarsT + 1) + 8) = P + 1104 := by
    rw [hφ]; (clear * - hpK'; omega)
  have q2 : K.2.ent + 72 + (K.2.msg + 16 * (Lvm.Typed.phiVarsT + 1) + 8) + 40 + 0 = P + 1176 := by
    rw [Nat.add_zero, hφ]; (clear * - hpK'; omega)
  have hhV : (List.range (Lvm.Typed.phiVarsT + 1)).map (fun i => fe2At sig (rpos K.2 + 40 + 16 * i)) =
      (List.range (tVarsT + 1)).map fun i => fe2At sig (P + 360 + 16 * i) := by
    rw [hpK]
  -- `h(0) = acc_in.y`, `h(1) = Σ_{o'} eq(κ, o')·vs_{o'}`
  have hy0 : Lvm.E2T.hEvalD ((List.range (tVarsT + 1)).map fun i => fe2At sig (P + 360 + 16 * i)) 0 =
      Lvm.e2OfFE (Lvm.pubOfWS vk cL sig).accIn.y := by
    have e0 : ((ld2s (L iH) (tVarsT + 1)).getD 0 z2).val M = fe2At sig (P + 360) := by
      rw [ld2s_getD _ _ _ _ (by decide), ld2_val hS (by clear * - hh hT; omega)]
      exact congrArg (fe2At sig) (by clear * - hh; omega)
    rw [e0, hain tVarsT (by decide), hainv tVarsT (by decide)] at hA0
    have hyv : Lvm.e2OfFE (Lvm.pubOfWS vk cL sig).accIn.y =
        fe2At sig (headerAt (hdrFixS + 16 * Lvm.VEq.accVT)) := rfl
    simp only [Lvm.E2T.hEvalD, List.range_succ_eq_map, List.map_cons, List.foldr_cons, zero_mul, add_zero,
      Nat.mul_zero]
    rw [hA0, hyv]
    exact congrArg (fe2At sig) (by
      rw [show tVarsT = 45 from rfl, show Lvm.VEq.accVT = 45 from rfl]; simp only [headerAt, hdrFixS])
  have hy1 : Lvm.E2T.hEvalD ((List.range (tVarsT + 1)).map fun i => fe2At sig (P + 360 + 16 * i)) 1 =
      Lvm.E2T.yOwnD (vs.map (C2.val M)) ((List.range 4).map fun j => fe2At sig (P + 48 + 80 * j)) := by
    rw [← hhl, hEvalD_eq]
    simp only [one_pow, one_mul]
    rw [range_getD2, show ((ld2s (L iH) (tVarsT + 1)).map (C2.val M)).sum = sh.val M by rw [hsh, hz2, zero_add],
      hA1, hy, Lvm.E2T.yOwnD, dotF_eqKernel _ _ (by simp [hvs]), List.length_map, hkap]
  rw [q1, q2, Lvm.Q2.e2OfFE_feAt, hhV, hK1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hline, hht]
    unfold accCS
    rw [List.map_map]
    rfl
  · rw [hzv, hy0, hy1, beq_self_eq_true, beq_self_eq_true, beq_self_eq_true, hpt, a3, hs,
      show Lvm.Typed.selBitsT = 4 from rfl, hpκ, hok]
    rfl
  · show K.2.ent + 72 + (K.2.msg + 16 * (Lvm.Typed.phiVarsT + 1) + 8) + (0 + 16) = P + 1152
    rw [Nat.zero_add, hφ]; (clear * - hpK'; omega)

end

end Lvm.E2Q

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped

/-! ## The typed phases at S2GS (no table phase, `acc_in` after 18 lanes) -/

section TypedS

open Lvm.Q1 Lvm.Q2 DM Lvm.E2V

variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- `pubLanesS` with `leafOut` and `P20T`'s accumulator is `P20S`'s (proof help). -/
theorem pubLanesS_eq_P20S {pc : Params} (hlo : pc.leafOut = true) (hacc : pc.accV = P20T.accV) :
    pubLanesS pc = pubLanesS P20S := by
  unfold pubLanesS hdrFixL
  rw [hlo, hacc]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The typed phases in `PhaseAt` form at S2GS's circuit parameters `pc`** (`typed_phaseTL`'s twin for `typedGS`,
with `leafOut`: the child's `PUB` without `σ_leaf`, `pubOfWS`, `acc_in` after 18 lanes): where `typedGS`'s rows hold
and assert (gate on) on the lanes of `pc`'s phase `bus` (from `P`), V_S's `dTypedLG` on `pubOfWS` runs from `P` to
`typedEndL`, folds to the current proof's `PUB` accumulator (`accCS`), and its claims and evaluations are the gadget's
cells'. -/
theorem typed_phaseTS (pc : Params) (hlo : pc.leafOut = true) (hacc : pc.accV = P20T.accV) (vk cL : Vector UInt8 32)
    (hS : Streamed M sig T) {pb : Nat} (hg : M.k pb = 1)
    (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {z o zk ok : Cell} (hzE : z.ty = .E)
    (hoE : o.ty = .E) (hz : z.val M = 0) (ho : o.val M = 1) (hzK : zk.ty = .K) (hoK : ok.ty = .K)
    (hzk : zk.val M = 0) (hok1 : ok.val M = 1) {Td : TData} {N : Lvm.E2T.TNatT} (htd : TdOk Td N.toN)
    (p : Params) (hl : p.leafdecReads = 1) (hD : Td.mbD = p.busDepth) (m : M3) {P : Nat} (hL : BusLanesT (busL pc) P)
    (hpow : PowOkV (feAt sig) (typedChalsT pc)) (hT : typedEndL Td pc + 40 ≤ 8 * T)
    (hH : 11 + pubLanesS pc ≤ T) (q : Ptr) (hq : 1 ≤ q.e)
    (hok : Lvm.QSig.Ok c M (typedGS Td pc pb (pubLanesS pc) z o zk ok) q)
    (hm : ∀ i : BusIn, (m.busFinal i).ok = (i.values.length == 3 && i.leafdec == [0])) {α : Type}
    (mk : List FE2 → List FE2 → List FE2 → FE2 → α) :
    PhaseAt (Lvm.E2L.dTypedLG p N m (Lvm.pubOfWS vk cL sig) mk) sig P (typedEndL Td pc)
      (accCS M pb, mk ((typedGS Td pc pb (pubLanesS pc) z o zk ok q).1.1.ry.map (C2.val M))
        ((typedGS Td pc pb (pubLanesS pc) z o zk ok q).1.1.rv.map (C2.val M))
        ((typedGS Td pc pb (pubLanesS pc) z o zk ok q).1.1.rr.map (C2.val M))
        ((typedGS Td pc pb (pubLanesS pc) z o zk ok q).1.1.vR.val M),
        vs M (typedGS Td pc pb (pubLanesS pc) z o zk ok q).1.1.bus.pt,
        m.busFinal ⟨vs M (typedGS Td pc pb (pubLanesS pc) z o zk ok q).1.1.bus.al,
          (typedGS Td pc pb (pubLanesS pc) z o zk ok q).1.1.bus.be.val M,
          (typedGS Td pc pb (pubLanesS pc) z o zk ok q).1.1.bus.cnt.val M,
          vs M (typedGS Td pc pb (pubLanesS pc) z o zk ok q).1.1.bus.pt,
          vs M (typedGS Td pc pb (pubLanesS pc) z o zk ok q).1.1.bus.vals, [0],
          Lvm.pubOfWS vk cL sig⟩) := by
  have hpl : pubLanesS pc = pubLanesS P20S := pubLanesS_eq_P20S hlo hacc
  have hhf : hdrFixL pc = 18 := by unfold hdrFixL; rw [hlo]; rfl
  rw [hpl] at hok hH ⊢
  intro s hs hsok
  have hgv : (kc pb).val M = 1 := Lvm.QAcc.kc_val_one hg
  have hz2 : (⟨zk, zk⟩ : C2).val M = 0 := by
    show (⟨(zk.val M).c₀, (zk.val M).c₀⟩ : FE2) = 0; rw [hzk]; rfl
  have ho2 : (⟨ok, zk⟩ : C2).val M = 1 := by
    show (⟨(ok.val M).c₀, (zk.val M).c₀⟩ : FE2) = 1; rw [hok1, hzk]; rfl
  have hz2K : KC2 ⟨zk, zk⟩ := ⟨hzK, hzK⟩
  have ho2K : KC2 ⟨ok, zk⟩ := ⟨hoK, hzK⟩
  obtain ⟨pτ, pω, pZ, pγ, pW, pR, pκ, pt⟩ := powT_facts hL hpow
  have hP8 := hL.al
  -- through `mbPT`'s equation (as in `typed_phaseTL`)
  have hmb : mbPT pc = P + 10120 := (mbPT.eq_1 pc).trans hL.mb
  have hE := mbPT_leL Td pc
  -- the circuit's parts, at their pointers
  unfold typedGS at hok ⊢
  dsimp only at hok ⊢
  rw [hhf] at hok ⊢
  simp only [bind_apply, pure_apply] at ⊢
  obtain ⟨hZ, hok⟩ := okb hok
  obtain ⟨zr, hzr⟩ : ∃ x, (zeroGT ⟨zk, zk⟩ (kc pb) (busL pc) q).1 = x := ⟨_, rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ x, q.adv (zeroGT ⟨zk, zk⟩ (kc pb) (busL pc) q).2 = x := ⟨_, rfl⟩
  have RZ := zeroGT_run (c := c) hS hz2 hgv (P := P) (qz := (P + 1792) / 8) hL.tau hL.om
    (by clear * - hP8; omega) (fun k hk => by have := hL.zr k hk; clear * - this hP8; omega) hL.zv
    (by clear * - hT hE hmb; omega) pτ pω pZ q hZ.1 hZ.2
  rw [hzr] at RZ hok
  rw [hq1] at hok
  simp only [hzr, hq1]
  obtain ⟨hW, hok⟩ := okb hok
  obtain ⟨w, hw⟩ : ∃ x, (wireGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td pb (pubLanesS P20S) (busL pc) zr.2 q1).1 = x :=
    ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ x, q1.adv (wireGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td pb (pubLanesS P20S) (busL pc) zr.2 q1).2 = x :=
    ⟨_, rfl⟩
  have hs1 : rpos s = P := hs
  obtain ⟨z1, z2', z3, z4, z5⟩ := RZ s hs1 hsok
  have RW := wireGT_runS (c := c) vk cL hS hz2 ho2 hz2K ho2K hgv htd hvk (P := P + 4136) (qw := (P + 4256) / 8)
    (by rw [hL.gam]) (by clear * - hP8; omega) (fun k hk => by have := hL.wr k hk; clear * - this hP8; omega)
    (by rw [hL.wv]) (by rw [hL.wv4])
    (by clear * - hT hE hmb; omega) hH (by rw [show P + 4136 + 48 = P + 4184 from rfl]; exact pγ)
    (by rw [show P + 4136 + 80 = P + 4216 from rfl]; exact pW) zr.2 (by rw [z5]; simp [ld2s]) q1 hW.1 hW.2
  rw [hw] at RW hok
  rw [hq2] at hok
  simp only [hw, hq2]
  obtain ⟨hRl, hok⟩ := okb hok
  obtain ⟨r, hr⟩ : ∃ x, (relayGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td (busL pc) w.1 (w.2.2.getD 1 ⟨zk, zk⟩) q2).1 = x :=
    ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ x, q2.adv (relayGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td (busL pc) w.1
      (w.2.2.getD 1 ⟨zk, zk⟩) q2).2 = x := ⟨_, rfl⟩
  -- V's run
  unfold Lvm.E2L.dTypedLG
  rw [dbind_run]
  obtain ⟨Z, hZr⟩ : ∃ x, Lvm.E2T.dZeroT sig s = x := ⟨_, rfl⟩
  rw [hZr] at z1 z2' z3
  rw [hZr, dbind_run, Prod.fst, z1]
  obtain ⟨W1, W2, W3, W4, W5, W6, W7⟩ := RW Z.2 z3 z2'
  have RR := relayGT_run (c := c) hS hz2 ho2 hz2K ho2K hgv htd (N := N) (P := P + 6824) (qr := (P + 6864) / 8)
    (by clear * - hP8; omega) (fun k hk => by have := hL.rr k hk; clear * - this hP8; omega) (by rw [hL.rv])
    (by clear * - hT hE hmb; omega)
    (by rw [show P + 6824 = P + 6824 by rfl]; exact pR) w.1 W4 W5 (w.2.2.getD 1 ⟨zk, zk⟩) q2 hRl.1 hRl.2
  rw [hr] at RR hok
  rw [hq3] at hok
  simp only [hr, hq3]
  obtain ⟨hA, hok⟩ := okb hok
  obtain ⟨q4, hq4⟩ : ∃ x, q3.adv (qaccGS 18 ⟨zk, zk⟩ ⟨ok, zk⟩ pb (busL pc) zr.1 w.1 w.2.1 q3).2 = x := ⟨_, rfl⟩
  have RA := qaccGS_run (c := c) vk cL hS hz2 ho2 hz2K ho2K hg (P := P + 8968)
    (fun j hj => by rw [hL.kap j hj]) (by rw [hL.h]) (by rw [hL.t]) (by rw [hL.z])
    (by clear * - hT hE hmb; omega) hH pκ
    (by rw [show P + 8968 + 1104 = P + 10072 from rfl]; exact pt) zr.1 w.1 w.2.1 z4 W4
    (by rw [W6]; simp [ld2s]) q3 hA.1 hA.2
  rw [hq4] at hok
  simp only [hq4]
  -- the wiring's run
  obtain ⟨Wr, hWr⟩ : ∃ x, Lvm.E2T.dWiringT N (Lvm.pubOfWS vk cL sig) (zr.2.map (C2.val M)) sig Z.2 = x :=
    ⟨_, rfl⟩
  rw [hWr] at W1 W2 W3
  rw [hWr, W1]
  dsimp only
  have egd : (w.2.2.map (C2.val M)).getD 1 0 = (w.2.2.getD 1 ⟨zk, zk⟩).val M := by rw [← hz2, List.getD_map]
  rw [egd, dbind_run]
  -- the relayout's run
  obtain ⟨Rr, hRr⟩ : ∃ x, Lvm.E2T.dRelayT2 N (w.1.map (C2.val M)) ((w.2.2.getD 1 ⟨zk, zk⟩).val M) sig Wr.2 = x :=
    ⟨_, rfl⟩
  obtain ⟨R1, R2, R3, R4, R5, R6⟩ := RR Wr.2 (by clear * - W3; omega) W2
  rw [hRr] at R1 R2 R3
  rw [hRr, dbind_run, R1]
  dsimp only
  rw [← List.map_append]
  -- A23's run
  obtain ⟨Ar, hAr⟩ : ∃ x, Lvm.E2T.dAccT (Lvm.pubOfWS vk cL sig) ((zr.1 ++ w.1).map (C2.val M))
      (w.2.1.map (C2.val M)) sig Rr.2 = x := ⟨_, rfl⟩
  obtain ⟨A1, A2, A3⟩ := RA Rr.2 (by clear * - R3; omega) R2
  rw [hAr] at A1 A2 A3
  rw [hAr, dbind_run, A1]
  -- the mini-bus's GKR (no table phase)
  obtain ⟨hB, -⟩ := okb hok
  have e1 : busGD Td.mbD z o (kc pb) (mbPT pc) = busG p z o (kc pb) (mbPT pc) := by rw [hD]; rfl
  have eE : typedEndL Td pc = busEnd p (mbPT pc) := by unfold typedEndL; rw [hD]; rfl
  rw [e1] at hB ⊢
  rw [eE] at hT ⊢
  obtain ⟨b1, b2, b3⟩ := busG_replays (c := c) hS hz ho hgv p hl (P := mbPT pc) (by clear * - hmb hP8; omega)
    (by clear * - hT; omega) q4 hB Ar.2
    (by show Ar.2.ent + Ar.2.msg = _; simp only [rpos] at A3; clear * - A3 hmb; omega) A2
  obtain ⟨hbv, h3⟩ := busR_eq b3
  rw [dMiniL_eq, dbind_run]
  generalize busPh p sig Ar.2 = BB at b1 b2 hbv ⊢
  obtain ⟨bv, s1⟩ := BB
  simp only at b1 b2 hbv
  subst hbv
  have hok2 : (m.busFinal ⟨vs M (busG p z o (kc pb) (mbPT pc) q4).1.al, (busG p z o (kc pb) (mbPT pc) q4).1.be.val M,
      (busG p z o (kc pb) (mbPT pc) q4).1.cnt.val M, vs M (busG p z o (kc pb) (mbPT pc) q4).1.pt,
      vs M (busG p z o (kc pb) (mbPT pc) q4).1.vals, [0], Lvm.pubOfWS vk cL sig⟩).ok = true := by
    rw [hm]; show ((vs M (busG p z o (kc pb) (mbPT pc) q4).1.vals).length == 3 && [(0 : FE)] == [0]) = true
    rw [h3]; decide
  simp only [busV, bind_run', require_run', pure_run', hok2, b1]
  exact ⟨trivial, rfl, b2⟩

end TypedS

/-! ## `typedGS`'s shape -/

section ShapeS

open Lvm.Har Lvm.Q2

variable {c : Ctx} {M : Mem}

/-- **`typedGS`'s outputs** (`typedGL_shape`'s twin): the relay's and wire's cells are `K` pairs, no table outputs, and
the mini-bus's claims satisfy whatever `mbLinG` guarantees on a bus whose `α` and point cells are `E` cells, `busBits`
and `busDepth` of them. -/
theorem typedGS_shape (Td : TData) (p : Params) (pb n : Nat) (z o zk ok : Cell) (hD : Td.mbD = p.busDepth)
    (Φ : BusC → List CClaim → Prop)
    (hΦ : ∀ bc : BusC, bc.al.length = busBits → (∀ x ∈ bc.al, x.ty = .E) → (∀ x ∈ bc.pt, x.ty = .E) →
      bc.pt.length = p.busDepth → SoundG c M (mbLinG z o Td bc) (Φ bc)) :
    SoundG c M (typedGS Td p pb n z o zk ok) (fun t => ((t.1.ry.length = tY ∧ ∀ x ∈ t.1.ry, KC2 x) ∧
      (t.1.rr.length = tR ∧ ∀ x ∈ t.1.rr, KC2 x) ∧ KC2 t.1.vR ∧ (∀ x ∈ t.1.rv, KC2 x)) ∧ t.1.tab = [] ∧
      Φ t.1.bus t.2) := by
  have hsg : ∀ {α : Type} {m : BM α} {P : α → Prop}, Hs c M m P → SoundG c M m P := fun h q hH _ => h q hH
  unfold typedGS
  dsimp only
  refine soundG_bind (Φ := fun _ => True) (fun _ _ _ => trivial) fun zr _ => ?_
  refine soundG_bind (hsg (hs_wireGT_fst _ _ _ _ _ _ _ _)) fun w ⟨hw1, hw2⟩ => ?_
  refine soundG_bind (hsg (hs_relayGT_fst _ _ _ _ _ _ _)) fun r ⟨hr1, hr2⟩ => ?_
  refine soundG_bind (Φ := fun _ => True) (fun _ _ _ => trivial) fun _ _ => ?_
  refine soundG_bind (Φ := fun bc : BusC => bc.al.length = busBits ∧ (∀ x ∈ bc.al, x.ty = .E) ∧
    (∀ x ∈ bc.pt, x.ty = .E) ∧ bc.pt.length = p.busDepth) ?_ fun bc ⟨h1, h2, h3, h4⟩ => ?_
  · intro q _ _
    have e1 : busGD Td.mbD z o (kc pb) (mbPT p) = busG p z o (kc pb) (mbPT p) := by rw [hD]; rfl
    rw [e1]
    obtain ⟨ha, d, hd⟩ := busG_fst p z o (kc pb) (mbPT p) q
    refine ⟨by rw [ha, List.length_map, List.length_range], fun x hx => ?_, fun x hx => ?_,
      busG_pt_len p z o (kc pb) (mbPT p) q⟩
    · rw [ha] at hx
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx
      rfl
    · rw [hd] at hx
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx
      rfl
  refine soundG_bind (hΦ bc h1 h2 h3 h4) fun cs hcs => soundG_pure ⟨⟨⟨by rw [hw1]; simp, by
    rw [hw1]; exact kc2_range _ _ _⟩, ⟨by rw [hr1]; simp, by rw [hr1]; exact kc2_range _ _ _⟩,
    by rw [hr2]; exact kc2_ld2 _, ?_⟩, rfl, hcs⟩
  show ∀ x ∈ w.2.2, KC2 x
  rw [hw2]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  exact kc2_ld2 _

end ShapeS

end Lvm.E2Q
