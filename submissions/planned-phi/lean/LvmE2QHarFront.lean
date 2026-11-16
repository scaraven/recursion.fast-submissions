-- New for lvm2 E2-FT (E2F-C4): the S2GF front's phases for `harithF20` (roll 11's `p47_at` for `frontF`): the bits
-- of `n' − 1` on `K` cells (`borrowK`), their `E2` form for the wiring, and the front's run cut into its gadgets.
import LvmE2QHarLanes
import LvmE2QWPhase
import LvmE2QKGkrEq
import LvmE2QKLay
import LvmQAsmBorrow
import LvmQWireSound
import LvmE2QAsmSpec
import LvmE2QNodeFacts
import LvmE2QOpenPhase
import LvmE2QHarClaims
import LvmQRingCrtL
import LvmE2QHarGen

/-!
# The front's phases at S2GF

* **`borrowK_vs`**: `borrowK`'s cells (on `K` cells, the carry starting at the `K` one) are the bits of `N − 1`
  (roll 11's `borrow_vs`);
* **`bitsF_eq`**, **`kC2_bits`**: `bitsF z m` is the list of `z`'s bits; `K` bit cells paired with a `K` zero have
  those values in `E2` (`wire_phase`'s `hmb`).
-/

set_option autoImplicit false

namespace Lvm.Q1

/-- The tape at P20 (`n_log = 20`: `P = 15`). -/
theorem layOk2_15 : layOk2 15 = true := by rw [Lvm.Q1.layOk2_eq_lit, layerTB2T_eq_F, layOk2T_eq_R]; decide +kernel

/-- `KS` at P20 (`ksLog = 13`: `P = 9`). -/
theorem layOk2_9 : layOk2 9 = true := by rw [Lvm.Q1.layOk2_eq_lit, layerTB2T_eq_F, layOk2T_eq_R]; decide +kernel

end Lvm.Q1

namespace Lvm.E2Q

section P20F

open Lvm Lvm.Q2 Lvm.QShape

theorem regs_P20F : RegsP P20F := by
  unfold RegsP
  rw [show layout0 P20F = layout0 P20 from rfl, layout0_P20]
  decide +kernel

theorem dsel_P20F : DselP P20F := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end P20F

end Lvm.E2Q

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Har Lvm.QSig Lvm.QAsm

variable {c : Ctx} {M : Mem}

/-! ## The bits of `n' − 1` on `K` cells -/

-- `borrowK_vs`, `kC2_bits`, `laneC2_mk`, `const_val`, `powOkV_append`, `getD_map_range`, `sb_vals`, `ok_bindE`,
-- `rowG_rr`, `rowNuOk_of`, `mapB_add_vs` (and their helpers) are in `LvmE2QHarGen` (moved, lvm2 U-TAPE).

/-! ## Bits in `E2` -/

/-! ## `KS` (`callerD`) -/

/-- The `KS` gadget's slices are the lane pairs from `gkrQO2 P qs + 226`. -/
theorem gkr_slices (P qs : Nat) (inst out : Nat → C2) (b : Cell) (p : Ptr) :
    (Lvm.Q1.gkrGadgetE2 P qs inst out b p).1.slices =
      (List.range 64).map fun k => Lvm.Q1.laneC2 (Lvm.Q1.gkrQO2 P qs + 226 + 2 * k) := rfl

theorem slices_laneC2 (a : Nat) :
    ((List.range 64).map fun k => Lvm.Q1.laneC2 (a + 2 * k)).map (C2.val M) = Lvm.Q2.slicesOf M a := by
  simp only [List.map_map, Lvm.Q2.slicesOf]
  rfl

/-- `n` ground challenges' gadget cells (lane pairs at `q₀ + 10 i`, `8 q₀ = P + 48`) are `sampsG`. -/
theorem samps_vals {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {n q0 P : Nat} {xs : List C2}
    (hx : ∀ i < n, xs.getD i default = Lvm.Q1.laneC2 (q0 + 10 * i)) (hq : 8 * q0 = P + 48)
    (hT : q0 + 10 * n < T) :
    ((List.range n).map fun i => (xs.getD i default).val M) = Lvm.Q2.sampsG sig P n := by
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  rw [hx i hi', Lvm.Q1.laneC2_val hS (by omega)]
  exact congrArg _ (by omega)

/-- 25 `E2` scalars' gadget cells (lane pairs at `a + 2 l`, `8 a = P + 40`) are `readsE2`. -/
theorem reads_vals {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {n a P : Nat} {xs : List C2}
    (hx : ∀ l < n, xs.getD l default = Lvm.Q1.laneC2 (a + 2 * l)) (ha : 8 * a = P + 40) (hT : a + 2 * n < T) :
    ((List.range n).map fun l => (xs.getD l default).val M) = Lvm.Q2.readsE2 sig P n := by
  refine List.map_congr_left fun l hl => ?_
  have hl' := List.mem_range.mp hl
  rw [hx l hl', Lvm.Q1.laneC2_val hS (by omega)]
  exact congrArg _ (by omega)

/-- **`KS`'s phase** (`callerD (P + 4)`, roll 11's `kblock_sound` at `E2`): from `P3` (`ksLog` instance challenges
at lanes `q₀ + 10 i`, the 25 scalars at `kOut + 2 l`), E2F-QH4's GKR (`gkr_phase2`) then the row switch
(`rowSwitch_phase`, its row words the GKR's slices); the value has V's instance point and scalars, the GKR's result
and the row switch's value. -/
theorem callerD_at {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {P P3 q0 kOut qs qr tB z o : Nat}
    {ki kv : List C2} {gate : Cell} {p1 p2 : Ptr} (hlay : Lvm.Q1.layOk2 P = true)
    (hki : ∀ i < P + 4, ki.getD i default = Lvm.Q1.laneC2 (q0 + 10 * i)) (hq0 : 8 * q0 = P3 + 48)
    (hkv : ∀ l < 25, kv.getD l default = Lvm.Q1.laneC2 (kOut + 2 * l)) (hkO : 8 * kOut = P3 + 80 * (P + 4) + 40)
    (hqs : 8 * qs = P3 + 80 * (P + 4) + 448) (hqr : 8 * qr = 8 * Lvm.Q1.gkrEnd2 P qs - 40 + 40)
    (hT : qr + 9 * 6 + 2 < T) (hTg : Lvm.Q1.gkrEnd2 P qs ≤ T) (hTq : q0 + 10 * (P + 4) < T) (hTo : kOut + 50 < T)
    (hg : gate.val M = 1) (hz : M.e z = 0) (ho : M.e o = 1)
    (hhG : SegsHold c M p1
      (Lvm.Q1.gkrGadgetE2 P qs (fun i => ki.getD i default) (fun l => kv.getD l default) gate p1).2)
    (haG : SegsAssert M p1
      (Lvm.Q1.gkrGadgetE2 P qs (fun i => ki.getD i default) (fun l => kv.getD l default) gate p1).2)
    (hhR : SegsHold c M p2 (Lvm.Q2.rowG qr tB z o p2).2)
    (ht : ∀ j < 128, M.k (tB + j) = rowWordD (Lvm.Q2.slicesOf M (Lvm.Q1.gkrQO2 P qs + 226)) j)
    (hpow : Lvm.Q1.PowOkV (feAt sig) (Lvm.Q2.chalsG q0 E2V.gC1 (P + 4)))
    (hpowG : Lvm.Q1.PowOkV (feAt sig) (Lvm.Q1.gkrChals2 P qs)) :
    let ko := (Lvm.Q1.gkrGadgetE2 P qs (fun i => ki.getD i default) (fun l => kv.getD l default) gate p1).1
    Lvm.Har.PhaseAt (callerD (P + 4)) sig P3 (8 * qr - 40 + 504)
      (Lvm.Q2.sampsG sig P3 (P + 4), Lvm.Q2.readsE2 sig (P3 + 80 * (P + 4)) 25,
        ([(ko.wordPoint.map (C2.val M), ko.word.val M)], ko.slicePoint.map (C2.val M), ko.slices.map (C2.val M)),
        Lvm.Q2.rowValD (ko.slicePoint.map (C2.val M)) (ko.slices.map (C2.val M))
          ((Lvm.Q2.rowG qr tB z o p2).1.eqR.map (Cell.val M))) ∧
      (Lvm.Q2.rowValD (ko.slicePoint.map (C2.val M)) (ko.slices.map (C2.val M))
          ((Lvm.Q2.rowG qr tB z o p2).1.eqR.map (Cell.val M))).1.1 = (Lvm.Q2.rowG qr tB z o p2).1.target.val M := by
  intro ko
  have hG := Lvm.Q1.gkr_phase2 hlay (by omega) hS hTg hhG haG hg hpowG
  rw [samps_vals hS hki hq0 hTq, reads_vals hS (P := P3 + 80 * (P + 4)) hkv hkO (by omega),
    show 8 * qs - 48 = P3 + 80 * (P + 4) + 400 by omega] at hG
  have hsl : ko.slices.map (C2.val M) = Lvm.Q2.slicesOf M (Lvm.Q1.gkrQO2 P qs + 226) := by
    show (Lvm.Q1.gkrGadgetE2 P qs _ _ gate p1).1.slices.map _ = _
    rw [gkr_slices, slices_laneC2]
  have hR := Lvm.Q2.rowSwitch_phase hS hz ho hT hhR (P := 8 * Lvm.Q1.gkrEnd2 P qs - 40)
    hqr (ko.slicePoint.map (C2.val M)) (ko.slices.map (C2.val M))
    (fun j hj => by rw [hsl]; exact ht j hj)
  refine ⟨?_, hR.2⟩
  rw [show 8 * qr - 40 + 504 = 8 * Lvm.Q1.gkrEnd2 P qs - 40 + 504 by omega]
  exact Lvm.Q2.callerD_phase hq0 hpow hG hR.1

/-! ## The tape and the wiring (`tapeD`) -/

/-- The wiring gadget's slices are the lane pairs from its slice lane. -/
theorem wire_slices (P qw : Nat) (cv : Nat → C2) (mb sb : List Cell) (zk gate : Cell) (p : Ptr) :
    (Lvm.Q2.wireG2 P qw cv mb sb zk gate p).1.slices = Lvm.Q2.slices2 (Lvm.Q2.wireLanes (P + 5) qw).slices := rfl

theorem slices2_vals (a : Nat) : (Lvm.Q2.slices2 a).map (C2.val M) = Lvm.Q2.slicesOf M a := by
  simp only [Lvm.Q2.slices2, List.map_map, Lvm.Q2.slicesOf]
  rfl

set_option maxRecDepth 100000 in
/-- **The tape phase with the wiring** (`tapeD (P + 5)`, roll 11's `tape_phase`/`wire_phase` in `p47_at`): from `P4`
(the separator, `r_i` at lanes `q₀ + 10 i`, the 25 scalars at `tOut + 2 l`), E2F-QH4's tape GKR (`tape_phase2`), `n`'s
range and E2F-QH5's `wire_phase` (its row switch's words the wiring's slices). -/
theorem tapeD_at {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {P P4 q0 tOut qs qw tB z o : Nat}
    {r v : List C2} {mb sb : List Cell} {zk gate : Cell} {p1 p2 p3 : Ptr} (s' : List FK) (n sbsel dsel : Nat)
    (hlay : Lvm.Q1.layOk2 P = true)
    (hr : ∀ i < P + 5, r.getD i default = Lvm.Q1.laneC2 (q0 + 10 * i)) (hq0 : 8 * q0 = P4 + 120)
    (hv : ∀ l < 25, v.getD l default = Lvm.Q1.laneC2 (tOut + 2 * l)) (htO : 8 * tOut = P4 + 72 + 80 * (P + 5) + 40)
    (hqs : 8 * qs = P4 + 72 + 80 * (P + 5) + 448) (hqw : 8 * qw = 8 * Lvm.Q1.tapeEnd2 P qs - 40 + 40)
    (hTt : Lvm.Q1.tapeEnd2 P qs + 2 ≤ T) (hTq : q0 + 10 * (P + 5) < T) (hTo : tOut + 50 < T)
    (hTr : (Lvm.Q2.wireLanes (P + 5) qw).ring + 9 * 6 + 2 < T)
    (hg : gate.val M = 1) (hzk : zk.val M = 0) (hz : M.e z = 0) (ho : M.e o = 1) (hsb : sb.length = 256)
    (hmb : (mb.map fun b => Lvm.Q2.kC2 b zk).map (C2.val M) = E2V.bitsF (n - 1) (P + 5)) (hn : 1 ≤ n ∧ n ≤ 2 ^ (P + 5))
    (hsbv : (sb.map fun b => Lvm.Q2.kC2 b zk).map (C2.val M) = (List.range 256).map fun p => E2V.bitF (sBitsD s' p))
    (hhT : SegsHold c M p1
      (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).2)
    (haT : SegsAssert M p1
      (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).2)
    (hhW : SegsHold c M p2 (Lvm.Q2.wireG2 P qw
      (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate
        p2).2)
    (haW : SegsAssert M p2 (Lvm.Q2.wireG2 P qw
      (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate
        p2).2)
    (hhR : SegsHold c M p3 (Lvm.Q2.rowG (Lvm.Q2.wireLanes (P + 5) qw).ring tB z o p3).2)
    (ht : ∀ j < 128, M.k (tB + j) = rowWordD (Lvm.Q2.slicesOf M (Lvm.Q2.wireLanes (P + 5) qw).slices) j)
    (hpow : Lvm.Q1.PowOkV (feAt sig) (Lvm.Q2.chalsG q0 E2V.gC1 (P + 5)))
    (hpowT : Lvm.Q1.PowOkV (feAt sig) (Lvm.Q1.tapeChals2 P qs))
    (hpowW : Lvm.Q1.PowOkV (feAt sig) (Lvm.Q2.wireChals (P + 5) qw)) :
    Lvm.Har.PhaseAt (tapeD (P + 5) sbsel dsel s' n) sig P4 (8 * qw - 40 + 112 * (P + 5) + 1768)
      (Lvm.Q2.sampsG sig (P4 + 72) (P + 5), Lvm.Q2.readsE2 sig (P4 + 72 + 80 * (P + 5)) 25, (tapeGkrD (P + 5) (Lvm.Q2.sampsG sig (P4 + 72) (P + 5)) (Lvm.Q2.readsE2 sig (P4 + 72 + 80 * (P + 5)) 25)
      sig ⟨P4 + 72 + 80 * (P + 5) + 400, 0, true⟩).1,
        (((Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.sigma.map (C2.val M), (Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.final.val M), [(Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.gD.val M],
          (((Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.tau.map (C2.val M), Lvm.Q2.scFold2 (fun k => fe2At sig (8 * k)) 2 (Lvm.Q2.wireLanes (P + 5) qw).slot
            ((Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.gD.val M)), (Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.slices.map (C2.val M), (Lvm.Q2.rowValD ((Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.sigma.map (C2.val M) ++ (Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.tau.map (C2.val M) ++ E2V.selPtF dsel sbsel)
      ((Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.slices.map (C2.val M)) ((Lvm.Q2.rowG (Lvm.Q2.wireLanes (P + 5) qw).ring tB z o p3).1.eqR.map (Cell.val M)))))) ∧
      (Lvm.Q2.rowValD ((Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.sigma.map (C2.val M) ++ (Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.tau.map (C2.val M) ++ E2V.selPtF dsel sbsel)
      ((Lvm.Q2.wireG2 P qw (Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv mb sb zk gate p2).1.slices.map (C2.val M)) ((Lvm.Q2.rowG (Lvm.Q2.wireLanes (P + 5) qw).ring tB z o p3).1.eqR.map (Cell.val M))).1.1 = (Lvm.Q2.rowG (Lvm.Q2.wireLanes (P + 5) qw).ring tB z o p3).1.target.val M ∧ Lvm.Q1.Rep2 P (fun j => ((Lvm.Q1.tapeGadgetE2 P qs (fun i => r.getD i default) (fun l => v.getD l default) gate p1).1.cv j).val M) (tapeGkrD (P + 5) (Lvm.Q2.sampsG sig (P4 + 72) (P + 5)) (Lvm.Q2.readsE2 sig (P4 + 72 + 80 * (P + 5)) 25)
      sig ⟨P4 + 72 + 80 * (P + 5) + 400, 0, true⟩).1 false := by
  have hT := Lvm.Q1.tape_phase2 hlay (by omega) hS hTt hhT haT hg hpowT
  rw [samps_vals hS (P := P4 + 72) hr (by omega) hTq, reads_vals hS (P := P4 + 72 + 80 * (P + 5)) hv (by omega) (by omega),
    show 8 * qs - 48 = P4 + 72 + 80 * (P + 5) + 400 by omega] at hT
  obtain ⟨hT1, hT2⟩ := hT
  have hW := Lvm.Q2.wire_phase hS _ s' n sbsel dsel hzk hg hsb hmb (by omega) hsbv hT2
    (P5 := 8 * Lvm.Q1.tapeEnd2 P qs - 40) hqw hhW haW hz ho hhR
    (fun j hj => by rw [wire_slices, slices2_vals]; exact ht j hj) hTr hpowW
  obtain ⟨hW1, hW2⟩ := hW
  refine ⟨?_, hW2, hT2⟩
  rw [show 8 * qw - 40 + 112 * (P + 5) + 1768 = 8 * Lvm.Q1.tapeEnd2 P qs - 40 + 112 * (P + 5) + 1768 by omega]
  exact Lvm.Q2.tapeD_phase (by omega) hpow hT1 hn hW1

/-! ## The front at `P20F` -/

set_option maxHeartbeats 1000000 in
/-! ## The front gadgets' outputs (for `front_claimsG`) -/

-- `hs_true` is in `LvmE2QHarGen` (moved, lvm2 U-TAPE).

/-- The `KS` link's `eq(λ, ·)` cells are `K` cell pairs. -/
theorem ksLinkG2_omK (hk xl B K qa : ℕ) (gate : Cell) :
    Hs c M (Lvm.Q2.ksLinkG2 hk xl B K qa gate) (fun o => ∀ x ∈ o.om, Lvm.Q2.KC2 x) := by
  unfold Lvm.Q2.ksLinkG2
  refine hs_bind (hs_true _) fun z _ => hs_bind (Lvm.Q2.g2One_K z) fun one ho => ?_
  refine hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => ?_
  refine hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => ?_
  refine hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => ?_
  refine hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => ?_
  refine hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => ?_
  exact hs_bind (Lvm.Q2.hs_g2EqTab_K z [one] _ (by simpa using ho)) fun om hom => hs_pure hom

theorem rowNuOk_cast {nu : Lvm.Q2.RowNu} {a b : List Cell} (h : Lvm.Q2.RowNuOk M nu (a.map (Cell.val M)))
    (e : a = b) : Lvm.Q2.RowNuOk M nu (b.map (Cell.val M)) := e ▸ h

/-- The link's `M` coefficients `ω_l · sel` (`l < 17`). -/
theorem omS_spec (om : List C2) (sel z2 : C2) :
    Hs c M (Lvm.Q2.mapB (fun l => Lvm.Q2.g2Mul (om.getD l default) sel z2) (List.range 17))
      (fun rs => ∀ l < 17, Lvm.Q2.KC2 (rs.getD l default) ∧
        (rs.getD l default).val M = (om.getD l default).val M * sel.val M + z2.val M) :=
  hs_mono (hs_mapB_getD _ (fun l r => Lvm.Q2.KC2 r ∧ r.val M = (om.getD l default).val M * sel.val M + z2.val M)
    (fun l => Lvm.QShape.hs_and (Lvm.Q2.g2Mul_K _ _ _) (Lvm.Q2.hs_g2Mul _ _ _)) _) fun rs h l hl => by
    have := h l (by simpa using hl)
    simpa using this

/-- A relocated template's rows from `cb` on are `K` rows when the instructions' are (generic in `cb`: the kernel
never evaluates it). -/
theorem tpl_K {cb n q cst : ℕ} {ins : List Lvm.Q1.Ins} (hl : ins.length = cb + n) (hK : ∀ x ∈ ins.drop cb, x.ty = .K)
    {i : ℕ} (hi : i < n) : ((Lvm.Q1.tplOf (ins.map (Lvm.Q1.relocI q cst))).getD (cb + i) default).ty = Ty.K := by
  have h : cb + i < ins.length := by omega
  rw [Lvm.Q1.tplOf_getD _ (by rw [List.length_map]; exact h), List.getD_eq_getElem _ _ (by rw [List.length_map]; exact h),
    List.getElem_map]
  have hj : i < (ins.drop cb).length := by rw [List.length_drop]; omega
  have := hK _ (List.getElem_mem hj)
  rw [List.getElem_drop] at this
  exact this

theorem lastC2_K {P : ℕ} (hP : Lvm.Q1.layOk2 P = true) {lay : LoopOut} {q cst : ℕ}
    (hlay : lay.tpl = Lvm.Q1.layTpl2 P q cst) {j : ℕ} (hj : j < 57 + P) : Lvm.Q2.KC2 (Lvm.Q1.lastC2 P lay j) := by
  simp only [Lvm.Q1.layOk2, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hP
  obtain ⟨⟨hl, -⟩, hK⟩ := hP
  have key : ∀ i, i < 2 * (57 + P) → (lay.cell (Lvm.Q1.cbOf2 P + i) 11).ty = .K := by
    intro i hi
    unfold LoopOut.cell
    dsimp only
    rw [hlay, Lvm.Q1.layTpl2]
    exact tpl_K hl (fun x hx => (hK x hx).1) hi
  unfold Lvm.Q1.lastC2 LoopOut.cell2
  rw [Nat.add_assoc]
  exact ⟨key (2 * j) (by omega), key (2 * j + 1) (by omega)⟩

/-- **The `KS` gadget's points and word are `K` cell pairs** (`P + 10` coordinates). -/
theorem gkr_K {P qs : ℕ} {inst out : ℕ → C2} {b : Cell} (hP : Lvm.Q1.layOk2 P = true)
    (hi : ∀ i < P + 4, Lvm.Q2.KC2 (inst i)) :
    Hs c M (Lvm.Q1.gkrGadgetE2 P qs inst out b) (fun ko => (∀ x ∈ ko.wordPoint, Lvm.Q2.KC2 x) ∧
      ko.wordPoint.length = P + 10 ∧ Lvm.Q2.KC2 ko.word ∧ (∀ x ∈ ko.slicePoint, Lvm.Q2.KC2 x) ∧
      ko.slicePoint.length = P + 10) := by
  unfold Lvm.Q1.gkrGadgetE2
  refine hs_bind (hs_true _) fun p _ => hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => ?_
  refine hs_bind (hs_true _) fun _ _ => hs_bind (P := fun o => o.tpl = Lvm.Q1.layTpl2 P (qs + 61) p.k)
    (fun _ _ => rfl) fun lay hlay => ?_
  refine hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => ?_
  refine hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_pure ?_
  have hch : ∀ (d q : ℕ) (n : ℕ), ∀ x ∈ (List.range n).map (Lvm.Q1.scChal2 d q), Lvm.Q2.KC2 x := by
    intro d q n x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact ⟨rfl, rfl⟩
  refine ⟨fun x hx => ?_, by simp only [List.length_append, List.length_map, List.length_range], ⟨rfl, rfl⟩,
    fun x hx => ?_, by simp only [List.length_append, List.length_map, List.length_range]; omega⟩
  · rcases List.mem_append.mp hx with h | h
    · obtain ⟨i, hi', rfl⟩ := List.mem_map.mp h
      exact hi i (List.mem_range.mp hi')
    · exact hch _ _ _ x h
  · rcases List.mem_append.mp hx with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hch _ _ _ x h
      · obtain ⟨i, hi', rfl⟩ := List.mem_map.mp h
        exact lastC2_K hP hlay (by have := List.mem_range.mp hi'; omega)
    · exact hch _ _ _ x h

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- **The front's phases at a stage with `P20`'s front** (`StE2`: S2GF or S2GT; roll 11's `p47_at` for `frontF C`): from the front's rows and assertions
(gate on), the proof-of-work answers (`powFront`), the row switches' words (the two `rowAux` blocks), `n'`'s bits and
range and the bits of `s'`, V's tape (with the wiring), `KS` and `KS` link phases run from their starts to the next
phase's start. -/
theorem front_phasesG {C : QCfg} (hE : StE2 C.p) (hA : alignB C.p = true) (hR : RegsP C.p) (hD : DselP C.p)
    (hBlk : spongeBlocks C.p - 1 < 2 ^ C.p.ksLog) (hKsp : ksSplit C.p + 399 + 31 < 2 ^ C.p.ksLog)
    {sig : ByteArray} {q : Ptr} (hS : Lvm.Q1.Streamed M sig (streamLanes C.p))
    (hTo : posOf C.p (phaseItem0 C.p .openMain) + 48 ≤ 8 * streamLanes C.p)
    (hg : M.k (pbB C) = 1) (hpow : Lvm.Q1.PowOkV (feAt sig) (powFront C.p))
    (hrw : ∀ j < 128, M.k (tBw C + j) = rowWordD (Lvm.Q2.slicesOf M (wireSlices C.p)) j)
    (hrk : ∀ j < 128, M.k (tBk C + j) = rowWordD (Lvm.Q2.slicesOf M (ksSlices C.p)) j)
    (pub : Pub) (hnb : ∀ j < 20, (kc ((sigIn C).bn + 2 + j)).val M = bitE pub.n j)
    (hn : 1 ≤ pub.n ∧ pub.n ≤ 2 ^ 20) (hsb : ∀ i < 256, M.k (bsB C + i) = if sBitsD pub.s i then 1 else 0)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) (zc : Cell) (b : Bool)
    (hsm : b = true → pub.n ≤ 2 ^ 18) (h : Lvm.QSig.Ok c M (frontF C) q) :
    ∃ tp co lo,
      Lvm.Har.PhaseAt (tapeD C.p.logN (dSelBits C.p) (dSel C.p) pub.s pub.n) sig
        (posOf C.p (phaseItem0 C.p .tape)) (posOf C.p (phaseItem0 C.p .ks)) tp ∧
      Lvm.Har.PhaseAt (callerD C.p.ksLog) sig (posOf C.p (phaseItem0 C.p .ks))
        (posOf C.p (phaseItem0 C.p .ksLink)) co ∧
      Lvm.Har.PhaseAt (ksLinkD C.p.ksLog (ksXLog C.p) (contRows C.p)) sig (posOf C.p (phaseItem0 C.p .ksLink))
        (posOf C.p (phaseItem0 C.p .openMain)) lo ∧
      List.Forall₂ (Lvm.Q2.FRelZ M zc b) (frontF C q).1.cs (frontClaimsD C.p pub tp co lo) ∧
      vs M (frontF C q).1.mb = selectorPoint (pub.n - 1) 20 := by
  have hn' := hn
  obtain ⟨hn1, hn2⟩ := hn'
  have hlogN : C.p.logN = 20 := hD.2.2.2.2.2.2.1
  have hksL : C.p.ksLog = 13 := hD.2.2.2.2.1
  obtain ⟨T, hTl⟩ : ∃ T, streamLanes C.p = T := ⟨_, rfl⟩
  rw [hTl] at hS hTo
  have hgv : (kc (pbB C)).val M = 1 := by rw [Cell.val_K, hg, ofK_one]
  -- the positions (E2F-QH6's `LvmE2QHarPos`, the lanes at every index)
  have h1 := hE
  have pSep := tape_sep h1 hA
  have pRs := tape_rs h1 hA
  have pOut := tape_out h1 hA
  have pQs := tape_qsA h1 hA
  have pTE := tape_end h1 hA (by rw [hlogN]; norm_num)
  have pQw := wire_qw h1 hA
  have pWB := wire_body h1 hA
  have pWR := wire_ring h1 hA
  have pKs := ks_rs h1 hA
  have pKo := ks_out h1 hA
  have pKq := ks_qsA h1 hA
  have pKe := ks_end h1 hA (by rw [hksL]; norm_num)
  have pKr := ks_ring h1 hA
  have pLq := link_qa h1 hA
  have pLe := link_end h1 hA
  have hrs : rowSwitchStages = 7 := rfl
  have hlb : laneBits = 5 := rfl
  rw [hrs] at pWR pKr
  rw [hlb] at pLe
  have hri : ∀ i < C.p.logN, 8 * laneOf C.p (phaseItem0 C.p .tape + 2 + 2 * i) =
      posOf C.p (phaseItem0 C.p .tape) + 72 + 80 * i + 48 := fun i hi => by
    have := tape_ri h1 hA hi
    rw [phaseLane, ← Nat.add_assoc, pSep] at this
    exact this
  have hki : ∀ i < C.p.ksLog, 8 * laneOf C.p (phaseItem0 C.p .ks + 2 * i + 1) =
      posOf C.p (phaseItem0 C.p .ks) + 80 * i + 48 := fun i hi => by
    have := ks_ri h1 hA hi
    rw [phaseLane, ← Nat.add_assoc] at this
    exact this
  -- the proof of work, by phase
  simp only [powFront, getD_toArray, typedChalsX, List.append_nil] at hpow
  obtain ⟨hp5, hpL⟩ := powOkV_append hpow
  obtain ⟨hp4, hpG⟩ := powOkV_append hp5
  obtain ⟨hp3, hpK⟩ := powOkV_append hp4
  obtain ⟨hp2, hpW⟩ := powOkV_append hp3
  obtain ⟨hpR, hpT⟩ := powOkV_append hp2
  -- the position facts in lane form
  simp only [phaseLane] at pOut pQs pTE pQw pKo pKq pKe pLq
  simp only [ringLane, phaseEnd] at pWR pKr
  simp only [wireSlices, ksSlices, phaseLane] at hrw hrk
  have e5 : C.p.logN - 5 + 5 = C.p.logN := by omega
  have e4 : C.p.ksLog - 4 + 4 = C.p.ksLog := by omega
  have hr0 := hri 0 (by omega)
  have hk0 := hki 0 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hr0 hk0
  rw [show phaseItem0 C.p .tape + 1 + 2 * C.p.logN + 1 = phaseItem0 C.p .tape + (2 * C.p.logN + 2) by omega]
    at pOut
  rw [show phaseItem0 C.p .ks + 2 * C.p.ksLog + 1 = phaseItem0 C.p .ks + (2 * C.p.ksLog + 1) by omega] at pKo
  have hwl : ∀ qw : Nat, (Lvm.Q2.wireLanes (C.p.logN - 5 + 5) qw).ring = qw + 438 := fun qw => by
    simp only [Lvm.Q2.wireLanes, Lvm.Q2.roundLanes2]; omega
  have hwr : laneOf C.p (phaseItem0 C.p .ks - 7) =
      (Lvm.Q2.wireLanes (C.p.logN - 5 + 5) (laneOf C.p (phaseItem0 C.p .wire + 0))).ring := by
    rw [hwl]; omega
  have hgE : laneOf C.p (phaseItem0 C.p .ks + (2 * C.p.ksLog + 2)) ≤
      Lvm.Q1.gkrEnd2 (C.p.ksLog - 4) (laneOf C.p (phaseItem0 C.p .ks + (2 * C.p.ksLog + 2))) := by
    unfold Lvm.Q1.gkrEnd2 Lvm.Q1.gkrQO2; omega
  have htE : laneOf C.p (phaseItem0 C.p .tape + (2 * C.p.logN + 3)) ≤
      Lvm.Q1.tapeEnd2 (C.p.logN - 5) (laneOf C.p (phaseItem0 C.p .tape + (2 * C.p.logN + 3))) := by
    unfold Lvm.Q1.tapeEnd2 Lvm.Q1.tapeQ2; omega
  -- the arithmetic for `KS`, the link and the ends (before the phase facts enter the context: `omega` scans it)
  have kq0 : 8 * laneOf C.p (phaseItem0 C.p .ks + 1) = posOf C.p (phaseItem0 C.p .ks) + 48 := by omega
  have kiL : ∀ i < C.p.ksLog - 4 + 4, laneOf C.p (phaseItem0 C.p .ks + 2 * i + 1) =
      laneOf C.p (phaseItem0 C.p .ks + 1) + 10 * i := fun i hi => by have := hki i (by omega); omega
  have kO : 8 * laneOf C.p (phaseItem0 C.p .ks + 2 * C.p.ksLog) =
      posOf C.p (phaseItem0 C.p .ks) + 80 * (C.p.ksLog - 4 + 4) + 40 := by omega
  have kqs : 8 * laneOf C.p (phaseItem0 C.p .ks + (2 * C.p.ksLog + 2)) =
      posOf C.p (phaseItem0 C.p .ks) + 80 * (C.p.ksLog - 4 + 4) + 448 := by omega
  have kqr : 8 * laneOf C.p (phaseItem0 C.p .ksLink - 7) = 8 * Lvm.Q1.gkrEnd2 (C.p.ksLog - 4)
      (laneOf C.p (phaseItem0 C.p .ks + (2 * C.p.ksLog + 2))) - 40 + 40 := by omega
  have kT : laneOf C.p (phaseItem0 C.p .ksLink - 7) + 9 * 6 + 2 < T := by omega
  have kTg : Lvm.Q1.gkrEnd2 (C.p.ksLog - 4) (laneOf C.p (phaseItem0 C.p .ks + (2 * C.p.ksLog + 2))) ≤ T := by
    omega
  have kTq : laneOf C.p (phaseItem0 C.p .ks + 1) + 10 * (C.p.ksLog - 4 + 4) < T := by omega
  have kTo : laneOf C.p (phaseItem0 C.p .ks + 2 * C.p.ksLog) + 50 < T := by omega
  have eKS : 8 * laneOf C.p (phaseItem0 C.p .ksLink - 7) - 40 + 504 = posOf C.p (phaseItem0 C.p .ksLink) := by
    omega
  have lT : Lvm.Q2.ksLinkQV C.p.ksLog (laneOf C.p (phaseItem0 C.p .ksLink + 1)) + 8 < T := by
    unfold Lvm.Q2.ksLinkQV Lvm.Q2.ksLinkQ1 Lvm.Q2.roundLanes2; omega
  have eLK : posOf C.p (phaseItem0 C.p .ksLink) + 80 * (C.p.ksLog + 5) + 112 * C.p.ksLog + 64 =
      posOf C.p (phaseItem0 C.p .openMain) := by omega
  have eTW : 8 * laneOf C.p (phaseItem0 C.p .wire + 0) - 40 + 112 * (C.p.logN - 5 + 5) + 1768 =
      posOf C.p (phaseItem0 C.p .ks) := by omega
  -- the front's gadgets (`ok_bind`: every next pointer an opaque variable)
  obtain ⟨fo, hfo⟩ : ∃ fo, (frontF C q).1 = fo := ⟨_, rfl⟩
  rw [hfo]
  simp only [frontF, getD_toArray, Lvm.Q1.tapeGadgetE2F_eq,
    Lvm.Q1.gkrGadgetE2F_eq] at h hfo
  obtain ⟨q1, hZ, h, E⟩ := ok_bindE h
  rw [E] at hfo
  rw [show (const .E 0 (kc 0) q).1 = ec q.e from rfl] at h hfo
  obtain ⟨q2, hO, h, E⟩ := ok_bindE h
  rw [E] at hfo
  rw [show (const .E 1 (kc 0) q1).1 = ec q1.e from rfl] at h hfo
  obtain ⟨q3, hZK, h, E⟩ := ok_bindE h
  rw [E] at hfo
  rw [show (const .K 0 (kc 0) q2).1 = kc q2.k from rfl] at h hfo
  obtain ⟨q4, hOK, h, E⟩ := ok_bindE h
  rw [E] at hfo
  rw [show (const .K 1 (kc 0) q3).1 = kc q3.k from rfl] at h hfo
  have hz : M.e q.e = 0 := (const_val hZ.1).trans ofK_zero
  have ho : M.e q1.e = 1 := (const_val hO.1).trans ofK_one
  have hzk : (kc q2.k).val M = 0 := (const_val hZK.1).trans ofK_zero
  have hok : M.k q3.k = 1 := Lvm.Q1.fe_ofK_inj ((const_val hOK.1).trans ofK_one.symm)
  -- the tape, `n' − 1`'s bits, the wiring and its row switch
  obtain ⟨q5, hT, h, E⟩ := ok_bindE h
  rw [E] at hfo
  obtain ⟨q6, hB, h, E⟩ := ok_bindE h
  rw [E] at hfo
  obtain ⟨q7, hW, h, E⟩ := ok_bindE h
  rw [E] at hfo
  obtain ⟨q8, hRW, h, E⟩ := ok_bindE h
  rw [E] at hfo
  obtain ⟨q9, hNW, h, E⟩ := ok_bindE h
  rw [E] at hfo
  -- `KS` and its row switch, the link
  obtain ⟨q10, hG, h, E⟩ := ok_bindE h
  rw [E] at hfo
  obtain ⟨q11, hRK, h, E⟩ := ok_bindE h
  rw [E] at hfo
  obtain ⟨q12, hNK, h, E⟩ := ok_bindE h
  rw [E] at hfo
  obtain ⟨q13, hL, h, E⟩ := ok_bindE h
  rw [E] at hfo
  obtain ⟨q14, hME, h, E⟩ := ok_bindE h
  rw [E] at hfo
  obtain ⟨q15, hOS, -, E⟩ := ok_bindE h
  rw [E] at hfo
  -- `n' − 1`'s bits, `s'`'s bits
  have hmbv := borrowK_vs (N := pub.n) (show M.k (kc q3.k).n = 1 from hok)
    (fun j hj => hnb j (by rw [hlogN] at hj; exact hj)) hn.1 hB.1
  have hmb := kC2_bits (m := C.p.logN - 5 + 5) hzk (by rw [e5]; exact hmbv)
  -- the tape with the wiring
  have hRW0 := hRW.1
  have hRK0 := hRK.1
  have hRWo := hRW
  have hRKo := hRK
  rw [show phaseEnd C.p .wire = phaseItem0 C.p .ks from rfl, hwr] at hRW
  rw [show phaseEnd C.p .ks = phaseItem0 C.p .ksLink from rfl] at hRK
  have TD := tapeD_at hS (P4 := posOf C.p (phaseItem0 C.p .tape))
    (q0 := laneOf C.p (phaseItem0 C.p .tape + 2)) (tOut := laneOf C.p (phaseItem0 C.p .tape + (2 * C.p.logN + 1)))
    pub.s pub.n (dSelBits C.p) (dSel C.p) (by rw [show C.p.logN - 5 = 15 by omega]; exact Lvm.Q1.layOk2_15)
    (fun i hi => by
      rw [getD_map_range _ (by omega)]
      have := hri i (by omega)
      congr 1; omega)
    (by omega) (fun l hl => getD_map_range _ hl) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hwl]; omega) hgv hzk hz ho (by simp [sbCells]) hmb ⟨hn.1, by rw [e5, hlogN]; exact hn.2⟩
    (sb_vals hzk pub.s hsb) hT.1 hT.2 hW.1 hW.2 hRW.1 (by rw [e5]; exact hrw) (by rw [e5]; exact hpR) hpT
    (by rw [e5]; exact hpW)
  obtain ⟨TD1, TD2, -⟩ := TD
  have TD1' := phaseAt_cast TD1 (F' := tapeD C.p.logN (dSelBits C.p) (dSel C.p) pub.s pub.n)
    (P'' := posOf C.p (phaseItem0 C.p .ks)) (by rw [e5]) eTW
  -- `KS`
  have CD := callerD_at hS (P3 := posOf C.p (phaseItem0 C.p .ks)) (q0 := laneOf C.p (phaseItem0 C.p .ks + 1))
    (kOut := laneOf C.p (phaseItem0 C.p .ks + 2 * C.p.ksLog))
    (by rw [show C.p.ksLog - 4 = 9 by omega]; exact Lvm.Q1.layOk2_9)
    (fun i hi => by rw [getD_map_range _ (by rw [e4] at hi; exact hi), kiL i hi])
    kq0 (fun l hl => getD_map_range _ hl) kO kqs kqr kT kTg kTq kTo hgv hz ho hG.1 hG.2 hRK.1 hrk
    (by rw [e4]; exact hpK) hpG
  obtain ⟨CD1, CD2⟩ := CD
  have CD' := phaseAt_cast CD1 (F' := callerD C.p.ksLog) (P'' := posOf C.p (phaseItem0 C.p .ksLink)) (by rw [e4])
    eKS
  -- the link
  have LK := Lvm.Q2.ksLink_phase hS hgv hBlk hKsp pLq lT
    hL.1 hL.2 hpL
  have LK' := phaseAt_cast LK (F' := ksLinkD C.p.ksLog (ksXLog C.p) (contRows C.p))
    (P'' := posOf C.p (phaseItem0 C.p .openMain)) rfl eLK
  rw [← hfo]
  refine ⟨_, _, _, TD1', CD', LK', ?_, ?_⟩
  · simp only [pure_apply]
    have hz2v : (⟨kc q2.k, kc q2.k⟩ : C2).val M = 0 := by
      show (⟨((kc q2.k).val M).c₀, ((kc q2.k).val M).c₀⟩ : FE2) = 0
      rw [hzk]; rfl
    have ho2v : (⟨kc q3.k, kc q2.k⟩ : C2).val M = 1 := by
      show (⟨((kc q3.k).val M).c₀, ((kc q2.k).val M).c₀⟩ : FE2) = 1
      rw [Cell.val_K, hok, ofK_one, hzk]; rfl
    have hXw : laneOf C.p (phaseEnd C.p .wire - 7) =
        (Lvm.Q2.wireLanes (C.p.logN - 5 + 5) (laneOf C.p (phaseItem0 C.p .wire + 0))).ring := by
      rw [show phaseEnd C.p .wire = phaseItem0 C.p .ks from rfl, hwr]
    have hXk : laneOf C.p (phaseEnd C.p .ks - 7) = laneOf C.p (phaseItem0 C.p .ksLink - 7) := by
      rw [show phaseEnd C.p .ks = phaseItem0 C.p .ksLink from rfl]
    have hWS := Lvm.Q2.wireG2_sound _ _ _ _ _ _ _ (pub.n - 1) hzk hgv (by simp [sbCells]) hmb
      (by rw [e5, hlogN]; omega) _ hW.1 hW.2
    have hLS := Lvm.Q2.ksLinkG2_sound hgv hBlk hKsp _ hL.1 hL.2
    have hGK := gkr_K (by rw [show C.p.ksLog - 4 = 9 by omega]; exact Lvm.Q1.layOk2_9)
      (fun i hi => by rw [getD_map_range _ (by omega)]; exact ⟨rfl, rfl⟩) _ hG.1
    -- the gadgets' outputs as opaque values (the claims' unification never meets a builder run)
    obtain ⟨nuW, hnuWo⟩ := ok_out hNW
    obtain ⟨nuK, hnuKo⟩ := ok_out hNK
    obtain ⟨omS, homSo⟩ := ok_out hOS
    obtain ⟨mbE, hmbEo⟩ := ok_out hME
    obtain ⟨wo, hwoo⟩ := ok_out hW
    obtain ⟨rwo, hrwo⟩ := ok_out hRWo
    obtain ⟨rko, hrko⟩ := ok_out hRKo
    obtain ⟨ko, hkoo⟩ := ok_out hG
    obtain ⟨kl, hklo⟩ := ok_out hL
    rw [hnuWo, hnuKo, homSo, hmbEo, hwoo, hrwo, hrko, hkoo, hklo]
    rw [hwoo] at TD2
    rw [hkoo] at CD2
    refine front_claimsG hR hD ?hz2 ?ho2 ?hz2K ?ho2K ?hzE ?hoE ?hr ?hrl ?hv ?htr ?htv ?hsgK ?hsgl ?htaK ?htal ?htr1
      ?hnuW ?hmbE ?hh ?hsm ?hn ?hwpK ?hwpl ?hwK ?hspK ?hspl ?hcr1 ?hnuK ?hkiK ?hkil ?hcr ?hkvK ?hcv
      ?hshK ?hshl ?hkcl ?homK ?hom ?hsel ?homS ?hvl ?hvK
    case hz2 => exact hz2v
    case ho2 => exact ho2v
    case hz2K => exact ⟨rfl, rfl⟩
    case ho2K => exact ⟨rfl, rfl⟩
    case hzE => exact hz
    case hoE => exact ho
    case hr =>
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨rfl, rfl⟩
    case hrl => simp [hlogN]
    case hv =>
      intro l hl
      rw [getD_map_range _ (by omega)]
      exact ⟨rfl, rfl⟩
    case htr =>
      rw [e5, ← samps_vals hS (P := posOf C.p (phaseItem0 C.p .tape) + 72)
        (q0 := laneOf C.p (phaseItem0 C.p .tape + 2))
        (xs := (List.range C.p.logN).map fun i => Lvm.Q1.laneC2 (laneOf C.p (phaseItem0 C.p .tape + 2 + 2 * i)))
        (fun i hi => by
          rw [getD_map_range _ (by omega)]
          have := hri i (by omega)
          congr 1; omega) (by omega) (by omega), map_getD_range]
    case htv =>
      intro l hl
      rw [e5, ← reads_vals hS (P := posOf C.p (phaseItem0 C.p .tape) + 72 + 80 * C.p.logN)
        (a := laneOf C.p (phaseItem0 C.p .tape + (2 * C.p.logN + 1))) (n := 25)
        (fun l hl => getD_map_range _ hl) (by omega) (by omega)]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
    case hsgK => rw [← hwoo, hWS.1]; exact ld2_K _
    case hsgl => rw [← hwoo, hWS.1]; simp [Lvm.Q2.sc2Ans, hlogN]
    case htaK => rw [← hwoo, hWS.2.2.2.2.1]; exact ld2_K _
    case htal => rw [← hwoo, hWS.2.2.2.2.1]; simp [Lvm.Q2.sc2Ans]
    case htr1 => rw [← hrwo, TD2, hXw]
    case hnuW =>
      rw [← hnuWo]
      exact rowNuOk_cast (rowNuOk_of hS hz ho (by rw [hXw, hwl]; omega) hRW0 hNW.1) (by rw [hXw])
    case hmbE =>
      rw [← hmbEo]
      exact (mapB_add_vs (by rw [Cell.val_E, hz]) _ _ hME.1).trans (by rw [hmbv, selectorPoint_bits, hlogN])
    case hh => exact hh
    case hsm => exact hsm
    case hn => exact hn.1
    case hwpK => rw [← hkoo]; exact hGK.1
    case hwpl => rw [← hkoo, hGK.2.1, hksL]
    case hwK => rw [← hkoo]; exact hGK.2.2.1
    case hspK => rw [← hkoo]; exact hGK.2.2.2.1
    case hspl => rw [← hkoo, hGK.2.2.2.2, hksL]
    case hcr1 => rw [← hrko, hXk]; exact CD2
    case hnuK =>
      rw [← hnuKo]
      exact rowNuOk_cast (rowNuOk_of hS hz ho (by rw [hXk]; exact kT) hRK0 hNK.1) (by rw [hXk])
    case hkiK =>
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨rfl, rfl⟩
    case hkil => simp [hksL]
    case hcr =>
      rw [e4, ← samps_vals hS (P := posOf C.p (phaseItem0 C.p .ks)) (q0 := laneOf C.p (phaseItem0 C.p .ks + 1))
        (xs := (List.range C.p.ksLog).map fun i => Lvm.Q1.laneC2 (laneOf C.p (phaseItem0 C.p .ks + 2 * i + 1)))
        (fun i hi => by rw [getD_map_range _ hi, kiL i (by omega)]) kq0 (by omega), map_getD_range]
    case hkvK =>
      intro l hl
      rw [getD_map_range _ hl]
      exact ⟨rfl, rfl⟩
    case hcv =>
      intro l hl
      rw [← reads_vals hS (P := posOf C.p (phaseItem0 C.p .ks) + 80 * (C.p.ksLog - 4 + 4))
        (a := laneOf C.p (phaseItem0 C.p .ks + 2 * C.p.ksLog)) (n := 25)
        (fun l hl => getD_map_range _ hl) kO (by omega)]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
    case hshK => rw [← hklo, hLS.2.1]; exact ld2_K _
    case hshl => rw [← hklo, hLS.2.1]; simp [Lvm.Q2.sc2Ans, hksL]
    case hkcl => rw [← hklo, hLS.1]; simp [hksL]
    case homK => rw [← hklo]; exact ksLinkG2_omK _ _ _ _ _ _ _ hL.1
    case hom => rw [← hklo]; exact hLS.2.2.2.2.1
    case hsel => rw [← hklo]; exact hLS.2.2.2.2.2.1
    case homS =>
      rw [← homSo, ← hklo]
      intro l hl
      obtain ⟨h1, h2⟩ := omS_spec _ _ _ _ hOS.1 l hl
      exact ⟨h1, by rw [h2, hz2v, add_zero]⟩
    case hvl => rw [← hklo, hLS.2.2.1]; simp
    case hvK =>
      rw [← hklo, hLS.2.2.1]
      intro x hx
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨rfl, rfl⟩
  · show vs M (borrowK ((sigIn C).bn + 2) (kc q3.k).n C.p.logN q5).1 = _
    rw [hmbv, selectorPoint_bits, hlogN]

/-- The `KS` link's bounds at S2GF (stated at `cfgF20.p`, as `front_phasesG` reads them). -/
theorem blk_cfgF20 : spongeBlocks cfgF20.p - 1 < 2 ^ cfgF20.p.ksLog := by
  rw [show cfgF20.p = P20F from rfl, spongeBlocks_P20F.1]; decide

theorem ksp_cfgF20 : ksSplit cfgF20.p + 399 + 31 < 2 ^ cfgF20.p.ksLog := by
  rw [show cfgF20.p = P20F from rfl, ksSplit_P20F]; decide

set_option maxRecDepth 100000 in
/-- **The front's phases at `P20F`** (`front_phasesG` at `cfgF20`; roll 11's `p47_at` for `frontF cfgF20`): from the front's rows and assertions
(gate on), the proof-of-work answers (`powFront`), the row switches' words (the two `rowAux` blocks), `n'`'s bits and
range and the bits of `s'`, V's tape (with the wiring), `KS` and `KS` link phases run from their starts to the next
phase's start. -/
theorem front_phasesF {sig : ByteArray} {q : Ptr} (hS : Lvm.Q1.Streamed M sig (streamLanes P20F))
    (hTo : posOf P20F (phaseItem0 P20F .openMain) + 48 ≤ 8 * streamLanes P20F)
    (hg : M.k (pbB cfgF20) = 1) (hpow : Lvm.Q1.PowOkV (feAt sig) (powFront P20F))
    (hrw : ∀ j < 128, M.k (tBw cfgF20 + j) = rowWordD (Lvm.Q2.slicesOf M (wireSlices P20F)) j)
    (hrk : ∀ j < 128, M.k (tBk cfgF20 + j) = rowWordD (Lvm.Q2.slicesOf M (ksSlices P20F)) j)
    (pub : Pub) (hnb : ∀ j < 20, (kc ((sigIn cfgF20).bn + 2 + j)).val M = bitE pub.n j)
    (hn : 1 ≤ pub.n ∧ pub.n ≤ 2 ^ 20) (hsb : ∀ i < 256, M.k (bsB cfgF20 + i) = if sBitsD pub.s i then 1 else 0)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) (zc : Cell) (b : Bool)
    (hsm : b = true → pub.n ≤ 2 ^ 18) (h : Lvm.QSig.Ok c M (frontF cfgF20) q) :
    ∃ tp co lo,
      Lvm.Har.PhaseAt (tapeD P20F.logN (dSelBits P20F) (dSel P20F) pub.s pub.n) sig
        (posOf P20F (phaseItem0 P20F .tape)) (posOf P20F (phaseItem0 P20F .ks)) tp ∧
      Lvm.Har.PhaseAt (callerD P20F.ksLog) sig (posOf P20F (phaseItem0 P20F .ks))
        (posOf P20F (phaseItem0 P20F .ksLink)) co ∧
      Lvm.Har.PhaseAt (ksLinkD P20F.ksLog (ksXLog P20F) E2V.contRowsF) sig (posOf P20F (phaseItem0 P20F .ksLink))
        (posOf P20F (phaseItem0 P20F .openMain)) lo ∧
      List.Forall₂ (Lvm.Q2.FRelZ M zc b) (frontF cfgF20 q).1.cs (frontClaimsD P20F pub tp co lo) ∧
      vs M (frontF cfgF20 q).1.mb = selectorPoint (pub.n - 1) 20 := by
  rw [contRowsF_eq]
  exact front_phasesG (C := cfgF20) stE2_P20F alignF regs_P20F dsel_P20F
    blk_cfgF20 ksp_cfgF20 hS hTo hg hpow hrw hrk pub hnb hn hsb hh zc b
    hsm h

end Lvm.E2Q
