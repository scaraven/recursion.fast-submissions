-- New for lvm2 MP-B cap pruning (CAP-C2, 2026-11-17): Q_arith's opening at S2GB is V's (`open_phaseB`, `dOpenFB`),
-- and `decideProgSB` from its phases (`core_of_phasesB`, `decideFSB_of`): the S2GB twins of `LvmE2QOpenPhase`'s and
-- `LvmS2GSHar`'s opening and decision lemmas.
import LvmS2GBHarW
import LvmS2GSHar

/-!
# Q_arith's opening and V's decision at S2GB

* **`dOpenFB p`**: `dOpenF` with `verifyStackedOpeningB p` (the S2GB stream); `dOpenFFLB_eq`: L's `dOpenFFLB` is it.
* **`openGF_zon_runB`**, **`open_phaseB`**: `openGFB … (some p)` replays V's `dOpenFB p` (`stackG_runB`).
* **`core_of_phasesB`**, **`decideFSB_of`**: `decideProgSB` / `decideFSB` from the pin, the typed phases, the tape
  and the opening.
-/

set_option autoImplicit false

namespace Lvm

open DM Lvm.E2V

/-- **`dOpenF` on the S2GB stream** (`verifyStackedOpeningB p`). -/
def dOpenFB (p : Params) (s : Bool) (pin : BlockClaim) (claims : List (Com × BlockClaim × FE)) : DM Unit := do
  require (claims.all (·.1 == .main))
  let cm := (claims.filter (·.1 == .main)).map (·.2)
  verifyStackedOpeningB p p.mainLevels p.nuMain
    ((pin.weight, pin.value) :: if s then cm.map fun e => TypedV.onStackZBN p.nuMain e.1 e.2 else cm.map (·.1.onStack))
    false p.grind p.mainOod

end Lvm

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Lvm.Shape Lvm.E2V

variable {c : Ctx} {M : Mem}

set_option maxHeartbeats 1000000 in
/-- **`openGF_zon_run` on the S2GB stream**: `openGFB` replays `verifyStackedOpeningB` on V's stack claims of the
shape `b` (`σ` holds `b`): the pin's claim on the physical stack first, then `scOf b` of V's claims. -/
theorem openGF_zon_runB (Cm : SCfg) (pp : Params) (hν : Cm.nu = CMain.nu20) {F : FCtx} (hF : FCtxOk M F) (pin : CClaim)
    (hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (pinPt pin)) (hl : (pinPt pin).length = CMain.nu20) (cs : List FClaim)
    (cls : List (Com × BlockClaim × FE)) (b : Bool) (hrel : List.Forall₂ (FRelZ M F.z b) cs cls) (mb : List Cell)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) = if b then 1 else 0)
    (sK g : Cell) (hsK : sK.val M = if b then 1 else 0) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T)
    (hok : LayOkB Cm (some pp) T = true) (hg : g.val M = 1) (hgK : g.ty = .K) (hpos : PosOkB Cm (some pp) M sig 0 Cm.levels (Cm.U + 15))
    (hpw : PwOk Cm M 0 Cm.levels) {p : Ptr} (hp : 1 ≤ p.e) (h : Lvm.QSig.Ok c M (openGFB Cm (some pp) true F pin cs mb sK g) p)
    (s : RS) (hs : pos s = 8 * Cm.U) :
    let scs := ((pin.val M).2.weight, (pin.val M).2.value) :: cls.map (scOf b)
    (verifyStackedOpeningB pp Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpeningB pp Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2 =
      8 * stackEndL Cm.g Cm.ood Cm.levels (Cm.U + 15) (some pp) ∧
    (verifyStackedOpeningB pp Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2.msg = 0 := by
  intro scs
  simp only [openGFB, if_true] at h
  have hlen : scs.length = cs.length + 1 := by simp [scs, hrel.length_eq]
  refine stackG_runB Cm pp (cs.length + 1) _ _ _
    (fun w => (w.1.val M = if b then 1 else 0) ∧ List.Forall₂ (SRel M w.1) w.2 scs) scs hlen ?_ ?_ ?_
    F.z F.o g hS hok hF.z hF.o hF.zE hF.oE hg hgK hpos hpw hp h s hs
  · refine hs_bind (sigmaG_spec hF.z) fun σ hσv => ?_
    have hσb : σ.val M = if b then 1 else 0 := hσv.trans hσ
    exact hs_bind (pinZG_spec hσb pin hpt hl) fun pz hpz =>
      hs_bind (prepZs_spec hF hσb hsK cs cls hrel) fun ps hps => hs_pure ⟨hσb, .cons hpz (List.forall₂_map_right_iff.mpr hps)⟩
  · intro w ⟨_, hrel'⟩ sp σ hsp p' h'
    have hl' : (w.2.map fun e => (⟨.main, .point ⟨0, 0⟩ [], e.2⟩ : CClaim)).length = cs.length + 1 := by
      simp [hrel'.length_eq, hlen]
    rw [targetG_spec h' hF.z σ (fun i hi => hsp i (by rw [← hl']; exact hi)), hl', List.map_map]
    congr 1
    rw [← srel_values hrel']
    refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp_apply]
    exact cval_value _
  · intro w ⟨hsv, hrel'⟩ sp xb σ hsp
    have hl : w.2.length = cs.length + 1 := by rw [hrel'.length_eq, hlen]
    have hX : ((List.range Cm.nu).map fun i => M.e (xb + i)).length = CMain.nu20 := by simp [hν]
    refine hs_bind (muxPtG_spec w.1 xb (List.range CMain.nu20)) fun ms ⟨hml, hmE, hmv⟩ => ?_
    have hcp : Hs c M (copiesG ms) (fun xs => ∀ i < CMain.nu20, M.e (xs + i) = (ms.getD i default).val M) :=
      fun p' h' => by
        obtain ⟨e1, e2⟩ := copiesG_spec hmE h'
        rw [e1]; exact fun i hi => e2 i (by rw [hml]; simpa using hi)
    refine hs_bind hcp fun xs hxs => hs_mono (basisZF_spec hF (srel_ok hrel') σ
      (fun j hj => hsp j (by rw [← hl]; simpa using hj))) fun bv hbv => ?_
    rw [hbv]
    set X := (List.range Cm.nu).map fun i => M.e (xb + i) with hXd
    have hXl : X.length = CMain.nu20 := hX
    have hXg : ∀ i < CMain.nu20, X.getD i 0 = M.e (xb + i) := fun i hi => by
      simp [hXd, List.getD_eq_getElem?_getD, List.getElem?_map, hν, hi]
    have hxs' : xsOf M CMain.nu20 xs = if b then rotZ X else X := by
      refine list_ext_getD _ _ (by cases b <;> simp [xs_length, hXl, rotZ_length X hXl]) fun i hi => ?_
      rw [xs_length] at hi
      have hm := hmv i (by simpa using hi)
      have hrN : (List.range CMain.nu20).getD i 0 = i := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]
      rw [hrN] at hm
      rw [xs_getD hi, hxs i hi, hm, hsv]
      cases b
      · simp only [Bool.false_eq_true, if_false, mux_zero]; rw [hXg i hi]
      · simp only [if_true, mux_one]; rw [rotZ_getD X hXl hi, hXg _ (Nat.mod_lt _ (by decide))]
    have hsl : (scs.map fun sc => sc.1 X).length = w.2.length := by rw [List.length_map, hlen, hl]
    rw [← hl, ← hsl, dot_powers_bsum, hsv, hxs', List.map_map, List.map_map]
    cases b
    · simp only [Bool.false_eq_true, if_false, mux_zero]
      exact congrArg _ (srel_big (by rw [hsv]; rfl) X hXl hrel')
    · simp only [if_true, mux_one]
      exact congrArg _ (srel_small (by rw [hsv]; rfl) X hXl hrel')

/-! ## The phase -/

set_option maxHeartbeats 1000000 in
/-- **`open_phase` on the S2GB stream**: the opening is V's `dOpenFB p b` (`hopen` of `core_of_phasesF`, with `b = smallT p pub`): from the
opening's start with `ok`, V keeps `ok`, reads `Σ` to its end and leaves no message pending; `σ` (the bits `mb` of
`n' − 1`) and `sK` hold the shape `b`, the pin is V's pin claim, the other claims stand for V's (`FRelZ`). -/
theorem open_phaseB (p : Params) (Cm : SCfg) (hlv : Cm.levels = p.mainLevels) (hnu : Cm.nu = p.nuMain)
    (hgr : Cm.g = p.grind) (hood : Cm.ood = p.mainOod) (hzon : (p.logN == 20 && p.nuMain == CMain.nu20) = true)
    {F : FCtx} (hF : FCtxOk M F) (pin : CClaim) (hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (pinPt pin)) (z : List FE)
    (a : FE) (hpin : FRel M CMain.nu20 (.e3 pin) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a)) (cs : List FClaim)
    (cls : List (Com × BlockClaim × FE)) (b : Bool) (hrel : List.Forall₂ (FRelZ M F.z b) cs cls) (mb : List Cell)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) = if b then 1 else 0)
    (sK g : Cell) (hsK : sK.val M = if b then 1 else 0) {sig : ByteArray} {T : Nat}
    (hS : Lvm.Q1.Streamed M sig T) (hok : LayOkB Cm (some p) T = true) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOkB Cm (some p) M sig 0 Cm.levels (Cm.U + 15)) (hpw : PwOk Cm M 0 Cm.levels)
    (hend : 8 * stackEndL Cm.g Cm.ood Cm.levels (Cm.U + 15) (some p) = sig.size) {q : Ptr} (hq : 1 ≤ q.e)
    (h : Lvm.QSig.Ok c M (openGFB Cm (some p) (p.logN == 20 && p.nuMain == CMain.nu20) F pin cs mb sK g) q) :
    ∀ s : RS, pos s = 8 * Cm.U → s.ok = true →
      (dOpenFB p b (BlockClaim.point ⟨p.nuMain, 0⟩ z a) cls sig s).2.ok = true ∧
      (dOpenFB p b (BlockClaim.point ⟨p.nuMain, 0⟩ z a) cls sig s).2.ent = sig.size ∧
      (dOpenFB p b (BlockClaim.point ⟨p.nuMain, 0⟩ z a) cls sig s).2.msg = 0 := by
  intro s hs hsok
  have hz' : p.logN = 20 ∧ p.nuMain = CMain.nu20 := by simpa using hzon
  rw [hzon] at h
  have hν : Cm.nu = CMain.nu20 := hnu.trans hz'.2
  obtain ⟨hwf, hpB⟩ := hpin
  have hl : (pinPt pin).length = CMain.nu20 := by
    have := hwf
    rw [WF1, hpt] at this
    simpa using this
  have hall : cls.all (·.1 == .main) = true := (relT_main (hrel.imp fun _ _ hr => hr.1)).1
  have hfilt : cls.filter (·.1 == .main) = cls := List.filter_eq_self.mpr fun cl hcl => by
    simpa using (List.all_eq_true.mp hall) cl hcl
  have hrq : ({ s with ok := true && s.ok } : RS) = s := by cases s; rfl
  have e : dOpenFB p b (BlockClaim.point ⟨p.nuMain, 0⟩ z a) cls sig s =
      verifyStackedOpeningB p Cm.levels Cm.nu (((pin.val M).2.weight, (pin.val M).2.value) :: cls.map (scOf b)) false
        Cm.g Cm.ood sig s := by
    unfold dOpenFB
    rw [dm_bind, require_runW, hall, hrq, hlv, hnu, hgr, hood, hfilt, hz'.2, ← hpB]
    cases b
    · simp only [Bool.false_eq_true, if_false, List.map_map]
      rfl
    · simp only [if_true, List.map_map]
      rfl
  rw [e]
  obtain ⟨o1, o2, o3⟩ := openGF_zon_runB Cm p hν hF pin hpt hl cs cls b hrel mb hσ sK g hsK hS hok hg hgK hpos hpw hq h
    s hs
  refine ⟨o1.trans hsok, ?_, o3⟩
  simp only [pos] at o2
  omega

end Lvm.Q2

namespace Lvm.Har

open Lvm DM Lvm.E2T Lvm.E2U

/-- **`dOpenFFLB` is `dOpenFB`** on the typed items' claims, the three claims, the front's claims. -/
theorem dOpenFFLB_eq (p : Params) (s : Bool) (pin : BlockClaim) (ti : List FItem) (ζ : List FE)
    (css : List (List (FE × Nat × Nat))) (vs : List FE) (items : List FItem) :
    Lvm.E2L.dOpenFFLB p s pin ti ζ css vs items =
      dOpenFB p s pin (ti.flatMap FItem.flat ++ Lvm.E2L.linClaims p.nuMain ζ css vs ++ items.flatMap FItem.flat) := by
  have hm := linClaims_main p.nuMain ζ css vs
  have hall : (Lvm.E2L.linClaims p.nuMain ζ css vs).all (·.1 == .main) = true :=
    List.all_eq_true.mpr fun e he => by rw [hm e he]; rfl
  have hfl : (Lvm.E2L.linClaims p.nuMain ζ css vs).filter (·.1 == .main) = Lvm.E2L.linClaims p.nuMain ζ css vs :=
    List.filter_eq_self.mpr fun e he => by rw [hm e he]; rfl
  unfold Lvm.E2L.dOpenFFLB dOpenFB
  rw [verifyStackedOpeningGB_eq]
  simp only [List.flatMap_cons, List.flatMap_append, groups_flat, List.all_append, hall, Bool.and_true,
    List.filter_append, hfl, List.map_append]
  cases s <;> simp only [SGroup.one, Lvm.E2L.linGroup, toStk, List.map_map, Function.comp_def, Bool.false_eq_true,
    ↓reduceIte, List.singleton_append, List.append_assoc]

private theorem bind_runB {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := (bind_run' m f sig s).trans rfl
private theorem pure_runB {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) :=
  (pure_run' a sig s).trans rfl
private theorem skip_runB (n : Nat) (sig : ByteArray) (s : RS) :
    skip n sig s = ((), { s with msg := s.msg + n }) := (skip_run' n sig s).trans rfl
private theorem read_runB (sig : ByteArray) (s : RS) : (read : DM ByteArray) sig s = (sig, s) :=
  (read_run' sig s).trans rfl
private theorem stRunB {α : Type} (x : StateM RS α) (s : RS) : x.run s = x s := (rfl : x.run s = x s).trans rfl

/-- **`decideProgSB` from its phases** (`core_of_phasesS`'s twin at S2GB: the sent cap `2^capSendBits`, the intervals `iv`; the typed phases
end at the bus's point and decomposition; the opening is `dOpenFB` on the typed claims, the three claims and the front's). -/
theorem core_of_phasesB (p pT : Params) (iv : List (ℕ × ℕ)) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray)
    {Pb P1 P2 P3 : Nat} {pin : BlockClaim} {acc : Acc} {ti : List FItem} {ζ : List FE} {bus : BusOut}
    {tp : TapeU RowZ}
    (hb : pos (RS.startH (headerBytesP p)) + nodeBytes * 2 ^ p.capSendBits 0 (p.level ⟨.main, 0⟩).cap = Pb)
    (hpin : PhaseAt (pinD p.nuMain) sig Pb P1 pin)
    (htyped : PhaseAt (Lvm.E2L.dTypedLG pT N (m3G N p) (Lvm.pubOfWS vk c sig) (typedItemsND N p)) sig P1 P2
      (acc, ti, ζ, bus))
    (htape : PhaseAt (Lvm.E2L.tapeUDGc iv rowSwitchDR p (Lvm.pubOfWS vk c sig).s
      (Lvm.pubOfWS vk c sig).n) sig P2 P3 tp)
    (hopen : ∀ s : RS, pos s = P3 → s.ok = true →
      let o := dOpenFB p (TypedV.smallT p (Lvm.pubOfWS vk c sig)) pin
        (ti.flatMap FItem.flat ++ Lvm.E2L.linClaims p.nuMain ζ
            ((List.range 3).map (M3.mbColsN (M3.sumcheckTabs N.mbT) bus))
            ((List.range 3).map (M3.mbValueN (M3.sumcheckTabs N.mbT) bus ζ)) ++
          (frontItemsU rowAccR p (Lvm.pubOfWS vk c sig) tp).flatMap FItem.flat) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    ∃ s₉ : RS, Lvm.E2S.decideProgSB p pT iv N vk c sig (RS.startH (headerBytesP p)) = (acc, s₉) ∧ s₉.ok = true ∧
      s₉.ent = sig.size ∧ s₉.msg = 0 := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : RS, RS.startH (headerBytesP p) = s₀ := ⟨_, rfl⟩
  have h₀ : s₀.ok = true := by rw [← hs₀]; rfl
  rw [hs₀] at hb ⊢
  obtain ⟨s1, hs1⟩ : ∃ s1 : RS, s1 = { s₀ with msg := s₀.msg + nodeBytes * 2 ^ p.capSendBits 0 (p.level ⟨.main, 0⟩).cap } :=
    ⟨_, rfl⟩
  have e1 : pos s1 = Pb := by rw [← hb, hs1]; simp only [pos]; omega
  obtain ⟨a1, a2, a3⟩ := hpin s1 e1 (by rw [hs1]; exact h₀)
  generalize hA : pinD p.nuMain sig s1 = AA at a1 a2 a3
  obtain ⟨av, s2⟩ := AA
  simp only at a1 a2 a3
  rw [a1] at hA
  obtain ⟨b1, b2, b3⟩ := htyped s2 a3 a2
  generalize hB : Lvm.E2L.dTypedLG pT N (m3G N p) (Lvm.pubOfWS vk c sig) (typedItemsND N p) sig s2 = BB at b1 b2 b3
  obtain ⟨bv, s3⟩ := BB
  simp only at b1 b2 b3
  rw [b1] at hB
  obtain ⟨c1, c2, c3⟩ := htape s3 b3 b2
  generalize hC : Lvm.E2L.tapeUDGc iv rowSwitchDR p (Lvm.pubOfWS vk c sig).s (Lvm.pubOfWS vk c
      sig).n sig s3 = CC
    at c1 c2 c3
  obtain ⟨cv, s4⟩ := CC
  simp only at c1 c2 c3
  rw [c1] at hC
  obtain ⟨o1, o2, o3⟩ := hopen s4 c3 c2
  rw [← dOpenFFLB_eq] at o1 o2 o3
  generalize hO : Lvm.E2L.dOpenFFLB p (TypedV.smallT p (Lvm.pubOfWS vk c sig)) pin ti ζ
    ((List.range 3).map (M3.mbColsN (M3.sumcheckTabs N.mbT) bus))
    ((List.range 3).map (M3.mbValueN (M3.sumcheckTabs N.mbT) bus ζ))
    (frontItemsU rowAccR p (Lvm.pubOfWS vk c sig) tp) sig s4 = OO at o1 o2 o3
  obtain ⟨ov, s5⟩ := OO
  simp only at o1 o2 o3
  refine ⟨s5, ?_, o1, o2, o3⟩
  unfold Lvm.E2S.decideProgSB
  simp only [bind_runB, read_runB, skip_runB, pure_runB]
  rw [← hs1, hA]
  simp only
  rw [hB]
  simp only
  rw [hC]
  simp only
  rw [Lvm.M3.mbValsF_eq, hO]

/-- **`decideFSB` accepts** when its run ends accepting with the accumulator `acc` and `Φ_Q` at `E2` holds at it. -/
theorem decideFSB_of (p pT : Params) (iv : List (ℕ × ℕ)) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) {acc : Acc}
    (hrun : ∃ s₉ : RS, Lvm.E2S.decideProgSB p pT iv N vk c sig (RS.startH (headerBytesP p)) = (acc, s₉) ∧
      s₉.ok = true ∧ s₉.ent = sig.size ∧ s₉.msg = 0)
    (hphi : N.phiT (acc.pt.map Lvm.e2OfFE) = Lvm.e2OfFE acc.y) :
    Lvm.E2S.decideFSB p pT iv N vk c sig = true := by
  obtain ⟨s₉, h1, h2, h3, h4⟩ := hrun
  have eD : @Lvm.E2S.decideFSB = @Lvm.E2S.decideFSB := rfl
  conv at eD => rhs; delta Lvm.E2S.decideFSB
  rw [eD]
  beta_reduce
  rw [DM.runOnH, stRunB, h1]
  simp only [h2, h3, h4, hphi, beq_self_eq_true, Bool.and_self]

end Lvm.Har
