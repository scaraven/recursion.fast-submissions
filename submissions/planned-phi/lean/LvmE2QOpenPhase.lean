-- New for lvm2 E2-FT (E2F-C5): the opening phase at S2GF (`harithF20`'s `hopen` of `core_of_phasesF`): `C_main`'s
-- opening `openGF` with the gate on both shapes (`zon`, always on at `P20F`) replays V's `dOpenF p b` for either shape
-- `b` of the child (roll 11's `openT_atG` / `stackZ_run` with the `E2` claim forms of `LvmE2QPinOpen`).
import LvmE2QOpenPhaseP

/-!
# The opening phase at S2GF (`open_phase`)

* **`FSmall M zc b fc t`**: the small shape's side of a circuit claim `fc` whose V claim has tail `t`: an `E3` claim
  in `zClaimG`'s static form (`ZWF`) with tail `tailC`; a word half or row claim on regular blocks with tail `0`; a
  `D` word half at `r ‖ sel(l)` with tail coordinate `h` of `tailDE2 r l` (`frontClaimsD`'s); the tape's row claim
  with block bit `0` and tail `rowTailE2`.
* **`FRelZ M zc b fc cl`**: `FRelT` (what `fc` stands for in V's list on `C_main`) and `FSmall`.
* **`open_phase`**: from the opening's start with `ok`, `dOpenF p b` on the pin and V's claims keeps `ok`, reads `Σ`
  to its end and leaves no message pending, for the shape `b` that the shape cell `σ` holds.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Lvm.Shape Lvm.E2V

variable {c : Ctx} {M : Mem}

/-! ## The terms of the prepared claims, both shapes -/

/-- **The terms of one prepared claim** (`ν = 23`): pairs and plain terms summing to `sc·pfWB` with the big keys
and `sc·pfWS` with the moved keys. -/
theorem pfTermsZ1_spec {F : FCtx} (hF : FCtxOk M F) {xb : ℕ} (sc : Cell) {pf : PF} (hok : PFOk pf) (memo : Memo)
    (m6 : Memo6) (hm : MemoOk M (fun i => M.e (xb + i)) memo) (hm6 : Memo6Ok M xb m6) :
    Hs c M (pfTerms F CMain.nu20 xb sc pf memo m6) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
      Memo6Ok M xb r.2.1 ∧
      (r.2.2.1.map fun t => tval M (fun i => M.e (xb + i)) CMain.nu20 t.big).sum +
        (r.2.2.2.map (tval M (fun i => M.e (xb + i)) CMain.nu20)).sum = sc.val M * pfWB M pf (xsOf M CMain.nu20 xb) ∧
      (r.2.2.1.map fun t => tval M (fun i => M.e (xb + i)) CMain.nu20 t.sml).sum +
        (r.2.2.2.map (tval M (fun i => M.e (xb + i)) CMain.nu20)).sum = sc.val M * pfWS M pf (xsOf M CMain.nu20 xb) ∧
      ∀ t ∈ r.2.2.1, t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20) := by
  have hX : (xsOf M CMain.nu20 xb).length = CMain.nu20 := xs_length _ _
  cases pf with
  | e3 cc reg =>
    obtain ⟨hwf, hreg⟩ := hok
    cases reg
    · show Hs c M (oneClaim CMain.nu20 xb F.z F.o sc cc memo >>= fun r => pure (r.1, m6, [], r.2)) _
      exact hs_bind (oneClaim_spec hF.z hF.o hF.zE hwf hm) fun r ⟨hm', hv⟩ =>
        hs_pure ⟨hm', hm6, by simp [hv, pfWB], by simp [hv, pfWS], by simp⟩
    · show Hs c M (regPairs xb F.z F.o sc cc memo >>= fun r => pure (r.1, m6, r.2, [])) _
      exact hs_bind (regPairs_spec hF.z hF.o hF.zE hwf (hreg rfl) hm) fun r ⟨hm', hb, hs, hl⟩ =>
        hs_pure ⟨hm', hm6, by simp [hb, pfWB], by simp [hs, pfWS], hl⟩
  | half h parts reg =>
    cases reg
    · show Hs c M (halfTerms F CMain.nu20 xb sc h false parts m6 >>= fun r => pure (memo, r.1, r.2.1, r.2.2)) _
      refine hs_bind (halfTermsB_spec hF sc h parts m6 (fun e he => by
        obtain ⟨a1, a2, a3, a4⟩ := hok e he; exact ⟨a1, a2, a3, by simpa using a4⟩) hm6)
        fun r ⟨hm6', hn, hs⟩ => hs_pure ⟨hm, hm6', ?_, ?_, by simp [hn]⟩
      all_goals
        simp only [hn, List.map_nil, List.sum_nil, zero_add, hs, pfWB, pfWS, Bool.false_eq_true, if_false]
        congr 1
        refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
        rw [c6_part]
        rfl
    · show Hs c M (halfTerms F CMain.nu20 xb sc h true parts m6 >>= fun r => pure (memo, r.1, r.2.1, r.2.2)) _
      refine hs_bind (halfTermsZ_spec hF sc h parts m6 (fun e he => by
        obtain ⟨a1, a2, a3, a4⟩ := hok e he; exact ⟨a1, a2, a3, by simpa using a4⟩) hm6)
        fun r ⟨hm6', hn, hb, hs, hl⟩ => hs_pure ⟨hm, hm6', ?_, ?_, hl⟩
      · rw [hn, List.map_nil, List.sum_nil, add_zero, hb]; rfl
      · rw [hn, List.map_nil, List.sum_nil, add_zero, hs]; rfl
  | row blk z κ nu reg =>
    obtain ⟨hne, hzK, hκK, hzl, hvc, hreg⟩ := hok
    have hlf : ∀ lf : Cell, lf.val M = rowLV M nu z κ ((List.range z.length).map fun l => M.e (xb + l)) →
        lf.val M = rowLV M nu z κ ((xsOf M CMain.nu20 xb).take blk.variableCount) := fun lf h => by
      rw [h, xs_take _ _ _ hvc, hzl]
    have hE : kprod (fun i => M.e (xb + i)) CMain.nu20 (keyOf (selbit blk) CMain.nu20 blk.variableCount) =
        blk.eqAbove (xsOf M CMain.nu20 xb) := by
      rw [kprod_keyOf, eqAbove_prod blk _ (fun i => M.e (xb + i)) (by rw [hX]; exact hvc)
        (fun i hi => xs_getD (by rwa [hX] at hi)), hX]
    cases reg
    · show Hs c M (rowLeafGL nu z κ xb F.z F.zk >>= fun lf =>
        pure (memo, m6, ([] : List ZT), [(⟨sc, keyOf (selbit blk) CMain.nu20 blk.variableCount, lf⟩ : TC)])) _
      refine hs_bind (rowLeafGL_val nu z κ xb hF.z hF.zk hne hzK hκK) fun lf hv => hs_pure ⟨hm, hm6, ?_, ?_, by simp⟩
      all_goals
        simp only [List.map_nil, List.sum_nil, zero_add, List.map_cons, List.sum_cons, add_zero, tval, pfWB, pfWS,
          Bool.false_eq_true, if_false]
        rw [hE, hlf lf hv]
        ring
    · show Hs c M (rowLeafGL nu z κ xb F.z F.zk >>= fun lf => pure (memo, m6, [(⟨sc, lf, topK (selbit blk),
        topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩ : ZT)], ([] : List TC))) _
      refine hs_bind (rowLeafGL_val nu z κ xb hF.z hF.zk hne hzK hκK) fun lf hv => ?_
      obtain ⟨pb, ps, l1, l2⟩ := pairT_spec (M := M) xb (hreg rfl) sc lf
      refine hs_pure ⟨hm, hm6, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [show (⟨sc, lf, topK (selbit blk), topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩ :
          ZT).big = (pairOf sc lf blk).big from rfl, pb, hlf lf hv]
        simp only [pfWB]
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [show (⟨sc, lf, topK (selbit blk), topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩ :
          ZT).sml = (pairOf sc lf blk).sml from rfl, ps, hlf lf hv]
        simp only [pfWS, ite_true]
      · intro t ht
        rcases List.mem_singleton.mp ht with rfl
        exact ⟨l1, l2⟩

/-- **The terms of the prepared claims** from index `i` (scale cells `sp + i`, holding `σ^i`). -/
theorem pfTermsAllZ_spec {F : FCtx} (hF : FCtxOk M F) {xb sp N : ℕ} {σ : FE} (hs : ∀ j < N, M.e (sp + j) = σ ^ j) :
    ∀ (pfs : List PF) (i : ℕ) (memo : Memo) (m6 : Memo6), (∀ pf ∈ pfs, PFOk pf) →
      MemoOk M (fun i => M.e (xb + i)) memo → Memo6Ok M xb m6 → i + pfs.length ≤ N →
      Hs c M (pfTermsAll F CMain.nu20 xb sp i pfs memo m6) (fun r =>
        (r.1.map fun t => tval M (fun i => M.e (xb + i)) CMain.nu20 t.big).sum +
          (r.2.map (tval M (fun i => M.e (xb + i)) CMain.nu20)).sum =
            bsum σ i (pfs.map fun pf => pfWB M pf (xsOf M CMain.nu20 xb)) ∧
        (r.1.map fun t => tval M (fun i => M.e (xb + i)) CMain.nu20 t.sml).sum +
          (r.2.map (tval M (fun i => M.e (xb + i)) CMain.nu20)).sum =
            bsum σ i (pfs.map fun pf => pfWS M pf (xsOf M CMain.nu20 xb)) ∧
        ∀ t ∈ r.1, t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20)
  | [], _, _, _, _, _, _, _ => hs_pure ⟨by simp [bsum], by simp [bsum], by simp⟩
  | pf :: pfs, i, memo, m6, hok, hm, hm6, hN => by
    simp only [List.length_cons] at hN
    show Hs c M (pfTerms F CMain.nu20 xb (ec (sp + i)) pf memo m6 >>= fun r =>
      pfTermsAll F CMain.nu20 xb sp (i + 1) pfs r.1 r.2.1 >>= fun rs =>
        pure (r.2.2.1 ++ rs.1, r.2.2.2 ++ rs.2)) _
    refine hs_bind (pfTermsZ1_spec hF (ec (sp + i)) (hok pf (List.mem_cons_self ..)) memo m6 hm hm6)
      fun r ⟨hm', hm6', hb, hsm, hl⟩ => hs_bind (pfTermsAllZ_spec hF hs pfs (i + 1) r.1 r.2.1
        (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hm' hm6' (by omega)) fun rs ⟨hb', hsm', hl'⟩ =>
      hs_pure ⟨?_, ?_, ?_⟩
    · have hb2 := hb
      rw [Cell.val_E, hs i (by omega)] at hb2
      rw [List.map_append, List.sum_append, List.map_append, List.sum_append, List.map_cons, bsum, ← hb', ← hb2]
      ring
    · have hs2 := hsm
      rw [Cell.val_E, hs i (by omega)] at hs2
      rw [List.map_append, List.sum_append, List.map_append, List.sum_append, List.map_cons, bsum, ← hsm', ← hs2]
      ring
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hl t ht
      · exact hl' t ht

/-! ## The basis in both shapes -/

/-- **The batched weight of the prepared claims, both shapes**: the mux of `Σ_i σ^i pfWB_i` and `Σ_i σ^i pfWS_i`
at the point in the `E` cells `xb + i`. -/
theorem basisZF_spec {F : FCtx} (hF : FCtxOk M F) {pfs : List PF} {sp xb : ℕ} {s : Cell}
    (hok : ∀ pf ∈ pfs, PFOk pf) (σ : FE) (hs : ∀ j < pfs.length, M.e (sp + j) = σ ^ j) :
    Hs c M (basisZF F pfs sp xb s) (fun r => r.val M = mux (s.val M)
      (bsum σ 0 (pfs.map fun pf => pfWB M pf (xsOf M CMain.nu20 xb)))
      (bsum σ 0 (pfs.map fun pf => pfWS M pf (xsOf M CMain.nu20 xb)))) := by
  unfold basisZF
  refine hs_bind (pfTermsAllZ_spec (N := pfs.length) hF hs pfs 0 [] [] hok (fun _ h => by simp at h)
    (fun _ h => by simp at h) (by omega)) fun r ⟨hb, hsm, hl⟩ => ?_
  set X : ℕ → FE := fun i => M.e (xb + i)
  refine hs_bind (hs_and (lowsG_spec hF.z r.1 (fun k => kprod X CMain.nu20 k.1) _)
    (lowsG_spec hF.z r.1 (fun k => kprod X CMain.nu20 k.2) _)) fun lows ⟨hl1, hl2⟩ =>
    hs_bind (trieG_spec hF.z CMain.nu20 _) fun tb htb => hs_bind (trieG_spec hF.z CMain.nu20 _) fun ts hts =>
      hs_mono (muxG_spec _ _ _) fun w hw => ?_
  have t1 : ((lows.map fun e => (⟨F.o, e.1.1, e.2⟩ : TC)).map (tval M X CMain.nu20)).sum =
      (r.1.map fun t => tval M X CMain.nu20 t.big).sum := by
    rw [List.map_map]
    have : (lows.map ((tval M X CMain.nu20) ∘ fun e => (⟨F.o, e.1.1, e.2⟩ : TC))) =
        lows.map fun e => kprod X CMain.nu20 e.1.1 * e.2.val M :=
      List.map_congr_left fun e _ => by simp only [Function.comp_apply, tval, hF.o, one_mul]
    rw [this, hl1, top_val X r.1 ZT.pb Prod.fst (fun t ht => (hl t ht).1) fun _ => rfl]
    rfl
  have t2 : ((lows.map fun e => (⟨F.o, e.1.2, e.2⟩ : TC)).map (tval M X CMain.nu20)).sum =
      (r.1.map fun t => tval M X CMain.nu20 t.sml).sum := by
    rw [List.map_map]
    have : (lows.map ((tval M X CMain.nu20) ∘ fun e => (⟨F.o, e.1.2, e.2⟩ : TC))) =
        lows.map fun e => kprod X CMain.nu20 e.1.2 * e.2.val M :=
      List.map_congr_left fun e _ => by simp only [Function.comp_apply, tval, hF.o, one_mul]
    rw [this, hl2, top_val X r.1 ZT.ps Prod.snd (fun t ht => (hl t ht).2) fun _ => rfl]
    rfl
  rw [hw, htb, hts, List.map_append, List.sum_append, List.map_append, List.sum_append, t1, t2, hb, hsm]

/-! ## The opening in both shapes -/

theorem srel_values {s : Cell} : ∀ {ws : List (PF × Cell)} {scs : List StackClaim},
    List.Forall₂ (SRel M s) ws scs → ws.map (fun e => e.2.val M) = scs.map (·.2)
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h hs => by rw [List.map_cons, List.map_cons, h.value, srel_values hs]

theorem srel_big {s : Cell} (h0 : s.val M = 0) (x : List FE) (hx : x.length = CMain.nu20) :
    ∀ {ws : List (PF × Cell)} {scs : List StackClaim}, List.Forall₂ (SRel M s) ws scs →
      ws.map (fun e => pfWB M e.1 x) = scs.map (fun sc => sc.1 x)
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h hs => by rw [List.map_cons, List.map_cons, h.big h0 x hx, srel_big h0 x hx hs]

theorem srel_small {s : Cell} (h1 : s.val M = 1) (x : List FE) (hx : x.length = CMain.nu20) :
    ∀ {ws : List (PF × Cell)} {scs : List StackClaim}, List.Forall₂ (SRel M s) ws scs →
      ws.map (fun e => pfWS M e.1 (rotZ x)) = scs.map (fun sc => sc.1 x)
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h hs => by rw [List.map_cons, List.map_cons, h.small h1 x hx, srel_small h1 x hx hs]

theorem srel_ok {s : Cell} : ∀ {ws : List (PF × Cell)} {scs : List StackClaim},
    List.Forall₂ (SRel M s) ws scs → ∀ pf ∈ ws.map (·.1), PFOk pf
  | [], [], _ => by simp
  | _ :: _, _ :: _, .cons h hs => by
    intro pf hpf
    rcases List.mem_cons.mp hpf with rfl | hpf
    · exact h.ok
    · exact srel_ok hs pf hpf

set_option maxHeartbeats 1000000 in
/-- **`C_main`'s opening at S2GF in both shapes replays V's `verifyStackedOpening`** on V's stack claims of the
shape `b` (`σ` holds `b`): the pin's claim on the physical stack first, then `scOf b` of V's claims. -/
theorem openGF_zon_run (Cm : SCfg) (hν : Cm.nu = CMain.nu20) {F : FCtx} (hF : FCtxOk M F) (pin : CClaim)
    (hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (pinPt pin)) (hl : (pinPt pin).length = CMain.nu20) (cs : List FClaim)
    (cls : List (Com × BlockClaim × FE)) (b : Bool) (hrel : List.Forall₂ (FRelZ M F.z b) cs cls) (mb : List Cell)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) = if b then 1 else 0)
    (sK g : Cell) (hsK : sK.val M = if b then 1 else 0) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T)
    (hok : LayOk Cm T = true) (hg : g.val M = 1) (hgK : g.ty = .K) (hpos : PosOk Cm M sig 0 Cm.levels (Cm.U + 15))
    (hpw : PwOk Cm M 0 Cm.levels) {p : Ptr} (hp : 1 ≤ p.e) (h : Lvm.QSig.Ok c M (openGF Cm true F pin cs mb sK g) p)
    (s : RS) (hs : pos s = 8 * Cm.U) :
    let scs := ((pin.val M).2.weight, (pin.val M).2.value) :: cls.map (scOf b)
    (verifyStackedOpening Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2 =
      8 * stackEndL Cm.g Cm.ood Cm.levels (Cm.U + 15) ∧
    (verifyStackedOpening Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2.msg = 0 := by
  intro scs
  simp only [openGF, if_true] at h
  have hlen : scs.length = cs.length + 1 := by simp [scs, hrel.length_eq]
  refine stackG_run Cm (cs.length + 1) _ _ _
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
/-- **The opening at S2GF is V's `dOpenF p b`** (`hopen` of `core_of_phasesF`, with `b = smallT p pub`): from the
opening's start with `ok`, V keeps `ok`, reads `Σ` to its end and leaves no message pending; `σ` (the bits `mb` of
`n' − 1`) and `sK` hold the shape `b`, the pin is V's pin claim, the other claims stand for V's (`FRelZ`). -/
theorem open_phase (p : Params) (Cm : SCfg) (hlv : Cm.levels = p.mainLevels) (hnu : Cm.nu = p.nuMain)
    (hgr : Cm.g = p.grind) (hood : Cm.ood = p.mainOod) (hzon : (p.logN == 20 && p.nuMain == CMain.nu20) = true)
    {F : FCtx} (hF : FCtxOk M F) (pin : CClaim) (hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (pinPt pin)) (z : List FE)
    (a : FE) (hpin : FRel M CMain.nu20 (.e3 pin) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a)) (cs : List FClaim)
    (cls : List (Com × BlockClaim × FE)) (b : Bool) (hrel : List.Forall₂ (FRelZ M F.z b) cs cls) (mb : List Cell)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) = if b then 1 else 0)
    (sK g : Cell) (hsK : sK.val M = if b then 1 else 0) {sig : ByteArray} {T : Nat}
    (hS : Lvm.Q1.Streamed M sig T) (hok : LayOk Cm T = true) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOk Cm M sig 0 Cm.levels (Cm.U + 15)) (hpw : PwOk Cm M 0 Cm.levels)
    (hend : 8 * stackEndL Cm.g Cm.ood Cm.levels (Cm.U + 15) = sig.size) {q : Ptr} (hq : 1 ≤ q.e)
    (h : Lvm.QSig.Ok c M (openGF Cm (p.logN == 20 && p.nuMain == CMain.nu20) F pin cs mb sK g) q) :
    ∀ s : RS, pos s = 8 * Cm.U → s.ok = true →
      (dOpenF p b (BlockClaim.point ⟨p.nuMain, 0⟩ z a) cls sig s).2.ok = true ∧
      (dOpenF p b (BlockClaim.point ⟨p.nuMain, 0⟩ z a) cls sig s).2.ent = sig.size ∧
      (dOpenF p b (BlockClaim.point ⟨p.nuMain, 0⟩ z a) cls sig s).2.msg = 0 := by
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
  have e : dOpenF p b (BlockClaim.point ⟨p.nuMain, 0⟩ z a) cls sig s =
      verifyStackedOpening Cm.levels Cm.nu (((pin.val M).2.weight, (pin.val M).2.value) :: cls.map (scOf b)) false
        Cm.g Cm.ood sig s := by
    unfold dOpenF
    rw [dm_bind, require_runW, hall, hrq, hlv, hnu, hgr, hood, hfilt, hz'.2, ← hpB]
    cases b
    · simp only [Bool.false_eq_true, if_false, List.map_map]
      rfl
    · simp only [if_true, List.map_map]
      rfl
  rw [e]
  obtain ⟨o1, o2, o3⟩ := openGF_zon_run Cm hν hF pin hpt hl cs cls b hrel mb hσ sK g hsK hS hok hg hgK hpos hpw hq h
    s hs
  refine ⟨o1.trans hsok, ?_, o3⟩
  simp only [pos] at o2
  omega

end Lvm.Q2
