-- lvm2 E2F-G (import pruning, a pure move out of `LvmQTypedHarS`): roll 11's typed HAR at `P20` (`harithT20`)
-- and its kernel decisions (`harNumT20`, `layOk_9T`, `okE_P20T`, `mini20`, `typedG_replays`, Q_link's glue
-- checks `okA_P20`/`okB_P20`/`okC_P20`). Only roll 11's certificate (`LvmCertM20R`) uses them, so they leave the
-- S2GF certificate's import closure (which keeps `LvmQTypedHarS` for its generic lemmas). Text unchanged.
import LvmQTypedHarS

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

theorem okA_P20 (Q : Nat) : SLok (chGlueA 20 Q) = true := by
  rw [← SLok_shape]
  simp only [chGlueA, List.map_append]
  rw [loadsAt_shape]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

theorem okB_P20 (Q : Nat) (oA sh : LoopOut) :
    SLok (chGlueB (chQB 20 Q) (rhoC oA 20) (rho'C sh 20) (eZC oA 20) (sh.cell 5 (20 - 1))) = true := by
  rw [← SLok_shape]
  simp only [chGlueB, List.map_append]
  rw [loadsAt_shape, dotIns_shape, shiftRecIns_shape]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc, shape_mulI, shape_linI, shape_addI, shape_loc, shape_shape, shape_getD_cellSrc, rhoC, rho'C, eZC, eLC, preP, List.length_map, List.length_range, shape_ins_mk, shape_getD_mapCellSrc, eMus_any]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

theorem okC_P20 (Q : Nat) (gate : Cell) (oA sh sc2 oB : LoopOut) :
    SLok (chGlueC (chQC 20 Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA 20) (eZC oA 20) (rho'C sh 20)
      (oA.cell (2 * 20 + 163) 0) (oB.cell (8 * 20 + 123) 0) (sc2.cell 5 1) gate) = true := by
  rw [← SLok_shape]
  simp only [chGlueC, List.map_append]
  rw [loadsAt_shape, eqTabGo_shape, dotIns_shape, dotIns_shape (n := 78), dotIns_shape (n := 82),
    dotIns_shape (n := 138), mulChainIns_shape]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc, shape_mulI, shape_linI, shape_addI, shape_loc, shape_shape, shape_getD_cellSrc, rhoC, rho'C, eZC, eLC, preP, List.length_map, List.length_range, shape_ins_mk, shape_getD_mapCellSrc, eMus_any]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

-- `okE` at `P20` depends on the sponge-block count literally (`preRecIns` walks its bits): `LvmFinDec.okE_P20`
-- (KS14's block E, `ksBlockE`), re-decided at each re-freeze.

end Lvm.Q1

namespace Lvm.Har

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.NS Lvm.T Lvm.ASM Lvm.QLink
  Lvm.Replay DM
open Lvm.M3 (lay26)
open Lvm.VEq (pubX)
open LeanVM.Protocol (Column)

/-! Proof help (GOLF-DEC3): non-`rfl` copies of the lane definitions, so that `simp` rewrites with proofs (no
definitional unfolding for the kernel to re-check by evaluation), and `harNumT20` reads the phases, the sizes and
the openings off `phaseFirst_P20`, `sizes_P20` and `opens_P20` instead of evaluating the schedule. -/

private theorem aLane_eqN (p : Params) (k : ℕ) : aLane p k = ((arithPos p).getD k 0 + 40) / 8 := by rw [aLane]

private theorem arithPos_eqN (p : Params) : arithPos p =
    [phaseByte p .tape + 24 * p.tableEvals, phaseByte p .tape + 24 * p.tableEvals + 72 * p.logN,
      phaseByte p .tape + 24 * p.tableEvals + 72 * p.logN + 24 * lanes, phaseByte p .wire,
      phaseByte p .ks, phaseByte p .ks + 72 * p.ksLog, phaseByte p .ks + 72 * p.ksLog + 24 * lanes,
      phaseByte p .ksLink] := by
  rw [arithPos]

private theorem phaseByte_eqN (p : Params) (ph : Phase) :
    phaseByte p ph = ((phaseFirst p).find? (·.1 == ph)).elim 0 (·.2.2) := by rw [phaseByte]

private theorem phByte_eqN (p : Params) (ph : Phase) :
    phByte p ph = ((phaseFirst p).find? (·.1 == ph)).elim 0 (·.2.2) := by rw [phByte]

private theorem openU_eqN (p : Params) : openU p = (phByte p .openMain + 96) / 8 := by rw [openU]

set_option maxRecDepth 200000 in
/-- **`HarNumT` at `P20`** (kernel). -/
theorem harNumT20 : HarNumT (streamLanes P20) (phaseByte P20 .tape + 24 * P20.tableEvals) (phaseByte P20 .wire)
    (phaseByte P20 .ks) (phaseByte P20 .ksLink) (8 * openU P20) := by
  unfold HarNumT
  simp only [aLane_eqN, arithPos_eqN, phaseByte_eqN, openU_eqN, phByte_eqN, phaseFirst_P20, opens_P20,
    sizes_P20.2.2.2.2.2.2.1, sizes_P20.2.2.2.2.2.2.2.2]
  decide +kernel

/-- `KS`'s layer check at `P20` (KS13: `layOk 9`). -/
theorem layOk_9T : layOk 9 = true := by rw [Lvm.Q1.layOk_eq_lit, Lvm.Q1.layerTBT_eq_F, Lvm.Q1.layOkT_eq_R]; decide +kernel

/-- **`SLok` of `KS`'s block E at `P20`** (`LvmFinDec.okE_P20`'s text; the typed closure does not import
`LvmFinDec`). -/
theorem okE_P20T (Q : ℕ) (gate : Cell) (sh : LoopOut) : SLok (ksBlockE P20 Q sh gate) = true := by
  rw [ksBlockE, if_pos (by decide), ksSelC_P20, sizes_P20.2.2.2.2.2.2.2.2, ksSplit_P20,
    show P20.ksLog = 13 from rfl]
  rw [← SLok_shape]
  simp only [ksGlueE14, List.map_append, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
  rw [loadsAt_shape, loadsAt_shape (q := ksQV 13 Q), preRecIns_shape, preRecIns_shape (n := 13 * 13 + 6),
    preRecIns_shape (n := 25 * 13 + 6), mulChainIns_shape (n := 38 * 13 + 8),
    mulChainIns_shape (n := 39 * 13 + 8)]
  simp only [List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc, shape_mulI,
    shape_linI, shape_addI, shape_loc, rho'C, preP, shape_ins_mk, shape_getD_mapCellSrc, sumSrc,
    reduceCtorEq, if_false, List.length_cons, List.length_nil]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

/-- **The circuit's mini-bus record is V_S's** at `P20`: the tables are all sumcheck tables, the rounds and depth are
the record's, and the typed phases end where the tape starts. -/
theorem mini20 (S : Lvm.CT.SF20) : M3.sumcheckTabs NT20.mbT = NT20.mbT ∧ tdata20.mbR = P20.tableRounds ∧
    tdata20.mbD = P20.busDepth ∧ typedEnd tdata20 (typedPos P20) = phaseByte P20 .tape + 24 * P20.tableEvals := by
  have hsc : M3.sumcheckTabs (mbTOf cfg20 frz20) = mbTOf cfg20 frz20 := mbT_sumcheck cfg20 _ _ _
  have hm := S.mini
  rw [NT20_mbT, show cfg20.p = P20 from rfl] at hm
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hD⟩, -⟩, -⟩, hR⟩, hE⟩, -⟩, -⟩, -⟩ := hm
  rw [hsc] at hR hE
  have hR' : tdata20.mbR = P20.tableRounds := by rw [tdata20_mbR, hR]
  have hD' : tdata20.mbD = P20.busDepth := by rw [tdata20_mbD, hD]
  refine ⟨by rw [NT20_mbT, hsc], hR', hD', ?_⟩
  have hW : (tdata20.mbS.map (·.cols.length)).sum = P20.tableEvals := by
    rw [hE, tdata20_mbS, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun t _ => by simp [M3.Tab.shape, M3.Tab.w])
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbe, -⟩ := harNumT20
  -- `rw`, not `unfold` (a delta `change` on these closed `Nat` terms made the kernel evaluate `tdata20.mbS`)
  rw [typedEnd, tabEnd, hW, hR', hD', ← hbe]

/-- **Part 2: the typed core gadget** (`typedG` replays `dTypedT`, as `busG_replays`, `tabG_replays`,
`qacc_replays` replay roll 7's phases 2, 3, 3b): the folded accumulator is `PUB`'s `acc_in`, the typed claims are
`typedClaimsN` of the cells, the mini-bus's evaluations are its table cells'. -/
theorem typedG_replays (S : Lvm.CT.SF20) (vk cL : Vector UInt8 32) {c : Ctx} {M : Mem} {sig : ByteArray}
    {T : Nat} (hS : Streamed M sig T) (hH : 11 + pubLanes ≤ T)
    (hT : typedEnd tdata20 (typedPos P20) + 40 ≤ 8 * T) (hg : M.k (pbB cfg20) = 1)
    (hvk : ∀ i < 4, M.k (pbB cfg20 + 1 + i) = (digestLanes vk).getD i 0)
    {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E) (hz : z.val M = 0) (ho : one.val M = 1) (q : Ptr)
    (hq : 1 ≤ q.e) :
    Replays c M sig (TypedV.dTypedT P20 NT20 (NT20.m3 P20) (pubOf vk cL sig))
      (typedG tdata20 (pbB cfg20) (typedPos P20) z one) q (typedPos P20) (typedEnd tdata20 (typedPos P20))
      fun v t ↦ v.1 = Lvm.QAcc.accC M (pbB cfg20) ∧
        v.2.1 = TypedV.typedClaimsN NT20 P20 (vs M t.ry) (vs M t.rv) (vs M t.rr) (t.vR.val M) ∧
        v.2.2 = t.tab.map fun e ↦ (vs M e.1, vs M e.2) := by
  obtain ⟨hsc, hR, hD, -⟩ := mini20 S
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hld, -⟩ := harNumT20
  have hfix : FixListed NT20.mbT tdata20.mbFix := by rw [NT20_mbT, tdata20_mbFix]; exact mbT_fix cfg20 _ _ _
  -- `P` explicit: from `busPos_mod_P20` it was `busPos P20`, and the kernel evaluated the closed `typedEnd` terms
  exact typedG_replaysG (P := typedPos P20) vk cL hS hH hg hvk hzE hoE hz ho P20 hld (harChk_sound S.har).1 hsc
    (by rw [tdata20_mbS, NT20_mbT]) hR hD hfix busPos_mod_P20 hT q hq

set_option maxHeartbeats 4000000 in
/-- **The typed HAR at `P20`** (L-H): the B program's Q_arith on a good node pair's memory accepts the child's stream
under V_S's typed decision and folds to the statement's `acc_in`. -/
theorem harithT20 (S : Lvm.CT.SF20) (H : THyp Lvm.CT.Ti20) {vk c : RecursionFast.Digest} {x : List UInt8}
    {qm : Column CMain.nu20} {qr : Column 19} (hok : okS vk c x = true) (hb : (hdrOf x).b = 1)
    (hG : GoodT Lvm.CT.Ti20 H x qm qr) (hin : InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr)
    (hL : LaneLink P20 (wsC qr)) (hLk : LinkOk P20 (decode P20 (wsC qr)))
    (hrun : Lvm.QSig.Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)) (memT x qm qr) qaB
      (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0))
    (hbv : BVT vk x qm qr) :
    TypedV.decideCoreT P20 NT20 vk (hdrOf x).cL (sigC qr) = true ∧
      TypedV.accOutOfT P20 NT20 vk (hdrOf x).cL (sigC qr) = (pubX x).accIn := by
  obtain ⟨htd, hcl⟩ := harChk_sound S.har
  obtain ⟨hpos, hn, hk, hql2, hql3, hql6, hTw, hTgk, hTr, hTv, hTrk, hTvk, hD, hDk, hTlk, hTlk', hB, hB2, hK, hT29,
    hlog, hH, hT4, hP8, hop, hld, hnuR, hnuM, hlogN, hmod, hbe, h0⟩ := harNumT20
  obtain ⟨hsc, -, -, hTE⟩ := mini20 S
  -- the stream, the gate, `vk`, the end of `Σ'`
  have hT := hQ20.hT
  have hsz := hL.size
  have hTL : streamLanes P20 = hashedLen P20 / 8 := by
    rw [sizes_P20.2.2.2.2.2.2.1, sizes_P20.2.2.2.2.2.1]
  have hT' : hashedLen P20 / 8 + 17 ≤ 2 ^ (lay cfg20).m := hT
  have hsz' : hashedLen P20 ≤ 8 * (wsC qr).length := hsz
  have e1 : streamLanes P20 ≤ 2 ^ (lay cfg20).m := by
    rw [hTL]; generalize hashedLen P20 = H at hT' ⊢; generalize 2 ^ (lay cfg20).m = K at hT' ⊢; omega
  have e2 : 8 * streamLanes P20 ≤ hashedLen cfg20.p := by
    rw [show cfg20.p = P20 from rfl, hTL]; generalize hashedLen P20 = H; omega
  have e3 : streamLanes P20 ≤ (wsC qr).length := by
    rw [hTL]; generalize hashedLen P20 = H at hsz' ⊢; generalize (wsC qr).length = K at hsz' ⊢; omega
  have hS : Streamed (memT x qm qr) (sigC qr) (streamLanes P20) := streamed_child cfg20 hS20 hL hin.stream e1 e2 e3
  have hpub : ∀ j < pubLanes, (memT x qm qr).k (pbB cfg20 + j) = Lvm.NS.hdrLane x j := hin.pub
  have hg : (memT x qm qr).k (pbB cfg20) = 1 := hin.flag
  have hgv : (kc (pbB cfg20)).val (memT x qm qr) = 1 := gate_val cfg20 hg
  have hvk := vk_cellsT hpub (okS_vk hok)
  have hend : 8 * stackEndL P20.grind P20.mainOod P20.mainLevels (openU P20 + 15) = (sigC qr).size := by
    rw [(lay20 (posBase cfg20) (pwBase cfg20)).2.1, sigC, traceBytesB_decode hS20 hL, sigma_sizeT hsz]
  -- Q_arith: phases 4–7, then `qarithB`
  rw [p2_eqT] at hrun
  have h : Lvm.QSig.Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)) (memT x qm qr)
      (phases47 cfg20 >>= qarithB cfg20 tdata20) (p2C cfg20) := hrun
  obtain ⟨h47, hR⟩ := okb h
  obtain ⟨o, ho47⟩ : ∃ o, (phases47 cfg20 (p2C cfg20)).1 = o := ⟨_, rfl⟩
  obtain ⟨q0, hq0⟩ : ∃ q0, (p2C cfg20).adv (phases47 cfg20 (p2C cfg20)).2 = q0 := ⟨_, rfl⟩
  simp only [ho47, hq0] at hR hcl
  simp only [qarithB] at hR
  simp only [qarithBParts, bind_apply, pure_apply] at hcl
  -- the constants
  obtain ⟨hZ, hR⟩ := okb hR
  have hzv : (ec q0.e).val (memT x qm qr) = 0 := (constE_val hZ.1).trans ofK_zero
  have ez : (const .E 0 (kc 0) q0).1 = ec q0.e := rfl
  rw [ez, Lvm.Loop.QRing.constE_adv] at hR hcl
  obtain ⟨hO1, hR⟩ := okb hR
  have hov : (ec (q0.e + 1)).val (memT x qm qr) = 1 := (constE_val hO1.1).trans ofK_one
  have eo : (const .E 1 (kc 0) ⟨q0.k, q0.e + 1⟩).1 = ec (q0.e + 1) := rfl
  rw [eo, Lvm.Loop.QRing.constE_adv] at hR hcl
  -- the typed core
  obtain ⟨hTy, hR⟩ := okb hR
  generalize ht : (typedG tdata20 (pbB cfg20) (typedPos cfg20.p) (ec q0.e) (ec (q0.e + 1))
    ⟨q0.k, q0.e + 1 + 1⟩).1 = t at hR hcl
  generalize hq2 : (⟨q0.k, q0.e + 1 + 1⟩ : Ptr).adv (typedG tdata20 (pbB cfg20) (typedPos cfg20.p) (ec q0.e)
    (ec (q0.e + 1)) ⟨q0.k, q0.e + 1 + 1⟩).2 = q2 at hR hcl
  obtain ⟨hTC, hR⟩ := okb hR
  generalize htc : (typedClaimsC (ec q0.e) (ec (q0.e + 1)) tdata20 cfg20.p.nuMain (layout0 cfg20.p).s t q2).1 = tc
    at hR hcl
  generalize hq3 : q2.adv (typedClaimsC (ec q0.e) (ec (q0.e + 1)) tdata20 cfg20.p.nuMain (layout0 cfg20.p).s t
    q2).2 = q3 at hR hcl
  obtain ⟨h8, hR⟩ := okb hR
  generalize hq4 : q3.adv (ringGkr (cfg20.p.ksLog - 4) (aLane cfg20.p 6) q0.e q3).2 = q4 at hR hcl
  obtain ⟨h9, hR⟩ := okb hR
  generalize hq5 : q4.adv (ksLinkG cfg20.p (aLane cfg20.p 7) q0.e (q0.e + 1) q4).2 = q5 at hR hcl
  -- the typed phases
  have hq1 : 1 ≤ (⟨q0.k, q0.e + 1 + 1⟩ : Ptr).e := by simp
  have RT := typedG_replays S vk (hdrOf x).cL (c := ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)) hS hH
    (by rw [hTE]; exact hT4) hg hvk (z := ec q0.e) (one := ec (q0.e + 1)) rfl rfl hzv hov ⟨q0.k, q0.e + 1 + 1⟩ hq1
  have htyped : PhaseAt (TypedV.dTypedT P20 NT20 (NT20.m3 P20) (pubOf vk (hdrOf x).cL (sigC qr))) (sigC qr) (typedPos P20)
      (phaseByte P20 .tape + 24 * P20.tableEvals)
      (Lvm.QAcc.accC (memT x qm qr) (pbB cfg20), TypedV.typedClaimsN NT20 P20 (vs (memT x qm qr) t.ry) (vs (memT x qm qr) t.rv) (vs (memT x qm qr) t.rr) (t.vR.val (memT x qm qr)),
        t.tab.map fun e => (vs (memT x qm qr) e.1, vs (memT x qm qr) e.2)) := by
    rw [← hTE]
    refine phaseAt_of RT hTy fun a ha => ?_
    rw [show typedPos P20 = typedPos cfg20.p from rfl, ht] at ha
    obtain ⟨a1, a2, a3⟩ := ha
    exact Prod.ext a1 (Prod.ext a2 a3)
  -- phases 4–7
  have hnb' : ∀ j < cfg20.p.logN, (kc ((sigIn cfg20).bn + 2 + j)).val (memT x qm qr) = bitE (pubOf vk (hdrOf x).cL (sigC qr)).n j := by
    intro j hj
    rw [pub_n hS hT29 vk (hdrOf x).cL, Cell.val_K]
    exact bitE_out1 (by rw [show cfg20.p = P20 from rfl] at hj; omega) (hbv.nb j hj)
  have hsl : (pubOf vk (hdrOf x).cL (sigC qr)).s = (List.range 4).map fun l => (memT x qm qr).k ((sigIn cfg20).hd + 9 + l) := by
    rw [pub_s hS hT29 vk (hdrOf x).cL]
    refine List.map_congr_left fun l _ => ?_
    rw [sLane_eq]; rfl
  have hlay : layOk (cfg20.p.logN - 5) = true := by
    rw [show cfg20.p = P20 from rfl, hlogN]; exact Lvm.Q1.layOk_15
  have hlayk : layOk (cfg20.p.ksLog - 4) = true := by
    rw [show cfg20.p.ksLog - 4 = 9 from rfl]; exact layOk_9T
  have hposS : P47Pos P20 (phaseByte P20 .tape + 24 * P20.tableEvals) (phaseByte P20 .wire) (phaseByte P20 .ks)
      (phaseByte P20 .ksLink) (8 * openU P20) := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hpos
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
  have hTgk' := le_trans (Nat.le_add_right _ 48) hTgk
  rw [show (P20 : Params) = cfg20.p from rfl] at hposS hn hk hql2 hql3 hql6 hTw hTgk' hTr hTv hTrk hTvk hD hDk hTlk hB hB2 hK
  obtain ⟨tp, wo, htp, -, hwiC, htw, hks, hksl, hokK⟩ := p47_at cfg20 (pubOf vk (hdrOf x).cL (sigC qr)) hposS hn hk hlay hlayk hql2 hql3 hql6 hS hTw
    hTgk' hTr hTv hTrk hTvk hD hDk hTlk hB hB2 hK (fun sh => okE_P20T _ _ sh) hnb' hbv.n1 hbv.nN hbv.sb hsl hgv
    h47 o ho47 (NT20.m3 P20) (real_eq _ _)
  rw [show cfg20.p = P20 from rfl] at htp hwiC hks hksl hokK
  generalize hkl : (NT20.m3 P20).ksLink (ksLinkView P20 (NT20.m3 P20) (feAt (sigC qr)) (phaseByte P20 .ksLink) (vs (memT x qm qr) o.rk) (pubOf vk (hdrOf x).cL (sigC qr)))
    = KL at hksl hokK
  obtain ⟨okK, kL⟩ := KL
  -- the openings
  have key := core_of_phasesT P20 NT20 vk (hdrOf x).cL (sigC qr) h0 htyped htp hwiC hks hksl hokK
  refine (fun hc => ⟨hc.1, hc.2.trans (accC_eqT hpub)⟩) (key ?_)
  intro s hs hok
  dsimp only
  -- the claim checks
  obtain ⟨hall, hwm, hzw, hnd1, hnd2, hnd⟩ := claimsOkB_parts hcl
  -- the openings' run on the circuit's claims
  rw [show cfg20.p = P20 from rfl] at hR hall hwm hzw hnd
  have hq5 : 1 ≤ q5.e := by
    have e2 := adv_e_le (⟨q0.k, q0.e + 1 + 1⟩ : Ptr) (typedG tdata20 (pbB cfg20) (typedPos cfg20.p) (ec q0.e)
      (ec (q0.e + 1)) ⟨q0.k, q0.e + 1 + 1⟩).2
    have e3 := adv_e_le q2 (typedClaimsC (ec q0.e) (ec (q0.e + 1)) tdata20 cfg20.p.nuMain (layout0 cfg20.p).s t q2).2
    have e4 := adv_e_le q3 (ringGkr (cfg20.p.ksLog - 4) (aLane cfg20.p 6) q0.e q3).2
    have e5 := adv_e_le q4 (ksLinkG cfg20.p (aLane cfg20.p 7) q0.e (q0.e + 1) q4).2
    rw [hq2] at e2; rw [hq3] at e3; rw [hq4] at e4; rw [hq5] at e5
    exact le_trans (Nat.le_add_left 1 (q0.e + 1)) (le_trans e2 (le_trans e3 (le_trans e4 e5)))
  have hσ : (1 + (o.mb.getD 18 default).val (memT x qm qr)) * (1 + (o.mb.getD 19 default).val (memT x qm qr)) =
      if decide ((pubOf vk (hdrOf x).cL (sigC qr)).n ≤ 2 ^ CMain.smallLogN20) then 1 else 0 := by
    have hmb := htw.mb
    rw [show cfg20.p.logN = 20 from hlogN] at hmb
    exact sigma_val o.mb _ hmb hbv.n1 (by have := hbv.nN; rw [hlogN] at this; exact this)
  have hOT := openT_at hS hg (lay20 (posBase cfg20) (pwBase cfg20)).1
    hop hbv.posm hend (fun k hk _ => hbv.pw k hk) _ hall hwm rfl rfl hzv hov hq5 (pubOf vk (hdrOf x).cL (sigC qr))
    o.mb hσ hzw hR s
    (by rw [hs]) hok
  -- the parts of the claim list
  obtain ⟨ev, evk, erl, sK⟩ := p47_out_facts cfg20 h47 ho47 hS hlayk hql6 hTgk'
  rw [show cfg20.p = P20 from rfl] at sK h8 h9 hql6 hTgk' hposS erl
  have hze : (memT x qm qr).e q0.e = 0 := hzv
  have hoe : (memT x qm qr).e (q0.e + 1) = 1 := hov
  have rK := ringGkr_rel _ hql6 sK hS hTgk hze h8.1
  have hh4 : (pubOf vk (hdrOf x).cL (sigC qr)).h = (List.range 4).map fun l => (memT x qm qr).k (hLane l) := pub_h hS hT29 vk (hdrOf x).cL
  -- the typed claims
  obtain ⟨T1, T2, C2⟩ := typedClaimsC_val hzv hov htd P20.nuMain (layout0 P20).s t NT20.mbT
    (by rw [tdata20_mbS, NT20_mbT]) q2 hTC.1
  rw [show cfg20.p.nuMain = P20.nuMain from rfl, show (layout0 cfg20.p).s = (layout0 P20).s from rfl] at htc
  rw [htc] at T1 T2 C2
  have C1 : ∀ cc ∈ tc.1, cc.com = .main := fun cc hcc => by
    have := List.all_eq_true.mp hall cc (by simp [hcc])
    simpa using this
  rw [← hsc, ← m3_tableClaimsT NT20 P20 (pubOf vk (hdrOf x).cL (sigC qr))] at T1 T2
  -- the rest's tails in the small shape
  have htt : TypedV.smallT P20 (pubOf vk (hdrOf x).cL (sigC qr)) = true → (tapeClaimsC P20 q0.e (q0.e + 1) o).map (Lvm.QShape.tailC (memT x qm qr)) =
      Shape.tapeTails P20 tp wo (vs (memT x qm qr) o.wire.ring.cs) (pubOf vk (hdrOf x).cL (sigC qr)) := by
    intro hsm
    rw [smallT_P20] at hsm
    have hmR : (⟨.main, .ring ⟨P20.nuMain, 0⟩ (o.wire.sigma ++ o.wire.tau ++ selC q0.e (q0.e + 1) (dSel P20)
        (dSelBits P20)) o.wire.ring.cs, o.wire.ring.target⟩ : CClaim) ∈
        onCom (tc.1 ++ tc.2 ++ (tapeClaimsC P20 q0.e (q0.e + 1) o ++
          kClaimsC ⟨P20.ksLog + slotLog, (layout0 P20).ks⟩ o.kko (ringGkr (P20.ksLog - 4) (aLane P20 6) q0.e q3).1) ++
          ksOutC P20 o.rk o.vk q0.e (q0.e + 1) ++ (ksLinkG P20 (aLane P20 7) q0.e (q0.e + 1) q4).1) .main := by
      refine List.mem_filter.mpr ⟨?_, rfl⟩
      simp only [List.mem_append, tapeClaimsC, List.mem_singleton, true_or, or_true]
    have zR := hzw _ hmR
    simp only [Lvm.QShape.ZWF, hnuM, if_true, Bool.and_eq_true, decide_eq_true_eq, List.length_append, selC,
      List.length_map, List.length_range] at zR
    have hdb : dSelBits P20 = 1 := by rw [dSelBits, hnuM, hlogN]
    have hστ : (o.wire.sigma ++ o.wire.tau).length = 22 := by
      have := zR.1.1
      simp only [hdb, show CMain.nu20 = 23 from rfl, List.length_append] at this ⊢
      first | exact this | exact Nat.succ.inj this
    exact tapeTails_eq cfg20 hze hoe htw (by rw [erl, hlogN]) hστ (by rw [hh4]; simp) hsm hDzT.1 hDzT.2 hbv.n1
  -- the rest's values (each stated in V_S's form, so that the last step matches syntactically)
  have htape' : (tapeClaimsC P20 q0.e (q0.e + 1) o).map (CClaim.val (memT x qm qr)) =
      (tapeClaims P20 tp wo (pubOf vk (hdrOf x).cL (sigC qr))).map (.main, ·) := by
    have e := tapeClaimsC_val cfg20 hze hoe htw ev hh4
    rw [show cfg20.p = P20 from rfl] at e
    exact e
  have hks' : (kClaimsC ⟨P20.ksLog + slotLog, (layout0 P20).ks⟩ o.kko (ringGkr (P20.ksLog - 4) (aLane P20 6) q0.e q3).1).map
      (CClaim.val (memT x qm qr)) = (keccakClaims (NT20.m3 P20).ksBlock (o.kko.vals (memT x qm qr))
        (ringAt (feAt (sigC qr)) (8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40) (o.kko.vals (memT x qm qr)).slicePoint
        (o.kko.vals (memT x qm qr)).slices)).map (.main, ·) := by
    rw [m3_ksBlockT]; exact kClaimsC_val _ o.kko _ _ rK
  have hko' : (ksOutC P20 o.rk o.vk q0.e (q0.e + 1)).map (CClaim.val (memT x qm qr)) =
      (NT20.m3 P20).ksOutputClaims (vs (memT x qm qr) o.rk) (vs (memT x qm qr) o.vk) := by
    rw [show NT20.m3 P20 = M3.real P20 (fun _ => NT20.mbT) from rfl, real_eq]
    exact ksOutC_val P20 o.rk o.vk hze hoe evk
  have hkl' : (ksLinkG P20 (aLane P20 7) q0.e (q0.e + 1) q4).1.map (CClaim.val (memT x qm qr)) = kL := by
    have e : (ksLinkG P20 (aLane P20 7) q0.e (q0.e + 1) q4).1.map (CClaim.val (memT x qm qr)) =
        ((M3.real P20 (fun _ => NT20.mbT)).ksLink (ksLinkView P20 (M3.real P20 (fun _ => NT20.mbT)) (feAt (sigC qr))
          (phaseByte P20 .ksLink) (vs (memT x qm qr) o.rk) (pubOf vk (hdrOf x).cL (sigC qr)))).2 := by
      rw [real_eq]; exact ksLinkG_val' P20 _ _ hk hposS.l7 hS hTlk' hze hoe h9.1
    rw [e, show M3.real P20 (fun _ => NT20.mbT) = NT20.m3 P20 from rfl, hkl]
  have eq := openClaimsT_eq P20 (TypedV.smallT P20 (pubOf vk (hdrOf x).cL (sigC qr))) NT20 (NT20.m3 P20) (pubOf vk (hdrOf x).cL (sigC qr)) (ec q0.e) hzv t.ry t.rv t.rr t.vR
    (t.tab.map fun e => (vs (memT x qm qr) e.1, vs (memT x qm qr) e.2)) tp wo (vs (memT x qm qr) o.wire.ring.cs) (vs (memT x qm qr) o.rk) (vs (memT x qm qr) o.vk)
    (keccakClaims (NT20.m3 P20).ksBlock (o.kko.vals (memT x qm qr))
      (ringAt (feAt (sigC qr)) (8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40) (o.kko.vals (memT x qm qr)).slicePoint
        (o.kko.vals (memT x qm qr)).slices)) kL tc.1 tc.2
    (tapeClaimsC P20 q0.e (q0.e + 1) o)
    (kClaimsC ⟨P20.ksLog + slotLog, (layout0 P20).ks⟩ o.kko (ringGkr (P20.ksLog - 4) (aLane P20 6) q0.e q3).1)
    (ksOutC P20 o.rk o.vk q0.e (q0.e + 1)) (ksLinkG P20 (aLane P20 7) q0.e (q0.e + 1) q4).1 hnuR T1 T2 C1 hnd1 hnd2
    htape' hks' hko' hkl' htt hnd
  rw [eq]
  rw [show (ec q0.e).n = q0.e from rfl, show (ec (q0.e + 1)).n = q0.e + 1 from rfl] at hOT
  exact hOT

end Lvm.Har
