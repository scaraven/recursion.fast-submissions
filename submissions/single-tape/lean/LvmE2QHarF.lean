-- New for lvm2 E2-FT (E2F-C): the S2GF node program's Q_arith is V_S's decision (`harithF20`, roll 11's
-- `harithT20` at S2GF): from Q_arith's segments on a good pair's memory, `decideFFX P20F NTF20` accepts the child's
-- stream, composed by `core_of_phasesF` from the gadgets' phase lemmas (pin, typed, tape + wire, `KS`, `KS` link,
-- the opening) and `decideFFX_of`; the typed claims stand for V's (`typedClaimsC_ok`, `e3s_rel`).
import LvmE2QInst
import LvmE2QNodeG
import LvmE2QHarTop
import LvmE2QHarPos
import LvmQTypedHarB
import LvmE2QTypedPhase
import LvmQTypedHarS
import LvmE2QHarFront
import LvmE2QHarIn
import LvmE2QHarPosOk
import LvmE2QTypedReg
import LvmE2QHarGen

/-!
# Q_arith at S2GF (`harithF20`)

* **`qaF20`**: Q_arith of the S2GF node program (the root pin, the `E2` front, `qarithF`), so that
  `QF20 = toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qaF20)` (`QF20_qa`).
* **`harithF20`**: on a stream-block pair of the S2GF good relation whose memory carries the input map, with Q_link's
  `LaneLink`/`LinkOk`, Q_arith's segments ⇒ `decideFFX P20F NTF20 vk c_L Σ = true` (`nodeSoundFG`'s `harith`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed LeanVM.Protocol

-- `posLanesDec` is in `LvmE2QTypedReg` (moved, lvm2 U-TAPE).

-- `typedRegB`, `typedRegB_sound` are in `LvmE2QTypedReg` (moved, lvm2 U-TAPE).

/-- **The HAR's static checks at S2GF** (roll 11's `harChkB`: the regions and the phases' positions in `Σ`), decided
by the S2GF guard (`staticOkBF20`, natively): the circuit's typed regions are V_S's (`tdMatchB`), the typed phases
start on a lane boundary, end where the tape phase starts, and inside the stream; the opening starts inside the stream
(the front's lane bounds); every proof-of-work answer of the front is streamed with `g ≤ 64` (`powOkF`'s `hpw`).
(The opening's claim shapes follow with `open_phase`.) -/
def harChkBF20 : Bool :=
  Lvm.QTyped.tdMatchB tdataF20 NTF20 && typedPosF P20F % 8 == 0 &&
    typedEndX tdataF20 (typedPosF P20F) == posOf P20F (phaseItem0 P20F .tape) &&
    decide (typedEndX tdataF20 (typedPosF P20F) + 40 ≤ 8 * streamLanes P20F) &&
    decide (posOf P20F (phaseItem0 P20F .openMain) + 48 ≤ 8 * streamLanes P20F) &&
    (powFront P20F).all (fun a => decide (a.1 + 2 < streamLanes P20F) && decide (a.2 ≤ 64)) &&
    posOf P20F (phaseItem0 P20F .openMain) == 8 * (phaseLane P20F .openMain 0 - 5) &&
    Lvm.Har.LayOk (cfgMainF P20F (fun _ => 0) (fun _ => 0)) (streamLanes P20F) &&
    8 * Lvm.Har.stackEndL P20F.grind P20F.mainOod P20F.mainLevels (phaseLane P20F .openMain 0 - 5 + 15) ==
      hashedLen P20F &&
    decide (P20F.mainLevels.length ≤ (Lvm.QLink.opens P20F).length) && decide (1 ≤ 64 - P20F.grind) &&
    decide (Lvm.Fin.PosLanes P20F P20F.grind P20F.mainOod P20F.mainLevels (phaseLane P20F .openMain 0 - 5 + 15) 0) &&
    typedRegB tdataF20 (layout0 P20F).s

/-- The facts `harChkBF20` decides. -/
theorem harChkF20_sound (h : harChkBF20 = true) :
    Lvm.Har.TdOk tdataF20 NTF20 ∧ typedPosF P20F % 8 = 0 ∧
      typedEndX tdataF20 (typedPosF P20F) = posOf P20F (phaseItem0 P20F .tape) ∧
      typedEndX tdataF20 (typedPosF P20F) + 40 ≤ 8 * streamLanes P20F ∧
      posOf P20F (phaseItem0 P20F .openMain) + 48 ≤ 8 * streamLanes P20F ∧
      (∀ a ∈ powFront P20F, a.1 + 2 < streamLanes P20F ∧ a.2 ≤ 64) ∧
      posOf P20F (phaseItem0 P20F .openMain) = 8 * (phaseLane P20F .openMain 0 - 5) ∧
      Lvm.Har.LayOk (cfgMainF P20F (fun _ => 0) (fun _ => 0)) (streamLanes P20F) = true ∧
      8 * Lvm.Har.stackEndL P20F.grind P20F.mainOod P20F.mainLevels (phaseLane P20F .openMain 0 - 5 + 15) =
        hashedLen P20F ∧
      P20F.mainLevels.length ≤ (Lvm.QLink.opens P20F).length ∧ 1 ≤ 64 - P20F.grind ∧
      Lvm.Fin.PosLanes P20F P20F.grind P20F.mainOod P20F.mainLevels (phaseLane P20F .openMain 0 - 5 + 15) 0 ∧
      typedRegB tdataF20 (layout0 P20F).s = true := by
  simp only [harChkBF20, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨Lvm.Har.tdOk_of h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

-- `cfgMainF_*`, `layOkF_pb` and the generic lemmas below `qaF20` are in `LvmE2QHarGen` (moved, lvm2 U-TAPE).

/-- **Q_arith of the S2GF node program**: the root pin, the `E2` front, `qarithF`. -/
def qaF20 : BM Unit := do
  let pin ← pinF cfgF20.p
  let o ← frontF cfgF20
  qarithF cfgF20 tdataF20 pin o

/-- The S2GF node program is a node program with Q_arith `qaF20`. -/
theorem QF20_qa : QF20 = toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qaF20) :=
  QF20_eq

/-- **`Φ_Q` holds at the statement's `acc_in`** for V_S's fast evaluator at S2GF (`NTF20.phi = PhiQCX cacheF20`):
statement 13 (`PhiQCX_eq`, its cache check decided in the guard) and the good pair's `AccOkTX`. -/
theorem phiF20_acc (S : NodeGF frzF20 QF20 layF20 NTF20) (H : THypX TiF20) {x : List UInt8}
    {qm : Column CMain.nu20} {qr : Column 19} (hG : E2V.GoodTF TiF20 H x qm qr) :
    NTF20.phi (Lvm.VEq.pubXF x).accIn.pt = (Lvm.VEq.pubXF x).accIn.y := by
  have hacc : AccOkTX TiF20 (Lvm.VEq.pubXF x) := hG.1.2
  have e : NTF20.phi (Lvm.VEq.pubXF x).accIn.pt = PhiQFX QF20 layF20 (Lvm.VEq.pubXF x).accIn.pt := by
    show PhiQCX cacheF20 _ = _
    rw [cacheF20_eq S.st.hlay]
    exact PhiQCX_eq QF20 layF20 S.st.hlay S.st.cache _ (H.acc x)
  rw [e]
  apply FE.toExt3_injective
  rw [← hacc]
  show _ = FE.toExt3 (PhiQFX QF20 layF20 (((Lvm.VEq.pubXF x).accIn.pt.map FE.toExt3).map FE.ofExt3))
  rw [List.map_map]
  congr 2

/-- The circuit's static data at S2GF is `tdataOf` (roll 11's `tdata20_eq`). -/
theorem tdataF20_of : tdataF20 = Lvm.QTyped.tdataOf cfgF20 frzF20 := rfl

/-- **The mini-bus record at S2GF** (roll 11's `mini20`): the tables are all sumcheck tables, the circuit's tables,
rounds, depth and fixed list are the record's. -/
theorem miniF20 (S : NodeGF frzF20 QF20 layF20 NTF20) : Lvm.M3.sumcheckTabs NTF20.mbT = NTF20.mbT ∧
    tdataF20.mbS = NTF20.mbT.map Lvm.M3.Tab.shape ∧ tdataF20.mbR = P20F.tableRounds ∧
    tdataF20.mbD = P20F.busDepth ∧ Lvm.Har.FixListed NTF20.mbT tdataF20.mbFix := by
  have hsc : Lvm.M3.sumcheckTabs (Lvm.QTyped.mbTOf cfgF20 frzF20) = Lvm.QTyped.mbTOf cfgF20 frzF20 :=
    Lvm.Har.mbT_sumcheck cfgF20 _ _ _
  have hm := S.st.mini
  have hN : NTF20.mbT = Lvm.QTyped.mbTOf cfgF20 frzF20 := rfl
  rw [hN, show cfgF20.p = P20F from rfl] at hm
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hD⟩, -⟩, -⟩, hR⟩, -⟩, -⟩, -⟩, -⟩ := hm
  rw [hsc] at hR
  obtain ⟨t1, t2, t3, t4⟩ := Lvm.Har.tdataOf_mb cfgF20 frzF20
  rw [tdataF20_of, hN, t1, t2, t3, t4, hR, hD]
  exact ⟨hsc, rfl, rfl, rfl, Lvm.Har.mbT_fix cfgF20 _ _ _⟩

/-- The small shape at `P20F` (generic in `pub`: a closed `pub` would make the kernel evaluate its `n`). -/
theorem smallT_P20F (pub : Pub) : TypedV.smallT P20F pub = decide (pub.n ≤ 2 ^ 18) := rfl

/-- **The typed claims stand for V's** (generic in the memory: the kernel never unfolds the instance's), from
`typedClaimsC_val`'s two lists and `typedClaimsC_ok`. -/
theorem typed_relF {M : Mem} {zc : Cell} {b : Bool} {N : TypedV.TNat} {pub : Pub} {t : Lvm.QTyped.TypedC}
    {tc : List Lvm.Har.CClaim × List Lvm.Har.CClaim} {z : Cell} (hz : z.val M = 0) {st : List Lvm.M3.Tab}
    {ev : List (List FE × List FE)} (hX : (N.m3 P20F).tableClaims pub ev = Lvm.M3.tableClaimsR st ev)
    (T1 : tc.1.map (Lvm.Har.CClaim.val M) =
      (.main, BlockClaim.point ⟨19, (layout0 P20F).s⟩ (Lvm.Har.vs M t.rr) (t.vR.val M)) ::
        (.main, ⟨⟨P20F.nuMain, 0⟩, TypedV.affW N .sigma (Lvm.Har.vs M t.ry), (t.rv.getD 2 z).val M⟩) ::
          (Lvm.M3.tableClaimsR st ev).filter (·.1 == .crec))
    (T2 : tc.2.map (Lvm.Har.CClaim.val M) =
      (.main, ⟨⟨P20F.nuMain, 0⟩, TypedV.affW N .com (Lvm.Har.vs M t.ry), (t.rv.getD 0 z).val M⟩) ::
        (.main, ⟨⟨P20F.nuMain, 0⟩, TypedV.affW N .ks (Lvm.Har.vs M t.ry), (t.rv.getD 3 z).val M⟩) ::
          (Lvm.M3.tableClaimsR st ev).filter (·.1 == .main))
    (hl2 : tc.1.length = 2) (hcok : ∀ cc ∈ tc.1 ++ tc.2, cOkB zc cc = true) :
    List.Forall₂ (Lvm.Q2.FRelZ M zc b) ((tc.1 ++ tc.2).map .e3)
      (TypedV.typedClaimsN N P20F (Lvm.Har.vs M t.ry) (Lvm.Har.vs M t.rv) (Lvm.Har.vs M t.rr) (t.vR.val M) ++
        Shape.zeroTails ((N.m3 P20F).tableClaims pub ev)) := by
  have hcr : (Lvm.M3.tableClaimsR st ev).filter (·.1 == .crec) = [] := by
    have := congrArg List.length T1
    rw [List.length_map, hl2] at this
    simp only [List.length_cons] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  have hmain : ∀ e ∈ Lvm.M3.tableClaimsR st ev, e.1 = .main := fun e he => by
    have := List.filter_eq_nil_iff.mp hcr e he
    revert this
    cases e.1 <;> simp
  have hmn : (Lvm.M3.tableClaimsR st ev).filter (·.1 == .main) = Lvm.M3.tableClaimsR st ev :=
    List.filter_eq_self.mpr fun e he => by simp [hmain e he]
  rw [hX]
  refine e3s_rel ?_ ?_ hcok
  · rw [List.map_append, T1, T2, hcr, hmn]
    simp only [TypedV.typedClaimsN, Shape.zeroTails, List.map_append, List.map_cons, List.map_map, List.nil_append,
      List.cons_append, Function.comp_def, List.map_id']
    rw [show P20F.nuRec = 19 from rfl, ← Lvm.QAcc.getD_vals t.rv z hz 2, ← Lvm.QAcc.getD_vals t.rv z hz 0,
      ← Lvm.QAcc.getD_vals t.rv z hz 3]
    rfl
  · intro e he
    simp only [TypedV.typedClaimsN, Shape.zeroTails, List.mem_append, List.mem_cons, List.mem_map,
      List.not_mem_nil, or_false] at he
    rcases he with (rfl | rfl | rfl | rfl) | ⟨e', he', rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨hmain e' he', rfl⟩

/-- **Q_arith at S2GF is V_S's decision** (`harithT20`'s twin; `nodeSoundFG`'s `harith` at the S2GF instance). -/
theorem harithF20 (S : NodeGF frzF20 QF20 layF20 NTF20) (hhar : harChkBF20 = true) (H : THypX TiF20)
    (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 →
      E2V.GoodTF TiF20 H x qm qr ∧ SBlk qm qr →
      InMapMB (spongeBlocks P20F) (pubLanesX accVF) (lay cfgF20) (sigIn cfgF20) (memF TiF20 x qm qr) vk x qm qr →
      LaneLink P20F (wsC qr) → LinkOk P20F (decode P20F (wsC qr)) →
      Ok (ctxOf TiF20.Q) (memF TiF20 x qm qr) qaF20 (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F) →
      E2V.decideFFX P20F NTF20 vk (hdrOf x).cL (traceBytesB (decode P20F (wsC qr))) = true := by
  intro c x qm qr hok hb hG hin hLL hlink hrun
  -- the program's three parts after Q_sig: the pin, the front, `qarithF`
  have hrun' : Lvm.QSig.Ok (ctxOf TiF20.Q) (memF TiF20 x qm qr)
      (pinF cfgF20.p >>= fun pin ↦ frontF cfgF20 >>= fun o ↦ qarithF cfgF20 tdataF20 pin o)
      (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F) := hrun
  obtain ⟨hPin, hR⟩ := Lvm.Har.okb hrun'
  -- (pointers and outputs as opaque variables: `generalize` would substitute the builders' runs back into the proof
  -- term, and the kernel then evaluates them when it compares cells)
  obtain ⟨q1, hq1⟩ : ∃ q1, (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F).adv
      (pinF cfgF20.p (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F)).2 = q1 := ⟨_, rfl⟩
  obtain ⟨pin, hpinE⟩ : ∃ pin, (pinF cfgF20.p (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F)).1 = pin :=
    ⟨_, rfl⟩
  rw [hq1, hpinE] at hR
  obtain ⟨hFr, hQa⟩ := Lvm.Har.okb hR
  obtain ⟨o, hfr⟩ : ∃ o, (frontF cfgF20 q1).1 = o := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q2, q1.adv (frontF cfgF20 q1).2 = q2 := ⟨_, rfl⟩
  rw [hfr, hq2] at hQa
  -- the static facts, the stream, the gate, `vk`
  obtain ⟨htd, hP8, hTE, hTT, hTO, hPW, hOU, hLY, hSE, hML, hGR, hPL, hTR⟩ := harChkF20_sound hhar
  have hle : typedPosF P20F ≤ typedEndX tdataF20 (typedPosF P20F) := by
    obtain ⟨a1, -, -, -⟩ := typedPosX_le tdataF20 (typedPosF P20F)
    have : typedPosF P20F ≤ wGPX (typedPosF P20F) := by simp only [wGPX, zAbcPX, zRPX]; omega
    have := (typedPosX_le tdataF20 (typedPosF P20F)).2.2.2
    have := (typedPosX_le tdataF20 (typedPosF P20F)).2.2.1
    have := (typedPosX_le tdataF20 (typedPosF P20F)).2.1
    omega
  have hS : Lvm.Q1.Streamed (memF TiF20 x qm qr) (sigCF qr) (streamLanes P20F) := streamedF hin.stream hLL
  have hTl : streamLanes P20F = 73001 := by rw [streamLanes, spongeBlocks_P20F.2]
  have hg : (memF TiF20 x qm qr).k (pbB cfgF20) = 1 := hin.flag
  have hvk := Lvm.Har.vk_cellsT (pub747F hin) (okS_vk hok)
  -- `qarithF`: the constants
  unfold qarithF at hQa
  obtain ⟨hZ, hR⟩ := Lvm.Har.okb hQa
  -- (the cells' equalities are stated without the memory: a kernel check of `Cell.val` at `memF TiF20` must not
  -- unfold the memory)
  have ez : (const .E 0 (kc 0) q2).1 = ec q2.e := rfl
  have hzv := (Lvm.Har.constE_val hZ.1).trans ofK_zero
  rw [ez] at hzv
  rw [ez, Lvm.Loop.QRing.constE_adv] at hR
  obtain ⟨hO, hR⟩ := Lvm.Har.okb hR
  have eo : (const .E 1 (kc 0) ⟨q2.k, q2.e + 1⟩).1 = ec (q2.e + 1) := rfl
  have hov := (Lvm.Har.constE_val hO.1).trans ofK_one
  rw [eo] at hov
  rw [eo, Lvm.Loop.QRing.constE_adv] at hR
  obtain ⟨hZK, hR⟩ := Lvm.Har.okb hR
  rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, Lvm.Har.constK_adv] at hR
  obtain ⟨hOK, hR⟩ := Lvm.Har.okb hR
  rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, Lvm.Har.constK_adv] at hR
  -- the typed phases (`typed_phaseX`), their claims, the shape cell (outputs and pointers opaque)
  obtain ⟨t, q3, ht, hq3e, hTy, hR⟩ := ok_bindV hR
  obtain ⟨tc, q4, htc, hq4e, hTC, hR⟩ := ok_bindV hR
  obtain ⟨ka, q5, hka, hq5e, hKA, hR⟩ := ok_bindV hR
  obtain ⟨kb, q6, hkb, hq6e, hKB, hR⟩ := ok_bindV hR
  obtain ⟨sK, q7, hsKe, hq7e, hSK, hOpen⟩ := ok_bindV hR
  obtain ⟨hsc, hSs, hRr, hDd, hfix⟩ := miniF20 S
  have htyped := typed_phaseX (c := ctxOf TiF20.Q) vk (hdrOf x).cL hS (by rw [hTl]; decide) hg hvk
    (z := ec q2.e) (o := ec (q2.e + 1)) rfl rfl hzv hov P20F rfl htd hsc hSs hRr hDd hfix hP8 hTT _
    (by simp) hTy
  rw [show cfgF20.p = P20F from rfl, show P20F.accV = accVF from rfl] at ht
  rw [hTE, accCA_pubXF (pb := pbB cfgF20) hin.pub, ht] at htyped
  -- the pin (`pin_phase`)
  have hnu : P20F.nuMain = 23 := rfl
  have hpb := pinHPF
  have hpe := pinEndF
  have hqa := pinQaF
  rw [hnu] at hpe hqa
  have epin : pinF cfgF20.p = Lvm.Q2.pinG 23 (phaseLane P20F .commit 1) (phaseLane P20F .commit (23 + 1)) := rfl
  rw [epin] at hPin hpinE
  obtain ⟨hpin, hpinV⟩ := Lvm.Q2.pin_phase hS (nu := 23) (by norm_num) hpb.symm hqa
    (by rw [hTl] at hTT ⊢; omega) (by rw [hqa]; rw [hTl] at hTT ⊢; omega) hPin.1
  rw [hpe] at hpin
  rw [hpinE] at hpinV
  obtain ⟨zP, aP, hzP, hzL⟩ := pinG_fst 23 (phaseLane P20F .commit 1) (phaseLane P20F .commit (23 + 1))
    (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F)
  rw [hpinE] at hzP
  have hpinB : (Lvm.pinD 23 (sigCF qr) ⟨posOf P20F 1, 0, true⟩).1 =
      BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memF TiF20 x qm qr) zP) (aP.val (memF TiF20 x qm qr)) := by
    rw [hzP, cclaim_point] at hpinV
    exact (Prod.mk.inj hpinV).2.symm
  rw [hpinB] at hpin
  -- the front's inputs (E2F-C6's `LvmE2QHarIn`) and its phases
  have hT29 : 29 ≤ streamLanes P20F := by rw [hTl]; norm_num
  obtain ⟨hrw, hrk⟩ := rowWordsF S H hG.1
  have hch := childOkF S H hok hb hG
  have hsb := sBits_onC (outsOnF S H hG.1)
  obtain ⟨hnb, hn, hsbv⟩ := frontIns hS hT29 (hbitsF S H hG.1) hch hsb accVF vk (hdrOf x).cL rfl rfl
  have hpow := powOkF S H hG.1 (pw := powF20) rfl hS (fun a ha => ha) hPW
  have hh : (pubOfA accVF vk (hdrOf x).cL (sigCF qr)).h = (List.range 4).map fun l => (memF TiF20 x qm qr).k (Lvm.Har.hLane l) :=
    Lvm.Har.pub_h hS hT29 vk (hdrOf x).cL
  have hsmE : TypedV.smallT P20F (pubOfA accVF vk (hdrOf x).cL (sigCF qr)) =
      decide ((pubOfA accVF vk (hdrOf x).cL (sigCF qr)).n ≤ 2 ^ 18) := smallT_P20F _
  obtain ⟨tp, co, lo, htape, hcall, hlink, hfrel, hmbv⟩ := front_phasesF hS hTO hg hpow hrw hrk
    (pubOfA accVF vk (hdrOf x).cL (sigCF qr)) hnb hn hsbv hh (ec q2.e)
    (TypedV.smallT P20F (pubOfA accVF vk (hdrOf x).cL (sigCF qr)))
    (fun h => by rw [hsmE] at h; exact of_decide_eq_true h) hFr
  rw [hfr] at hfrel hmbv
  -- the shape: `σ` from `n' − 1`'s bits 18, 19, the `K` cell `sK` (`(1 + b₁₈)(1 + b₁₉)`)
  have hσ := Lvm.Har.sigma_val o.mb _ hmbv hn.1 hn.2
  rw [← hsmE] at hσ
  have hzkv : (kc q2.k).val (memF TiF20 x qm qr) = 0 := by
    have e := const_val hZK.1
    rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, ofK_zero] at e
    exact e
  have hokv : (kc (q2.k + 1)).val (memF TiF20 x qm qr) = 1 := by
    have e := const_val hOK.1
    rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, ofK_one] at e
    exact e
  have hsK : sK.val (memF TiF20 x qm qr) =
      if TypedV.smallT P20F (pubOfA accVF vk (hdrOf x).cL (sigCF qr)) then 1 else 0 := by
    rw [← hsKe, mulAdd_spec hSK.1, ← hka, ← hkb, Lvm.Har.addK_val hKA.1, Lvm.Har.addK_val hKB.1, hzkv, ofK_one, add_zero, ← hσ]
    ring
  -- the opening's context, the pin as `FRel`
  have hF : Lvm.Q2.FCtxOk (memF TiF20 x qm qr)
      ⟨ec q2.e, ec (q2.e + 1), kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc (q2.k + 1), kc q2.k⟩, false⟩ := by
    refine ⟨hzv, hov, hzkv, rfl, rfl, ?_, ⟨rfl, rfl⟩, ?_⟩
    · show (⟨((kc (q2.k + 1)).val (memF TiF20 x qm qr)).c₀, ((kc q2.k).val (memF TiF20 x qm qr)).c₀⟩ : FE2) = 1
      rw [hokv, hzkv]; rfl
    · show (⟨((kc q2.k).val (memF TiF20 x qm qr)).c₀, ((kc q2.k).val (memF TiF20 x qm qr)).c₀⟩ : FE2) = 0
      rw [hzkv]; rfl
  have hpsp := Lvm.Q2.pinG_spec (c := ctxOf TiF20.Q) hS (nu := 23) (qz := phaseLane P20F .commit 1)
    (qa := phaseLane P20F .commit (23 + 1)) (by rw [hTl] at hTT ⊢; omega) (by rw [hqa]; rw [hTl] at hTT ⊢; omega) _
    hPin.1
  rw [hpinE, hzP, cclaim_point] at hpsp
  have hzl : zP.length = 23 := by
    rw [hzL]; simp
  have hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (Lvm.Q2.pinPt pin) := by rw [hzP]; rfl
  have hpinR : Lvm.Q2.FRel (memF TiF20 x qm qr) CMain.nu20 (.e3 pin)
      (BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memF TiF20 x qm qr) zP) (aP.val (memF TiF20 x qm qr))) := by
    refine ⟨?_, ?_⟩
    · rw [hzP]; simp [Lvm.Har.WF1, hzl]
    · rw [hzP, cclaim_point]
  -- the claims: the typed phases', then the front's
  have htrel : List.Forall₂ (Lvm.Q2.FRelZ (memF TiF20 x qm qr) (ec q2.e)
      (TypedV.smallT P20F (pubOfA accVF vk (hdrOf x).cL (sigCF qr)))) ((tc.1 ++ tc.2).map .e3)
      (TypedV.typedClaimsN NTF20 P20F (Lvm.Har.vs (memF TiF20 x qm qr) t.ry) (Lvm.Har.vs (memF TiF20 x qm qr) t.rv)
        (Lvm.Har.vs (memF TiF20 x qm qr) t.rr) (t.vR.val (memF TiF20 x qm qr)) ++
       Shape.zeroTails ((NTF20.m3 P20F).tableClaims (pubOfA accVF vk (hdrOf x).cL (sigCF qr))
         (t.tab.map fun e => (Lvm.Har.vs (memF TiF20 x qm qr) e.1, Lvm.Har.vs (memF TiF20 x qm qr) e.2)))) := by
    have hsh := typedGX_shape (c := ctxOf TiF20.Q) (M := memF TiF20 x qm qr) _ _ _ _ _ _ _ hTy.1
    rw [show cfgF20.p = P20F from rfl, show P20F.accV = accVF from rfl, ht] at hsh
    obtain ⟨hry, hrr, htabl⟩ := hsh
    rw [show cfgF20.p = P20F from rfl] at htc hTC
    have hok := typedClaimsC_ok (c := ctxOf TiF20.Q) (M := memF TiF20 x qm qr) (zc := ec q2.e) (nu := P20F.nuMain)
      rfl hTR hry hrr htabl _ hTC.1
    rw [htc] at hok
    obtain ⟨hl2, hcok⟩ := hok
    obtain ⟨T1, T2, -⟩ := Lvm.Har.typedClaimsC_val hzv hov htd P20F.nuMain (layout0 P20F).s t NTF20.mbT hSs _ hTC.1
    rw [htc] at T1 T2
    exact typed_relF hzv (by rw [Lvm.Har.m3_tableClaimsT, hsc]) T1 T2 hl2 hcok
  have hrel := List.rel_append htrel hfrel
  beta_reduce at hrel
  -- the opening's static inputs
  have hopenU : posOf P20F (phaseItem0 P20F .openMain) =
      8 * (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).U := by
    rw [cfgMainF_U]; exact hOU
  have hlayO : Lvm.Har.LayOk (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)) (streamLanes P20F) = true := by
    rw [layOkF_pb P20F _ _ (fun _ => 0) (fun _ => 0)]; exact hLY
  have hposO : Lvm.Har.PosOk (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)) (memF TiF20 x qm qr) (sigCF qr) 0
      (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).levels ((cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).U + 15) := by
    have hPL' : Lvm.Fin.PosLanes P20F (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).g
        (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).ood
        (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).levels
        ((cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).U + 15) 0 := by
      rw [cfgMainF_g, cfgMainF_ood, cfgMainF_levels, cfgMainF_U]; exact hPL
    exact posOk_ofG P20F cfgF20 rfl _ 0 (fun i => by rw [Nat.zero_add, cfgMainF_pb]) hPL' streamOk_P20F hLL hQF20
      (posCellsF S H hok hb hG)
  have hpwO : Lvm.Har.PwOk (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)) (memF TiF20 x qm qr) 0
      (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).levels := by
    intro i hi _
    rw [cfgMainF_levels] at hi
    rw [cfgMainF_pw, cfgMainF_g, Nat.zero_add]
    have e := pw_onC (outsOnF S H hG.1) hGR i (lt_of_lt_of_le hi hML)
    exact e
  have hendO : 8 * Lvm.Har.stackEndL (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).g
      (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).ood (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).levels
      ((cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).U + 15) = (sigCF qr).size := by
    rw [sigCF_size hLL, stackEnd_cfgMainF]; exact hSE
  have hq7 : 1 ≤ q7.e := by
    have h3 : 1 ≤ q3.e := le_trans (by simp) hq3e
    omega
  rw [show cfgF20.p = P20F from rfl] at hOpen
  -- `core_of_phasesF`, the opening by `open_phase`
  refine Lvm.Har.decideFFX_of (acc := (Lvm.VEq.pubXF x).accIn) P20F NTF20 vk (hdrOf x).cL _ ?_
    (phiF20_acc S H hG.1)
  refine Lvm.Har.core_of_phasesF P20F _ NTF20.m3 vk (hdrOf x).cL (sigCF qr) (RS.startH (headerBytesP P20F)) rfl hbF
    hpin htyped htape hcall hlink ?_
  intro s hs hsok
  rw [show P20F.accV = accVF from rfl]
  have key := Lvm.Q2.open_phase P20F (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)) rfl rfl rfl rfl rfl hF pin hpt _ _
    hpinR _ _ _ hrel o.mb hσ sK (kc (pbB cfgF20)) hsK hS hlayO (by rw [Cell.val_K, hg, ofK_one]) rfl hposO hpwO hendO
    hq7 hOpen s (hs.trans hopenU) hsok
  rw [hnu] at key
  exact key

end Lvm.E2Q
