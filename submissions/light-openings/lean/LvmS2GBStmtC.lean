-- New for lvm2 MP-B cap pruning (CAP-C2, 2026-11-17): DAY-0 STATEMENTS of the S2GB circuit (`harithB20`,
-- `nodeB20`). Every `sorry` is tagged `-- CAP-FRZ C2`; a proof never changes its statement (changes go to the lead).
import LvmS2GBGuardC
import LvmS2GSStmtC
import LvmS2GBTail
import LvmS2GBHarB
import LvmS2GBNodeLeft

/-!
# The circuit at S2GB

* `p2B20`: Q_arith's pointer (after Q_link at S2GB and `qsigSC`).
* **`harithB20`**: Q_arith is `V_S`'s decision at S2GB (`decideFBX`; `harithS20`'s twin).
* **`nodeB20`**: `NodeSoundS` at S2GB (`nodeS20`'s twin: `V_S` is `VSSB`, the good pair `GoodTSB`, the right
  leaf's signature from the circuit's second walk, `slM20`). The guard and the input map: `LvmS2GBGuardC`.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig

/-- **The left child of a stream block at S2GB** (RE-FREEZE R3: `childSP`'s twin with `reassembleB`: the static part
of π, then the π tail of the uncovered cap-layer nodes). -/
def childSPB (p : Params) (q : LeanVM.Protocol.Column 19) : Signed :=
  ⟨Lvm.Replay.reassembleB p (decode p (wsOf (Lvm.X.laneOf (wOfCol q)))), decode p (wsOf (Lvm.X.laneOf (wOfCol q))),
    Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol q))⟩

end Lvm.NS

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.QTyped Lvm.TypedV Lvm.BitsTab LeanVM.Protocol
open Lvm.E2T (TNatT PhiQGC)
open Lvm.E2U (SBlkU YqU MqU)
open Lvm.E2S (VSSB decideFBX THypSB GoodTSB)
open Lvm.CT (slM20)
open Lvm.ASM (okSL NodeSoundS)

/-- Q_arith's pointer at S2GB (after Q_link at S2GB and `qsigSC`). -/
def p2B20 : Ptr :=
  let p1 := (⟨nK cfgB20, 0⟩ : Ptr).adv (qlinkB cfgB20.p (lay cfgB20) ⟨nK cfgB20, 0⟩).2
  p1.adv (qsigSC (sigIn cfgB20) (sigInLC cfgB20) p1).2

/-- **CAP-FRZ C2**: **Q_arith is `V_S`'s decision at S2GB** (`harithS20`'s twin: the program's segments after Q_sig
on a good S2GB pair whose `qr` is `qm`'s stream block decide `decideFBX` on the child's trace bytes). -/
theorem harithB20 (S : NodeGB) (hhar : harChkBB20 = true) (hlin : Lvm.Typed.KT.linOkX cacheB20 = true)
    (H : THypSB TiB20) (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okSL vk c x = true → (hdrOf x).b = 1 →
      GoodTSB TiB20 H x qm qr ∧ SBlkU qm qr →
      InMapMBS (spongeBlocks P20B) (pubLanesS P20B) cfgB20 (memTX TiB20 Lvm.pubXTS x qm qr) vk x qm qr →
      LaneLink P20B (wsC qr) → LinkOk P20B (decode P20B (wsC qr)) →
      Ok (ctxOf TiB20.Q) (memTX TiB20 Lvm.pubXTS x qm qr) qaB20 p2B20 →
      decideFBX NTB20 vk (hdrOf x).cL (traceBytesB (decode P20B (wsC qr))) = true :=
  harithB20H S hhar hlin H vk

/-- The leaf walk's chain-end row (proof help, generic in `C`; `sigInLC_yc` of `LvmS2GSStmtC`). -/
private theorem sigInLC_ycB (C : QCfg) : (sigInLC C).yc = (sigInLC C).ys + 4 * (nStepRowsC + 31) := rfl

/-- **CAP-FRZ C2**: **`NodeSoundS` at S2GB** (`nodeS20`'s twin at `THypSB`, RE-FREEZE R1: `V_S` at S2GB, the good pair over the
S2GB tape; the right leaf's `σ_leaf` read off the candidate through `permC`, `slM20`). -/
theorem nodeB20 (S : SFB20) (H : THypSB (NTB20.inst QB20 layB20)) (vk : RecursionFast.Digest) :
    NodeSoundS (VSSB NTB20) vk (fun x qm qr ↦ GoodTSB (NTB20.inst QB20 layB20) H x qm qr ∧ SBlkU qm qr)
      (Lvm.NS.childSPB P20B) slM20 := by
  refine nodeSoundS_of (fun c x qm qr hok hG => ?_) (fun c x qm qr hok hb hG => ?_)
    (fun c x qm qr hok hb hG => ?_)
  · have hn := okSL_n hok
    exact Lvm.KG.chain_of_tape hn.1 hn.2 ⟨hG.1.2.1, hG.1.1.1.2 hn.2⟩
  · -- the left child: Q_link at S2GB, the first walk, Q_arith
    have S1 : NodeGB := S.1
    have H' : THypSB TiB20 := H
    have hG' : GoodTSB TiB20 H' x qm qr ∧ SBlkU qm qr := hG
    have hone : (NTB20.toN.instL Pub.hdrLanesT QB20 layB20).src? layB20.one = some .one := H.ok.2
    obtain ⟨hH, hA⟩ := hholdsCS S1 Pub.hdrLanesT Lvm.pubXTS cfgU_B20 hone (hWB S1 H' hG'.1) H'.hτ H'.layOk
      hG'.1.1.1.1.2 hG'.2
    have hH' : QB20.Holds (memTX TiB20 Lvm.pubXTS x qm qr) := hH
    have hA' : QB20.Asserts (memTX TiB20 Lvm.pubXTS x qm qr) := hA
    have hinj' : GInj (max (QB20.cells .K) (QB20.cells .E)) := S1.st.inj
    have hN : (ctxOf QB20).cells .K ≤ max (QB20.cells .K) (QB20.cells .E) := by
      rw [NS.ctxOf_cells]; exact le_max_left _ _
    have hNs : (lay cfgB20).sb + 2 ^ (lay cfgB20).m ≤ max (QB20.cells .K) (QB20.cells .E) :=
      le_trans (by decide) (le_trans S1.cells (le_max_left _ _))
    rw [QB20_eq] at hH' hA' hinj' hN hNs
    have P := parts_of_holdsB hH' hA'
    have mp := inMapB20 S1 H' vk c x qm qr hok hb hG'
    set M := memTX TiB20 Lvm.pubXTS x qm qr with hM
    have hwsl : 2 ^ (lay cfgB20).m ≤ (wsC qr).length := by
      rw [wsC, wsOf, List.length_map, List.length_range]; decide
    have hout : OutsOnC cfgB20 M.k := outsOnCS S1 Pub.hdrLanesT Lvm.pubXTS hone (hWB S1 H' hG'.1)
    have hpb : PosBits cfgB20.p (lay cfgB20) M.k := posBits_onC hout
    have hSt : StreamOkB cfgB20.p := streamOkB_P20B
    have hQ : QOkB cfgB20.p (lay cfgB20) := hQB20
    have hbit := qin_bitsB (ws := wsC qr) hSt hQ mp.stream hpb
    have hqin : QIn cfgB20.p (lay cfgB20) (wsC qr) M := ⟨mp.flag, mp.stream, hqltG cfgB20 _ S1.st.cst _, hbit⟩
    obtain ⟨hLLB, hpad⟩ := qlinkB_sound hSt hQ hqin hwsl hinj' hN hNs P.1.1 P.1.2
    have hLL := hLLB.base
    have hlink := linkOk_of_laneLinkB streamOkB_P20B hLLB
    -- the first walk
    have h1 := (Lvm.Har.okb P.2.1).1
    have hk : ksSplit cfgB20.p = ksSplit P20 := frontPF_P20B.ksSplit_eq.trans ksSplit_P20.symm
    have hx : ∀ r < 449, ∀ l < 17, M.k ((sigIn cfgB20).xs + 17 * r + l) = FK.ofBF64 (MqU qm (ksSplit P20 + r) l) :=
      fun r hr l hl ↦ by rw [mp.xs r hr l hl, hk]
    have hy : ∀ r < 449, ∀ l < 4, M.k ((sigIn cfgB20).ys + 4 * r + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l) :=
      fun r hr l hl ↦ by rw [mp.ys r hr l hl, hk]
    have hks := Lvm.E2U.sigKSin_of_GkL Lvm.E2S.contIvSB_ok.1 Lvm.E2S.contIvSB_ok.2.2.1 Lvm.E2S.contIvSB_ok.2.2.2.1
      hG.1.2 hx (fun r hr l hl ↦ hy r (by omega) l hl)
      (fun t ht l hl ↦ by
        rw [show (sigIn cfgB20).yc + 4 * t + l = (sigIn cfgB20).ys + 4 * (430 + t) + l by
          show ysQ cfgB20 + 4 * 430 + 4 * t + l = ysQ cfgB20 + 4 * (430 + t) + l; ring, hy _ (by omega) l hl,
          Nat.add_assoc])
      (fun l hl ↦ by
        rw [show (sigIn cfgB20).yls + l = (sigIn cfgB20).ys + 4 * 447 + l from rfl, hy _ (by omega) l hl])
      (fun l hl ↦ by
        rw [show (sigIn cfgB20).yns + l = (sigIn cfgB20).ys + 4 * 448 + l from rfl, hy _ (by omega) l hl])
    obtain ⟨hsig, hchild⟩ := qsigNoSl_sound (by rw [show (sigIn cfgB20).ln = 20 from rfl]; omega) h1 mp.flag hks
      (hbitsCSB (outsOnCS S1 Pub.hdrLanesT Lvm.pubXTS hone (hWB S1 H' hG'.1)) rfl rfl)
      fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h
    -- the trace digest
    have hmd : digAt M.k (sigIn cfgB20).md = traceDigest (decode P20B (wsC qr)) :=
      (digAt_of_cells mp.md).trans (Lvm.E2U.traceDigest_of_GkLB streamOkB_P20B Lvm.E2S.contIvSB_ok.1
        (fun i h1 h2 => Lvm.E2S.contIvSB_ok.2.1 i h1 (by have := Lvm.E2S.bB_eq; omega))
        (by rw [sizes_P20B.1.2.2.2.2.1, sizes_P20B.1.2.2.1]; rfl)
        (by rw [sizes_P20B.1.2.2.2.2.1]; norm_num) hG.1.2 hG.2 hLL hpad)
    have hqa : Ok (ctxOf TiB20.Q) M qaB20 p2B20H := by
      have h3 := P.2.2
      rw [← QB20_eq] at h3
      unfold p2B20H
      exact h3
    have har := harithB20H S1 S.2.1 S.2.2.2.1 H' vk c x qm qr hok hb hG' mp hLL hlink hqa
    have hparse := hdrBridgeB M (sigIn cfgB20) (wsC qr) vk (hdrOf x).cL hlink hLL.size
      (fun k hk => mp.hd k hk) hchild rfl mp.vk mp.cL
    exact accV_childB vk (hdrOf x).cL (decode P20B (wsC qr)) _ hlink hparse har
      (by rw [← mp.sg, ← hmd, ← mp.vk]; exact hsig)
  · -- the right leaf: the second walk
    have S1 : NodeGB := S.1
    have H' : THypSB TiB20 := H
    have hG' : GoodTSB TiB20 H' x qm qr ∧ SBlkU qm qr := hG
    have hone : (NTB20.toN.instL Pub.hdrLanesT QB20 layB20).src? layB20.one = some .one := H.ok.2
    obtain ⟨hH, hA⟩ := hholdsCS S1 Pub.hdrLanesT Lvm.pubXTS cfgU_B20 hone (hWB S1 H' hG'.1) H'.hτ H'.layOk
      hG'.1.1.1.1.2 hG'.2
    have hH' : QB20.Holds (memTX TiB20 Lvm.pubXTS x qm qr) := hH
    have hA' : QB20.Asserts (memTX TiB20 Lvm.pubXTS x qm qr) := hA
    rw [QB20_eq] at hH' hA'
    have P := parts_of_holdsB hH' hA'
    obtain ⟨h1, h2⟩ := Lvm.Har.okb P.2.1
    obtain ⟨h2, -⟩ := Lvm.Har.okb h2
    have mp := inMapB20 S1 H' vk c x qm qr hok hb hG'
    set M := memTX TiB20 Lvm.pubXTS x qm qr with hM
    set p1 := p1PB (lay cfgB20) (nK cfgB20) 0 cfgB20.p with hp1
    -- `Zn` is zero
    have hZ : M.k (qsigNoSl (sigIn cfgB20) p1).1.pre.1.n = 0 := by
      obtain ⟨⟨q, hq, e⟩, -⟩ := qsigNoSl_parts h1
      have := gPre_spec hq.1
      rw [e] at this
      exact this.2.2.1
    have hw := contIvSB_w2
    have hks := Lvm.E2U.sigKSinC_of_GkL (I := sigInLC cfgB20) (v := M.k) hw.1 Lvm.E2S.contIvSB_ok.1 hw.2.1 hw.2.2
      hG.1.2 mp.xsL mp.ysL (sigInLC_ycB cfgB20)
    have hpa : (sigOutSC cfgB20).2.pa = (qsigC (sigInLC cfgB20) (qsigNoSl (sigIn cfgB20) p1).1.pre.1.n
        (p1.adv (qsigNoSl (sigIn cfgB20) p1).2)).1.pa := by
      rw [sigOutSC, p1C_of_pr cfgB20 rfl]
      simp only [qsigSC, out_bind_eq, pure_apply_eq]
      rfl
    have hbits : SigBitsC (sigInLC cfgB20) (qsigC (sigInLC cfgB20) (qsigNoSl (sigIn cfgB20) p1).1.pre.1.n
        (p1.adv (qsigNoSl (sigIn cfgB20) p1).2)).1.pa M.k := by
      rw [← hpa]
      refine sigBitsC_of_outs M.k (sigInLC cfgB20) _ (fun k => bplOf noData (8 + nPosCls cfgB20 + k))
        (bspecs cfgB20 noData) (fun B hB => ?_) (outsOnCS S1 Pub.hdrLanesT Lvm.pubXTS hone (hWB S1 H' hG'.1))
      unfold bspecs
      rw [if_pos (show cfgB20.p.leafOut = true from rfl)]
      exact List.mem_append_right _ (List.mem_append_right _ hB)
    have hsig := qSigLeaf_sound h2 mp.flag hZ hks hbits
    have hvk : digAt M.k (sigInLC cfgB20).vk = vk := mp.vk
    rw [hvk, mp.sl] at hsig
    exact hsig

/-- **CAP-FRZ C2** (RE-FREEZE R3; proof owner X, `childS20_win`'s): **S2GB's left child from its window is the stream
block's** (`childB20` on the window = `childSPB P20B` on the candidate's stream block). -/
theorem childB20_win (x : List UInt8) (q : Column CMain.nu20) :
    Lvm.XB.childB20 x (Lvm.X.winOfL (Lvm.CT.loU x) q) = Lvm.NS.childSPB P20B (Lvm.E2U.recOfU20 x q) := by
  rw [Lvm.XB.childB20, Lvm.CT.winWU20, Lvm.XB.childWB, Lvm.XS.trBridgeS Lvm.XB.stB20 Lvm.XB.outOK_stB20]
  rfl

end Lvm.E2Q
