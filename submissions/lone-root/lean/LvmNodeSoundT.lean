-- New for lvm2 (roll 8 = B1, L-D): `NodeSound` for the typed backend's good pair `GoodT` (B-DES §2). WP-14c's
-- `nodeSound_main` (`LvmNodeSoundMain`) restated on the B program `QB20` and the memory read off the pair's words
-- (`memOf layT20 (zOf …)`): `holds_of_wiring` replaces `segs_of_aux` (the bus's `loopir_sound`); Q_link's, Q_sig's and
-- `KS`'s theorems (`qlink_sound`, `qsig_sound_in`, `sigKSin_of_goodK`, `traceDigest_of_goodK`) are used as they are.
import LvmNodeSoundFields
import LvmNodeSoundTr
import LvmQAsmFactsL
import LvmQSigSound
import LvmCertTInst

/-!
# `NodeSound` for the typed backend

The B program at `P20` is `QB20 = Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0` (`QB20_qn`): Q_link, Q_sig, then
`qaB = phases47 cfg20 >>= qarithB cfg20 tdata20`. The typed instance `TiB = NT20.inst QB20 layT20` is V_S's; a
candidate pair's words are `zT x qm qr = TiB.zOf lay26 (pubX x) qm qr` and its memory `memT x qm qr = memOf layT20 (zT …)`.

* **`holds_memT`**: on a good pair, with the layout check (`StaticFactsT.hlay`) and `ReaddOk`, `QB20`'s rows hold and
  assert on `memT` (`holds_of_wiring`; the word `1` from `THyp.ok`). No interpreter is needed: the gadget theorems
  read any memory where the segments hold (`toProgram_holds`, `parts_of_holds`), so `typed_sound`'s `inb` is not
  needed here (`holds_of_wiring` takes the guard's `S.wf`).
* **`accV_childW_ofT`**: the left child is accepted by the typed `V_S` (`VST`'s replay, `drive_replay`).
* **`nodeSoundT`**: `NodeSound VSB20 vk (GoodT TiB H) childS` from the guard's facts `S`, and on a good node pair:
  `ReaddOk` on `memT` (`hrd`: the mini-bus and QLT's static reads), the input map on `memT` (`hmap`, `hqlt`: the
  layout's input regions through `zOf`, QLT's constants), the position bits (`hpos`) and Q_sig's `BITS` (`hbits`)
  (the typed `BITS` rows), and the B program's Q_arith (`harith`: `qaB`'s segments ⇒ `decideFT … = true`, the typed
  HAR).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig
open Lvm.TypedV (TNat decideFT)

/-! ## The typed `V_S` accepts a reassembled child -/

/-- **Replay of the typed `V_S`**: on a trace of the schedule whose reassembled proof passes the header checks,
`VST` asks exactly the trace and returns `decideFT` on its stream. -/
theorem VST_replay (p : Params) (N : TNat) (vk c : RecursionFast.Digest) (hP : PlanOk p) (tr : Trace) (hL : LinkOk p tr)
    (hparse : parseOk p vk c (reassemble p tr) = true) :
    (VST p N vk c (reassemble p tr)).runSeq tr = some (decideFT p N vk c (traceBytesB tr)) := by
  simp only [VST, hparse, ite_true]
  exact drive_replay p hP tr hL _

/-- **The left child is accepted by the typed `V_S`** (`accV_reassemble` with `VST_replay`). -/
theorem accV_reassembleT (p : Params) (N : TNat) (vk cL : RecursionFast.Digest) (tr : Trace) (σ : Sig)
    (hP : PlanOk p) (hq : (plan p).length ≤ qVlvm)
    (hcap : ∀ i < (plan p).length, ((plan p).getD i default).len ≤ queryCap)
    (hpi : piSize p < 2 ^ 64) (hL : LinkOk p tr)
    (hparse : parseOk p vk cL (reassemble p tr) = true)
    (hdec : decideFT p N vk cL (traceBytesB tr) = true)
    (hsig : SigOk vk (traceDigest tr) σ = true) :
    accV (VST p N) vk cL ⟨reassemble p tr, tr, σ⟩ = true := by
  have hsize : (reassemble p tr).size = piSize p := by
    simp only [parseOk, Bool.and_eq_true, beq_iff_eq] at hparse
    exact hparse.1.1.1
  have hrun := VST_replay p N vk cL hP tr hL hparse
  rw [hdec] at hrun
  obtain ⟨hn, hG⟩ := hL
  simp only [accV, accWith, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨by rw [hsize]; exact hpi, by rw [hn]; exact hq⟩, fun e he => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hGi := (hG i hi).1
    have hq1 : (qOf tr i) = tr[i].1 := by
      simp [qOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [← hq1, hGi]
    exact hcap i (hn ▸ hi)
  · rw [SigOkF_eq, traceDigestF_eq]; exact hsig
  · rw [V_S _ _ _ _ (isS_reassemble p tr)]; exact hrun

/-- **The left child is accepted by the typed `V_S`** from what the circuit's memory gives (`accV_childW_of` on
`VST`). -/
theorem accV_childW_ofT (hH : HdrBridge) (hT : TrBridge) (N : TNat) {M : Mem} {I : SigIn}
    (w : ℕ → Word) {vk cL : RecursionFast.Digest} {σl : Sig}
    (hlink : LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf w))))
    (harith : decideFT P20 N vk cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf w)))) = true)
    (hsig : SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true)
    (hchild : ChildOk I M.k) (hln : I.ln = 20)
    (hvk : digAt M.k I.vk = vk) (hcL : digAt M.k I.cL = cL) (hsl : sigAt' M.k I.sl = σl)
    (hmd : digAt M.k I.md = traceDigest (decode P20 (wsOf (Lvm.X.laneOf w))))
    (hsg : sigAt' M.k I.sg = Lvm.X.sigOfF (Lvm.X.sigCol w))
    (hhd : ∀ k < 615, M.k (I.hd + k) = laneK (wsOf (Lvm.X.laneOf w)) (11 + k))
    (hσl : SigOk vk (traceDigest []) σl = true) :
    accV (VST P20 N) vk cL (childW w) = true := by
  have hws : hashedLen P20 ≤ 8 * (wsOf (Lvm.X.laneOf w)).length := by
    rw [wsOf, List.length_map, List.length_range, sizes_P20.2.2.2.2.2.1]; norm_num
  unfold childW
  rw [hT]
  refine accV_reassembleT P20 N vk cL _ _ planOk_P20 (by rw [plan_P20]; decide) planCap_P20'
    (by rw [sizes_P20.1]; norm_num) hlink
    (hH M I _ vk cL σl hlink hws hhd hchild hln hvk hcL hsl hσl) harith ?_
  rw [← hsg, ← hmd, ← hvk]
  exact hsig

section Typed

open Lvm.Loop.Build Lvm.M3 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

/-! ## The parts on any memory where the program holds -/

/-- **The three parts' segments** on any memory where the node program's rows hold and assert. -/
theorem parts_of_holds {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ} {M : Mem}
    (hH : (Qn lay I qa nK nE).Holds M) (hA : (Qn lay I qa nK nE).Asserts M) :
    Ok (ctxOf (Qn lay I qa nK nE)) M (qlink P20 lay) (p0 nK nE) ∧
      Ok (ctxOf (Qn lay I qa nK nE)) M (qsig I) (p1 lay nK nE) ∧
      Ok (ctxOf (Qn lay I qa nK nE)) M qa (p2 lay I nK nE) := by
  rw [toProgram_holds] at hH
  rw [toProgram_asserts] at hA
  have e : qprog lay I qa = (qlink P20 lay >>= fun _ => (qsig I >>= fun _ => qa)) := rfl
  have hh : SegsHold (ctxOf (Qn lay I qa nK nE)) M (p0 nK nE) (qprog lay I qa (p0 nK nE)).2 := hH
  have ha : SegsAssert M (p0 nK nE) (qprog lay I qa (p0 nK nE)).2 := hA
  rw [e, hold_bind, hold_bind] at hh
  rw [e, assert_bind, assert_bind] at ha
  exact ⟨⟨hh.1, ha.1⟩, ⟨hh.2.1, ha.2.1⟩, ⟨hh.2.2, ha.2.2⟩⟩

/-! ## The B program at `P20` -/

/-- **Q_arith of the B program at `P20`**: phases 4–7, then `qarithB` (the typed verifier, the claims, the
openings). -/
abbrev qaB : BM Unit := Lvm.Har.phases47 cfg20 >>= qarithB cfg20 tdata20

theorem qprogB20 : qprogB cfg20 tdata20 = qprog (lay cfg20) (sigIn cfg20) qaB := rfl

/-- **The B program at `P20` is a node program** (Q_link, Q_sig, `qaB`). -/
theorem QB20_qn : QB20 = Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0 := by
  rw [QB20_eq]
  show toProgram (nK cfg20) 0 (qprogB cfg20 tdata20) = _
  rw [qprogB20]

/-- **The typed instance at `P20`**: V_S's `NT20` on the B program and its layout (L-W's `Ti20`). -/
noncomputable abbrev TiB : TInst := Lvm.CT.Ti20

/-- **A candidate pair's words** (statement `x`). -/
noncomputable def zT (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : ℕ → FK :=
  TiB.zOf lay26 (pubX x) qm qr

/-- **The memory read off a candidate pair's words.** -/
noncomputable def memT (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : Mem :=
  memOf layT20 (zT x qm qr)

theorem lay_TiB : TiB.lay = layT20 := rfl
theorem Q_TiB : TiB.Q = QB20 := rfl

/-- A candidate pair's word `1` holds `1` when the word lies in a `one` region (generic in the instance: the kernel
must not meet `zOf`'s match at the closed `TiB`). -/
theorem zOf_one (Ti : TInst) (h : Ti.src? Ti.lay.one = some .one) (L : Lvm.M3.Lay) (pub : Lvm.Pub)
    (qm : Column L.nuMain) (qr : Column L.nuRec) : Ti.zOf L pub qm qr Ti.lay.one = 1 := by
  unfold TInst.zOf
  rw [h]

/-- The word `1` holds `1` (`THyp.ok`: it lies in a `one` region). -/
theorem zT_one (H : THyp TiB) (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) :
    zT x qm qr layT20.one = 1 := by
  have h := zOf_one TiB H.ok.2 lay26 (pubX x) qm qr
  rw [lay_TiB] at h
  exact h

/-- **The good pair's halves**: the wiring relation on its words, the mini-bus, the boundary claims, the incoming
accumulator, the Keccak relations. -/
theorem goodT_wiring {H : THyp TiB} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) : WiringRel QB20 layT20 (zT x qm qr) := by
  have h := hG.1.1.1.1
  rw [Q_TiB, lay_TiB] at h
  exact h

/-- The Keccak half of a good pair with its boundary claims (`okS` bounds `n` by `2^20`). -/
theorem goodK_of {H : THyp TiB} {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20}
    {qr : Column 19} (hok : okS vk c x = true) (hG : GoodT TiB H x qm qr) : GoodK x (qm, qr) :=
  ⟨hG.2.1, hG.2.2, hG.1.1.2 (okS_n hok).2⟩

/-- **`QB20`'s rows hold and assert on the pair's memory** (`holds_of_wiring`). -/
theorem holds_memT {H : THyp TiB} (S : StaticFactsT cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20)
    {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} (hG : GoodT TiB H x qm qr)
    (hrd : ReaddOk QB20 (memT x qm qr)) :
    QB20.Holds (memT x qm qr) ∧ QB20.Asserts (memT x qm qr) :=
  holds_of_wiring QB20 layT20 (zT x qm qr) S.wf S.hlay (zT_one H x qm qr) (goodT_wiring hG) hrd

/-! ## `NodeSound` -/

/-- **The input map on a memory** (`InMapN`'s fields on any memory). -/
structure InMapM (lay : Layout) (I : SigIn) (M : Mem) (vk : RecursionFast.Digest) (x : List UInt8)
    (qm : Column CMain.nu20) (qr : Column 19) : Prop where
  /-- The stream lanes (Q_link's and Q_sig's stream region; `C_rec`'s stream columns). -/
  stream : ∀ j < 2 ^ lay.m, M.k (lay.sb + j) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j
  /-- Q_sig's gate is on. -/
  flag : M.k I.flag = 1
  /-- `KS`'s `X` message lanes on Q_sig's message cells. -/
  xs : ∀ r < 449, ∀ l < 17, M.k (I.xs + 17 * r + l) = FK.ofBF64 (msgX qm r l)
  /-- `KS`'s output lanes `0 … 3` on Q_sig's digest cells. -/
  ys : ∀ r < 399, ∀ l < 4, M.k (I.ys + 4 * r + l) = FK.ofBF64 (Yq qm (ksSplit P20 + r) l)
  yc : ∀ t ≤ 16, ∀ l < 4, M.k (I.yc + 4 * t + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 430 + t) l)
  yls : ∀ l < 4, M.k (I.yls + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 447) l)
  yns : ∀ l < 4, M.k (I.yns + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 448) l)
  /-- `PUB`: the key, the left statement, the leaf signature. -/
  vk : digAt M.k I.vk = vk
  cL : digAt M.k I.cL = (hdrOf x).cL
  sl : sigAt' M.k I.sl = (hdrOf x).sig
  /-- The trace-digest cells: `KS` row `B − 1`'s output lanes `0 … 3`. -/
  md : ∀ l < 4, M.k (I.md + l) = FK.ofBF64 (Yq qm (spongeBlocks P20 - 1) l)
  /-- `σ'`'s cells: `C_rec`'s column 17. -/
  sg : sigAt' M.k I.sg = Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol qr))
  /-- Q_sig's child-header cells are the stream's lanes `11 …`. -/
  hd : ∀ k < 615, M.k (I.hd + k) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) (11 + k)
  /-- The whole `PUB` array from `I.flag`: the header's lanes. -/
  pub : ∀ j < pubLanes, M.k (I.flag + j) = hdrLane x j

/-- The child's stream lanes of a `C_rec` candidate. -/
abbrev wsC (qr : Column 19) : List Word := wsOf (Lvm.X.laneOf (wOfCol qr))

/-- **`NodeSound` for the typed backend on any good relation `G` below `GoodT`** (R11-N, M′: `nodeT20` uses
`G = GoodT ∧ SBlk`; the hypotheses are asked on `G`'s pairs only). -/
theorem nodeSoundTG (vk : RecursionFast.Digest) (H : THyp TiB) (S : Lvm.CT.SF20) (G : GoodRel)
    (hGT : ∀ x qm qr, G x qm qr → GoodT TiB H x qm qr)
    (hrd : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ReaddOk QB20 (memT x qm qr))
    (hmap : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr)
    (hqlt : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ y < (qltData P20 (lay cfg20)).length,
        (memT x qm qr).k ((lay cfg20).qt + y) = (qltData P20 (lay cfg20)).getD y 0)
    (hpos : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t,
        ∀ z < ((opens P20).getD k default).L.height,
        (memT x qm qr).k (bitBase P20 (lay cfg20) k + ((opens P20).getD k default).L.height * j + z) =
          if ansBit P20 (wsC qr) (((opens P20).getD k default).pe + j / 8)
            (j % 8 * ((opens P20).getD k default).L.height + z) then 1 else 0)
    (hbits : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      SigBits (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 (memT x qm qr).k)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr →
      LaneLink P20 (wsC qr) → LinkOk P20 (decode P20 (wsC qr)) →
      Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)) (memT x qm qr) qaB
        (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0) →
      decideFT P20 NT20 vk (hdrOf x).cL (traceBytesB (decode P20 (wsC qr))) = true) :
    NodeSound VSB20 vk G childS := by
  refine nodeSound_of (fun c x qm qr hok hG ↦ chain_of_goodK hok (goodK_of hok (hGT _ _ _ hG)))
    fun c x qm qr hok hb hG' ↦ ?_
  have hG := hGT _ _ _ hG'
  have hK := goodK_of hok hG
  obtain ⟨hH, hA⟩ := holds_memT S.toStaticFactsT hG (hrd c x qm qr hok hb hG')
  have hinj := S.inj
  rw [QB20_qn] at hH hA hinj
  have P := parts_of_holds hH hA
  have mp := hmap c x qm qr hok hb hG'
  have hwsl : 2 ^ (lay cfg20).m ≤ (wsC qr).length := by
    rw [wsC, wsOf, List.length_map, List.length_range]; exact hws20
  have hqin : QIn P20 (lay cfg20) (wsC qr) (memT x qm qr) :=
    ⟨by rw [hfg20]; exact mp.flag, mp.stream, hqlt c x qm qr hok hb hG', hpos c x qm qr hok hb hG'⟩
  have hN : (ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)).cells .K ≤
      max ((Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0).cells .K)
        ((Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0).cells .E) := by
    rw [ctxOf_cells]; exact le_max_left _ _
  have hNs : (lay cfg20).sb + 2 ^ (lay cfg20).m ≤
      max ((Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0).cells .K)
        ((Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0).cells .E) :=
    le_trans (by decide : (lay cfg20).sb + 2 ^ (lay cfg20).m ≤ nK cfg20)
      (le_trans (nK_le_cells _ _ _) (le_max_left _ _))
  obtain ⟨hLL, hpad⟩ := qlink_sound hS20 hQ20 hqin hwsl hinj hN hNs P.1.1 P.1.2
  have hlink := linkOk_of_laneLink hS20 hLL
  have hks := sigKSin_of_goodK hK mp.xs mp.ys mp.yc mp.yls mp.yns
  obtain ⟨hsig, hchild⟩ := qsig_sound_in (by rw [hln20]; omega) P.2.1 mp.flag hks (hbits c x qm qr hok hb hG')
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h
  have hmd := (digAt_of_cells mp.md).trans (traceDigest_of_goodK hK hLL hpad)
  have har := harith c x qm qr hok hb hG' mp hLL hlink P.2.2
  exact accV_childW_ofT hdrBridge trBridge NT20 (wOfCol qr) hlink har hsig hchild hln20 mp.vk mp.cL mp.sl hmd
    mp.sg mp.hd (okS_sig hok hb)

/-- **`NodeSound` for the typed backend** (`nodeSound_main` on the B program at `P20`; see the module docstring). -/
theorem nodeSoundT (vk : RecursionFast.Digest) (H : THyp TiB) (S : Lvm.CT.SF20)
    (hrd : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      ReaddOk QB20 (memT x qm qr))
    (hmap : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr)
    (hqlt : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      ∀ y < (qltData P20 (lay cfg20)).length,
        (memT x qm qr).k ((lay cfg20).qt + y) = (qltData P20 (lay cfg20)).getD y 0)
    (hpos : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t,
        ∀ z < ((opens P20).getD k default).L.height,
        (memT x qm qr).k (bitBase P20 (lay cfg20) k + ((opens P20).getD k default).L.height * j + z) =
          if ansBit P20 (wsC qr) (((opens P20).getD k default).pe + j / 8)
            (j % 8 * ((opens P20).getD k default).L.height + z) then 1 else 0)
    (hbits : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      SigBits (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 (memT x qm qr).k)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodT TiB H x qm qr →
      InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr →
      LaneLink P20 (wsC qr) → LinkOk P20 (decode P20 (wsC qr)) →
      Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)) (memT x qm qr) qaB
        (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0) →
      decideFT P20 NT20 vk (hdrOf x).cL (traceBytesB (decode P20 (wsC qr))) = true) :
    NodeSound VSB20 vk (GoodT TiB H) childS :=
  nodeSoundTG vk H S _ (fun _ _ _ h ↦ h) hrd hmap hqlt hpos hbits harith

end Typed

end Lvm.NS
