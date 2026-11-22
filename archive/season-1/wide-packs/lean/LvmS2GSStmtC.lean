-- New for lvm2 σ_LEAF (SLF-C, 2026-11-16): DAY-0 STATEMENTS of the S2GS circuit (SLF-STMT 7e `harithS20`, 7f `nodeS20`).
-- Every `sorry` is tagged `-- SLF-STMT 7<x>`; a proof never changes its statement (changes go to the lead, old → new).
import LvmS2GSGuardC
import LvmS2GSHar

/-!
# The circuit at S2GS (SLF-STMT 7e, 7f)

* `p2S20`: Q_arith's pointer (after Q_link and `qsigSC`).
* **`harithS20`** (7e): Q_arith is `V_S`'s decision at S2GS (`harithS20H`, `LvmS2GSHar`).
* **`sigKSinC_of_GkL`**: the leaf walk's `KS` rows from the merged tape (`sigKSin_of_GkL`'s twin for walk 2).
* **`hdrBridgeS`**, **`accV_reassembleDS`**: `ChildOkS` on the 18 header lanes is `parseOkS` on the reassembled child;
  the left child is accepted by a `V_S` of the S2GS shape.
* **`nodeS20`** (7f): `NodeSoundS` at S2GS, the right leaf's signature from the circuit's second walk (`slM20`).
  The guard and the input map: `LvmS2GSGuardC`.
-/

set_option autoImplicit false

namespace Lvm.E2U

open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- A `KS` row absorbs the `X` cells (`xorMsg_cellsU` at any row `R`). -/
theorem xorMsg_cellsR {qm : Column CMain.nu20} {v : ℕ → FK} {f : ℕ → ℕ} {R : ℕ}
    (h : ∀ l < 17, v (f l) = FK.ofBF64 (MqU qm R l)) (a : RecursionFast.Keccak.State) :
    Lvm.KSponge.xorMsg a (Lvm.Wots.laneByte (Lvm.QSig.lanesW v f)) = Lvm.KSponge.xorMsg a (Lvm.KG.msgBytes (MqU qm) R) := by
  have e : Lvm.KSponge.rateArr (Lvm.Wots.laneByte (Lvm.QSig.lanesW v f)) =
      Lvm.KSponge.rateArr (Lvm.KG.msgBytes (MqU qm) R) := by
    unfold Lvm.KSponge.rateArr
    congr 1
    funext j
    have hj : j.val < 136 := j.2
    simp only [Lvm.Wots.laneByte, Lvm.QSig.lanesW, Lvm.KG.msgBytes]
    rw [h _ (by (clear * - hj; omega))]
    rfl
  simp only [Lvm.KSponge.xorMsg, e]

/-- **The leaf walk's `KS` inputs over `iv`** (`sigKSin_of_GkL`'s twin for walk 2): its `nStepRowsC + 48` rows from
`a0` (the padded steps, the key leaf, the path) continue exactly on the key leaf's rows `nStepRowsC + 1 … + 31`. -/
theorem sigKSinC_of_GkL {iv : List (ℕ × ℕ)} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} {I : SigIn}
    {v : ℕ → FK} {a0 : ℕ} (hrow : a0 + (nStepRowsC + 48) ≤ 2 ^ 13) (h0 : contL iv 0 = false)
    (hcF : ∀ r, r < nStepRowsC + 48 → ¬ (nStepRowsC + 1 ≤ r ∧ r ≤ nStepRowsC + 31) → contL iv (a0 + r) = false)
    (hcT : ∀ r, nStepRowsC + 1 ≤ r → r ≤ nStepRowsC + 31 → contL iv (a0 + r) = true)
    (hG : GkL iv x (qm, qr))
    (hx : ∀ r < nStepRowsC + 48, ∀ l < 17, v (I.xs + 17 * r + l) = FK.ofBF64 (MqU qm (a0 + r) l))
    (hys : ∀ r < nStepRowsC + 48, ∀ l < 4, v (I.ys + 4 * r + l) = FK.ofBF64 (YqU qm (a0 + r) l))
    (hyc : I.yc = I.ys + 4 * (nStepRowsC + 31)) :
    SigKSinC I v := by
  have hr : ∀ r < nStepRowsC + 48, a0 + r < 2 ^ 13 := fun r h => by omega
  have H := spongeRel_of_GkL h0 hG
  have one : ∀ r < nStepRowsC + 48, ¬ (nStepRowsC + 1 ≤ r ∧ r ≤ nStepRowsC + 31) →
      OneHash v (fun l => I.xs + 17 * r + l) (I.ys + 4 * r) := fun r h hn =>
    ⟨yState (YqU qm) (a0 + r), by
      rw [xorMsg_cellsR (qm := qm) (R := a0 + r) (fun l hl => hx r h l hl)]
      exact oneRow_perm 13 _ (YqU qm) (MqU qm) _ H (hr r h) (hcF r h hn),
      digAt_of_cells (hys r h)⟩
  refine ⟨fun r h => one r (by omega) (by omega), ?_, fun t ht => ?_⟩
  · refine ⟨fun u => prevState (YqU qm) (contL iv) (a0 + (nStepRowsC + u)),
      fun u => yState (YqU qm) (a0 + (nStepRowsC + u)), ?_, fun u hu => ?_, fun u hu => ?_, ?_⟩
    · simp only [prevState, hcF (nStepRowsC + 0) (by omega) (by omega)]; rfl
    · rw [xorMsg_cellsR (qm := qm) (R := a0 + (nStepRowsC + u)) (fun l hl => hx _ (by omega) l hl)]
      exact row_perm 13 _ (YqU qm) (MqU qm) _ H (hr _ (by omega))
    · simp only [prevState, hcT (nStepRowsC + (u + 1)) (by omega) (by omega), if_true]
      rw [show a0 + (nStepRowsC + (u + 1)) - 1 = a0 + (nStepRowsC + u) by omega]
    · rw [hyc]; exact digAt_of_cells (hys _ (by omega))
  · have := one (nStepRowsC + 32 + t) (by omega) (by omega)
    rwa [show I.ys + 4 * (nStepRowsC + 32 + t) = I.yc + 4 * (t + 1) by rw [hyc]; omega] at this

end Lvm.E2U

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig Lvm.Wots Lvm.Bits Lvm.ASM

section HdrS

variable {π : ByteArray} {V : ℕ → UInt64}

theorem u64At_ofS (hB : ∀ k < 18, ∀ t < 8, π.get! (8 + 8 * k + t) = byteW (V k) t) {k : ℕ} (hk : k < 18) :
    u64At π (8 + 8 * k) = (V k).toNat := by
  rw [QLink.u64At_eq]
  have e : (List.range 8).map (fun i => π.get! (8 + 8 * k + i)) = enc64 (V k).toNat := by
    refine List.ext_getElem (by simp [enc64]) fun i h1 _ => ?_
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, hB k hk i h1, byteW_toNat _ h1]
    simp only [enc64, List.getElem_ofFn]
  rw [e, ofLE_enc64, Nat.mod_eq_of_lt (UInt64.toNat_lt _)]

theorem digestAt_ofS (hB : ∀ k < 18, ∀ t < 8, π.get! (8 + 8 * k + t) = byteW (V k) t) {k : ℕ}
    (hk : k + 4 ≤ 18) : digestAt π (8 + 8 * k) = digOfW fun l => V (k + l) := by
  refine Vector.ext fun i hi => ?_
  rw [digOfW_get _ hi]
  simp only [digestAt, Vector.getElem_ofFn]
  rw [show 8 + 8 * k + i = 8 + 8 * (k + i / 8) + i % 8 by omega, hB _ (by omega) _ (Nat.mod_lt _ (by omega))]

/-- **`parseOkS` from the header lanes** (`parseOk_of_lanesP`'s twin at S2GS: the 18 lanes before `acc_in`). -/
theorem parseOkS_of_lanes {p : Params} (hlog : p.logN = 20) {M : Mem} {I : SigIn} {vk cL : RecursionFast.Digest}
    (hsize : π.size = piSize p) (h0 : π.get! 0 = 0x53) (hz : ∀ i, 1 ≤ i → i < 8 → π.get! i = 0)
    (hB : ∀ k < 18, ∀ t < 8, π.get! (8 + 8 * k + t) = byteW (M.k (I.hd + k)).val t)
    (hchild : ChildOkS I M.k) (hln : I.ln = 20) (hvk : digAt M.k I.vk = vk) (hcL : digAt M.k I.cL = cL) :
    parseOkS p vk cL π = true := by
  have hdig : ∀ k, k + 4 ≤ 18 → digestAt π (8 + 8 * k) = digAt M.k (I.hd + k) := by
    intro k hk
    rw [digestAt_ofS hB hk, digAt]
    congr 1; funext l; rw [Nat.add_assoc]
  have hu : ∀ k < 18, u64At π (8 + 8 * k) = (M.k (I.hd + k)).val.toNat := fun k hk => u64At_ofS hB hk
  have hH : Header.ofProof π = ⟨(M.k I.hd).val.toNat, digAt M.k (I.hd + 1), digAt M.k (I.hd + 5),
      digAt M.k (I.hd + 9), (M.k (I.hd + 13)).val.toNat, digAt M.k (I.hd + 14), sigAt π offSig⟩ := by
    simp only [Header.ofProof]
    rw [show offB = 8 + 8 * 0 from rfl, hu 0 (by omega), show offVk = 8 + 8 * 1 from rfl, hdig 1 (by omega),
      show offCL = 8 + 8 * 5 from rfl, hdig 5 (by omega), show offS = 8 + 8 * 9 from rfl, hdig 9 (by omega),
      show offN = 8 + 8 * 13 from rfl, hu 13 (by omega), show offH = 8 + 8 * 14 from rfl, hdig 14 (by omega),
      Nat.add_zero]
  have hz17 : zeroBytes π 1 7 = true := zeroBytes_of fun i hi => hz _ (by omega) (by omega)
  obtain ⟨hb, hvk', hn1, hnL, h0c, hst⟩ := hchild
  rw [hln] at hnL
  simp only [parseOkS, hsize, hH, h0, hz17, hlog, Header.stmt, Header.leaf, leafStmtF_eq,
    nodeStmtF_eq, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  rw [← hcL, hst]
  refine ⟨⟨⟨⟨⟨hb, hvk'.trans hvk⟩, hn1⟩, hnL⟩, hnL⟩, ?_⟩
  rcases hb with hb | hb
  · have hz0 : zeroDig = zeroDigest := rfl
    simp only [hb, ↓reduceIte, h0c hb, hz0, beq_self_eq_true, Bool.and_self]
  · simp only [hb, one_ne_zero, ↓reduceIte, beq_self_eq_true]

/-- **The header bridge at S2GS** (`hdrBridgeP`'s twin: `ChildOkS` on the stream's 18 header lanes is `parseOkS` on
the reassembled child). -/
theorem hdrBridgeS (p : Params) (hlog : p.logN = 20) (hn : ∀ e ∈ plan p, nodeLenOk e = true)
    (hc : 8 + ((plan p).map clen).sum = piSize p) (hH : 6064 ≤ hashedLen p) (hseed : 176 ≤ seedLenP p) :
    ∀ (M : Mem) (I : SigIn) (ws : List Word) (vk cL : RecursionFast.Digest),
      LinkOk p (decode p ws) → hashedLen p ≤ 8 * ws.length →
      (∀ k < 18, M.k (I.hd + k) = laneK ws (11 + k)) → ChildOkS I M.k → I.ln = 20 →
      digAt M.k I.vk = vk → digAt M.k I.cL = cL →
      parseOkS p vk cL (reassemble p (decode p ws)) = true := by
  intro M I ws vk cL hlink hsz hhd hchild hln hvk hcL
  refine parseOkS_of_lanes hlog (size_reassembleP hn hc hlink) (reassemble_get0 _ _)
    (fun i h1 h8 => reassemble_get_hdr _ _ h1 h8) (fun k hk t ht => ?_) hchild hln hvk hcL
  rw [hhd k hk, Nat.add_assoc, reassemble_byteP hH hsz (by omega) (by omega),
    show 88 + (8 * k + t) = 8 * (11 + k) + t by omega,
    byte_of_lane ws _ _ ht, byteW_toNat _ ht, laneK_val, RecursionFast.toUInt8_mod]

/-- **The left child is accepted** by a `V_S` of the S2GS shape (`parseOkS`, then the driver; `accV_reassembleD`'s
twin). -/
theorem accV_reassembleDS (VS : SProg) (p : Params) (D : Digest → Digest → ByteArray → Bool)
    (hVS : ∀ vk c π, VS vk c π = if parseOkS p vk c π then drive p π (D vk c) else .ret false)
    (vk cL : Digest) (tr : Trace) (σ : Sig)
    (hP : PlanOk p) (hq : (plan p).length ≤ qVlvm)
    (hcap : ∀ i < (plan p).length, ((plan p).getD i default).len ≤ queryCap)
    (hpi : piSize p < 2 ^ 64) (hL : LinkOk p tr)
    (hparse : parseOkS p vk cL (reassemble p tr) = true)
    (hdec : D vk cL (traceBytesB tr) = true)
    (hsig : SigOk vk (traceDigest tr) σ = true) :
    accV VS vk cL ⟨reassemble p tr, tr, σ⟩ = true := by
  have hsize : (reassemble p tr).size = piSize p := by
    simp only [parseOkS, Bool.and_eq_true, beq_iff_eq] at hparse
    exact hparse.1.1.1
  have hrun : (VS vk cL (reassemble p tr)).runSeq tr = some true := by
    rw [hVS, hparse, if_pos rfl, drive_replayP p hP tr hL, hdec]
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

end HdrS

end Lvm.NS


namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.QTyped Lvm.TypedV Lvm.BitsTab LeanVM.Protocol
open Lvm.E2T (TNatT PhiQGC)
open Lvm.E2U (SBlkU YqU MqU)
open Lvm.E2S (VSSX decideFSX THypS GoodTS)
open Lvm.CT (slM20)
open Lvm.ASM (okSL NodeSoundS)

/-! ## Q_arith and the node -/

/-- Q_arith's pointer at S2GS (after Q_link and `qsigSC`). -/
def p2S20 : Ptr :=
  let p1 := (⟨nK cfgS20, 0⟩ : Ptr).adv (qlink cfgS20.p (lay cfgS20) ⟨nK cfgS20, 0⟩).2
  p1.adv (qsigSC (sigIn cfgS20) (sigInLC cfgS20) p1).2

/-- **SLF-STMT 7e** (owner C): **Q_arith is `V_S`'s decision at S2GS** (`harithL20`'s twin: the program's segments
after Q_sig on a good S2GS pair whose `qr` is `qm`'s stream block). -/
theorem harithS20 (S : NodeGS) (hhar : harChkBS20 = true) (hlin : Lvm.Typed.KT.linOkX cacheS20 = true)
    (H : THypS TiS20) (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okSL vk c x = true → (hdrOf x).b = 1 →
      GoodTS TiS20 H x qm qr ∧ SBlkU qm qr →
      InMapMBS (spongeBlocks P20S) (pubLanesS P20S) cfgS20 (memTX TiS20 Lvm.pubXTS x qm qr) vk x qm qr →
      LaneLink P20S (wsC qr) → LinkOk P20S (decode P20S (wsC qr)) →
      Ok (ctxOf TiS20.Q) (memTX TiS20 Lvm.pubXTS x qm qr) qaS20 p2S20 →
      decideFSX NTS20 vk (hdrOf x).cL (traceBytesB (decode P20S (wsC qr))) = true := by
  exact harithS20H S hhar hlin H vk

/-! ## 7f: the node at S2GS -/

/-- `okSL`'s chain-length bounds. -/
theorem okSL_n {vk c : RecursionFast.Digest} {x : List UInt8} (hok : okSL vk c x = true) :
    1 ≤ (hdrOf x).n ∧ (hdrOf x).n ≤ 2 ^ 20 := by
  unfold okSL at hok
  generalize hdrOf x = hd at hok ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact ⟨hok.1.1.2, hok.1.2⟩

/-- The leaf walk's rows `w2RowC cfgS20 + r` continue exactly on its key leaf's rows. -/
theorem contIvS_w2 : w2RowC cfgS20 + (nStepRowsC + 48) ≤ 2 ^ 13 ∧
    (∀ r, r < nStepRowsC + 48 → ¬ (nStepRowsC + 1 ≤ r ∧ r ≤ nStepRowsC + 31) →
      Lvm.E2U.contL (Lvm.E2S.contIvS Lvm.E2S.aSP) (w2RowC cfgS20 + r) = false) ∧
    (∀ r, nStepRowsC + 1 ≤ r → r ≤ nStepRowsC + 31 →
      Lvm.E2U.contL (Lvm.E2S.contIvS Lvm.E2S.aSP) (w2RowC cfgS20 + r) = true) := by
  have hw : w2RowC cfgS20 = 7280 := by rw [w2RowC, nStepRowsC_eq]; decide
  rw [hw, nStepRowsC_eq]
  refine ⟨by norm_num, fun r h1 h2 => ?_, fun r h1 h2 => ?_⟩
  all_goals
    unfold Lvm.E2S.bS Lvm.E2S.aSP at *
    simp only [Lvm.E2U.contL, Lvm.E2S.contIvS, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
      Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not, Lvm.E2S.bS]
    omega

/-- The leaf walk's chain-end row (proof help, generic in `C` so the kernel never evaluates `nStepRowsC`). -/
private theorem sigInLC_yc (C : QCfg) : (sigInLC C).yc = (sigInLC C).ys + 4 * (nStepRowsC + 31) := rfl

/-- **SLF-STMT 7f** (owner C): **`NodeSoundS` at S2GS** (`nodeL20`'s twin at `THypS`; the right leaf's `σ_leaf` read
off the candidate through `permC`, `slM20`, signs `traceDigest []` by the circuit's second walk). -/
theorem nodeS20 (S : SFS20) (H : THypS (NTS20.inst QS20 layS20)) (vk : RecursionFast.Digest) :
    NodeSoundS (VSSX NTS20) vk (fun x qm qr ↦ GoodTS (NTS20.inst QS20 layS20) H x qm qr ∧ SBlkU qm qr)
      (Lvm.NS.childSP P20S) slM20 := by
  refine nodeSoundS_of (fun c x qm qr hok hG => ?_) (fun c x qm qr hok hb hG => ?_)
    (fun c x qm qr hok hb hG => ?_)
  · have hn := okSL_n hok
    exact Lvm.KG.chain_of_tape hn.1 hn.2 ⟨hG.1.2.1, hG.1.1.1.2 hn.2⟩
  · -- the left child: Q_link, the first walk, Q_arith
    have S1 : NodeGS := S.1
    have H' : THypS TiS20 := H
    have hG' : GoodTS TiS20 H' x qm qr ∧ SBlkU qm qr := hG
    have hone : (NTS20.toN.instL Pub.hdrLanesT QS20 layS20).src? layS20.one = some .one := H.ok.2
    obtain ⟨hH, hA⟩ := hholdsCS S1 Pub.hdrLanesT Lvm.pubXTS cfgU_S20 hone (hWS S1 H' hG'.1) H'.hτ H'.layOk
      hG'.1.1.1.1.2 hG'.2
    have hH' : QS20.Holds (memTX TiS20 Lvm.pubXTS x qm qr) := hH
    have hA' : QS20.Asserts (memTX TiS20 Lvm.pubXTS x qm qr) := hA
    have hinj' : GInj (max (QS20.cells .K) (QS20.cells .E)) := S1.st.inj
    have hN : (ctxOf QS20).cells .K ≤ max (QS20.cells .K) (QS20.cells .E) := by
      rw [NS.ctxOf_cells]; exact le_max_left _ _
    have hNs : (lay cfgS20).sb + 2 ^ (lay cfgS20).m ≤ max (QS20.cells .K) (QS20.cells .E) :=
      le_trans (by decide) (le_trans S1.cells (le_max_left _ _))
    rw [QS20_eq] at hH' hA' hinj' hN hNs
    have P := parts_of_holdsS hH' hA'
    have mp := inMapS20 S1 H' vk c x qm qr hok hb hG'
    set M := memTX TiS20 Lvm.pubXTS x qm qr with hM
    have hwsl : 2 ^ (lay cfgS20).m ≤ (wsC qr).length := by
      rw [wsC, wsOf, List.length_map, List.length_range]; decide
    have hqin : QIn cfgS20.p (lay cfgS20) (wsC qr) M :=
      ⟨mp.flag, mp.stream, hqltG cfgS20 _ S1.st.cst _,
        hposCS S1 Pub.hdrLanesT Lvm.pubXTS streamOk_P20S hQS20 hone (hWS S1 H' hG'.1) mp.stream⟩
    obtain ⟨hLL, hpad⟩ := qlink_sound streamOk_P20S hQS20 hqin hwsl hinj' hN hNs P.1.1 P.1.2
    have hlink := linkOk_of_laneLink streamOk_P20S hLL
    -- the first walk
    have h1 := (Lvm.Har.okb P.2.1).1
    have hk : ksSplit cfgS20.p = ksSplit P20 := by decide
    have hx : ∀ r < 449, ∀ l < 17, M.k ((sigIn cfgS20).xs + 17 * r + l) = FK.ofBF64 (MqU qm (ksSplit P20 + r) l) :=
      fun r hr l hl ↦ by rw [mp.xs r hr l hl, hk]
    have hy : ∀ r < 449, ∀ l < 4, M.k ((sigIn cfgS20).ys + 4 * r + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l) :=
      fun r hr l hl ↦ by rw [mp.ys r hr l hl, hk]
    have hks := Lvm.E2U.sigKSin_of_GkL Lvm.E2S.contIvS_ok.1 Lvm.E2S.contIvS_ok.2.2.1 Lvm.E2S.contIvS_ok.2.2.2.1
      hG.1.2 hx (fun r hr l hl ↦ hy r (by omega) l hl)
      (fun t ht l hl ↦ by
        rw [show (sigIn cfgS20).yc + 4 * t + l = (sigIn cfgS20).ys + 4 * (430 + t) + l by
          show ysQ cfgS20 + 4 * 430 + 4 * t + l = ysQ cfgS20 + 4 * (430 + t) + l; ring, hy _ (by omega) l hl,
          Nat.add_assoc])
      (fun l hl ↦ by
        rw [show (sigIn cfgS20).yls + l = (sigIn cfgS20).ys + 4 * 447 + l from rfl, hy _ (by omega) l hl])
      (fun l hl ↦ by
        rw [show (sigIn cfgS20).yns + l = (sigIn cfgS20).ys + 4 * 448 + l from rfl, hy _ (by omega) l hl])
    obtain ⟨hsig, hchild⟩ := qsigNoSl_sound (by rw [show (sigIn cfgS20).ln = 20 from rfl]; omega) h1 mp.flag hks
      (hbitsCS S1 Pub.hdrLanesT Lvm.pubXTS rfl hone (hWS S1 H' hG'.1))
      fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h
    -- the trace digest
    have hbS := Lvm.E2S.bS_eq
    have hmd : digAt M.k (sigIn cfgS20).md = traceDigest (decode P20S (wsC qr)) :=
      (digAt_of_cells mp.md).trans (Lvm.E2U.traceDigest_of_GkL streamOk_P20S Lvm.E2S.contIvS_ok.1
        (fun i h1 h2 => Lvm.E2S.contIvS_ok.2.1 i h1 (by omega))
        (by rw [sizes_P20S.1.2.2.2.2.1, sizes_P20S.1.2.2.1]; rfl)
        (by rw [sizes_P20S.1.2.2.2.2.1]; norm_num) hG.1.2 hG.2 hLL hpad)
    have hqa : Ok (ctxOf TiS20.Q) M qaS20 p2S20H := by
      have h3 := P.2.2
      have hp : p1P (lay cfgS20) (nK cfgS20) 0 cfgS20.p =
          (⟨nK cfgS20, 0⟩ : Ptr).adv (qlink cfgS20.p (lay cfgS20) ⟨nK cfgS20, 0⟩).2 := rfl
      rw [← QS20_eq, hp] at h3
      unfold p2S20H
      exact h3
    have har := harithS20H S1 S.2.1 S.2.2.2.1 H' vk c x qm qr hok hb hG' mp hLL hlink hqa
    -- the plan's facts at `P20S`
    have hstat := plan_static_ofR passR_P20S sizes_P20S.1.1
    have hparse := hdrBridgeS P20S rfl hstat.1 hstat.2 (by rw [sizes_P20S.1.2.2.1]; norm_num) (by decide)
      M (sigIn cfgS20) (wsC qr) vk (hdrOf x).cL hlink
      (by rw [sizes_P20S.1.2.2.1, wsC, wsOf, List.length_map, List.length_range]; norm_num)
      (fun k hk => mp.hd k hk) hchild rfl mp.vk mp.cL
    exact accV_reassembleDS (VSSX NTS20) P20S (decideFSX NTS20) (fun _ _ _ => rfl) vk (hdrOf x).cL
      (decode P20S (wsC qr)) _ planSt_P20S.1
      (by rw [(Lvm.PlanChk.sound_of passR_P20S).2.2.1]; decide) (planCap_ofR passR_P20S)
      (by rw [sizes_P20S.1.1]; norm_num) hlink hparse har (by rw [← mp.sg, ← hmd, ← mp.vk]; exact hsig)
  · -- the right leaf: the second walk
    have S1 : NodeGS := S.1
    have H' : THypS TiS20 := H
    have hG' : GoodTS TiS20 H' x qm qr ∧ SBlkU qm qr := hG
    have hone : (NTS20.toN.instL Pub.hdrLanesT QS20 layS20).src? layS20.one = some .one := H.ok.2
    obtain ⟨hH, hA⟩ := hholdsCS S1 Pub.hdrLanesT Lvm.pubXTS cfgU_S20 hone (hWS S1 H' hG'.1) H'.hτ H'.layOk
      hG'.1.1.1.1.2 hG'.2
    have hH' : QS20.Holds (memTX TiS20 Lvm.pubXTS x qm qr) := hH
    have hA' : QS20.Asserts (memTX TiS20 Lvm.pubXTS x qm qr) := hA
    rw [QS20_eq] at hH' hA'
    have P := parts_of_holdsS hH' hA'
    obtain ⟨h1, h2⟩ := Lvm.Har.okb P.2.1
    obtain ⟨h2, -⟩ := Lvm.Har.okb h2
    have mp := inMapS20 S1 H' vk c x qm qr hok hb hG'
    set M := memTX TiS20 Lvm.pubXTS x qm qr with hM
    set p1 := p1P (lay cfgS20) (nK cfgS20) 0 cfgS20.p with hp1
    -- `Zn` is zero
    have hZ : M.k (qsigNoSl (sigIn cfgS20) p1).1.pre.1.n = 0 := by
      obtain ⟨⟨q, hq, e⟩, -⟩ := qsigNoSl_parts h1
      have := gPre_spec hq.1
      rw [e] at this
      exact this.2.2.1
    have hw := contIvS_w2
    have hks := Lvm.E2U.sigKSinC_of_GkL (I := sigInLC cfgS20) (v := M.k) hw.1 Lvm.E2S.contIvS_ok.1 hw.2.1 hw.2.2
      hG.1.2 mp.xsL mp.ysL (sigInLC_yc cfgS20)
    have hpa : (sigOutSC cfgS20).2.pa = (qsigC (sigInLC cfgS20) (qsigNoSl (sigIn cfgS20) p1).1.pre.1.n
        (p1.adv (qsigNoSl (sigIn cfgS20) p1).2)).1.pa := by
      simp only [sigOutSC, qsigSC, out_bind_eq, pure_apply_eq]
      rfl
    have hbits : SigBitsC (sigInLC cfgS20) (qsigC (sigInLC cfgS20) (qsigNoSl (sigIn cfgS20) p1).1.pre.1.n
        (p1.adv (qsigNoSl (sigIn cfgS20) p1).2)).1.pa M.k := by
      rw [← hpa]
      refine sigBitsC_of_outs M.k (sigInLC cfgS20) _ (fun k => bplOf noData (8 + nPosCls cfgS20 + k))
        (bspecs cfgS20 noData) (fun B hB => ?_) (outsOnCS S1 Pub.hdrLanesT Lvm.pubXTS hone (hWS S1 H' hG'.1))
      unfold bspecs
      rw [if_pos (show cfgS20.p.leafOut = true from rfl)]
      exact List.mem_append_right _ (List.mem_append_right _ hB)
    have hsig := qSigLeaf_sound h2 mp.flag hZ hks hbits
    have hvk : digAt M.k (sigInLC cfgS20).vk = vk := mp.vk
    rw [hvk, mp.sl] at hsig
    exact hsig

end Lvm.E2Q
