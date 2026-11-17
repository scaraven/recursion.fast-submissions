-- New for lvm2 MP-B cap pruning (CAP-C7, CAP-C8, 2026-11-17): the S2GB node's left child and leaf walk (proof help for
-- `nodeB20`): the position bits on `StreamOkB`, the trace digest on `StreamOkB`, the leaf walk's rows at S2GB, the
-- header bridge for `parseOkB` on `reassembleB`, and the left child's acceptance by `VSSB` (the driver's replay).
import LvmS2GBHarB
import LvmS2GBTail
import LvmS2GSStmtC
import LvmS2GBReplay

/-!
# The S2GB node's left child (proof help for `nodeB20`)

* **`qin_bitsB`**: `QIn.bits` from the `BITS` outputs on `StreamOkB`/`QOkB` (`qin_bits`'s twin).
* **`traceDigest_of_GkLB`**: the sponge half outputs the child's trace digest (`traceDigest_of_GkL` on `StreamOkB`).
* **`contIvSB_w2`**: the leaf walk's rows continue exactly on its key leaf's rows at S2GB (`contIvS_w2`'s twin).
* **`hdrBridgeB`**: `ChildOkS` on the 18 header lanes is `parseOkB` on the S2GB child (`hdrBridgeS`'s twin).
* **`accV_childB`**: the S2GB child `⟨reassembleB, tr, σ⟩` is accepted by `VSSB` (`accV_reassembleDS`'s twin).
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Bits

section
variable {p : Params} {lay : Layout} {ws : List Word}

/-- **`QIn.bits` from the `BITS` outputs** at S2GB (`qin_bits` on `StreamOkB`/`QOkB`). -/
theorem qin_bitsB (hS : StreamOkB p) (hQ : QOkB p lay) {v : Nat → FK}
    (hs : ∀ L < 2 ^ lay.m, v (lay.sb + L) = laneK ws L) (hb : PosBits p lay v) :
    ∀ k < (opens p).length, ∀ j < ((opens p).getD k default).L.t, ∀ z < ((opens p).getD k default).L.height,
      v (bitBase p lay k + ((opens p).getD k default).L.height * j + z) =
        if ansBit p ws (((opens p).getD k default).pe + j / 8) (j % 8 * ((opens p).getD k default).L.height + z)
        then 1 else 0 := by
  intro k hk j hj z hz
  have hbit := hb.bit k hk j hj z hz
  have ho : (opens p).getD k default ∈ opens p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  generalize (opens p).getD k default = o at ho hj hz hbit ⊢
  obtain ⟨h192, h1, hlt⟩ := open_pos_factsB hS hQ.cp hQ.lvIdx ho (hQ.opens o ho).1 hj
  have hin := lanes_inB hS h1 hlt
  have hT := hQ.hT
  have hlane : ansLane p (o.pe + j / 8) + (j % 8 * o.L.height + z) / 64 < 2 ^ lay.m := by
    simp only [ansLane, if_neg (show o.pe + j / 8 ≠ 0 by (clear * - h1; omega))]; (clear * - hz h192 hin hT; omega)
  unfold Out1 at hbit
  rw [hbit, Nat.add_assoc, hs _ hlane, bit_word _ (Nat.mod_lt _ (by decide))]
  rfl

end

end Lvm.QLink

namespace Lvm.E2U

open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- **The sponge half over `iv` outputs the child's trace digest** on `StreamOkB` (`traceDigest_of_GkL`'s twin). -/
theorem traceDigest_of_GkLB {P : Params} {iv : List (ℕ × ℕ)} {x : List UInt8} {qm : Column CMain.nu20}
    {qr : Column 19}
    (hst : StreamOkB P) (h0 : contL iv 0 = false)
    (hin : ∀ i, 0 < i → i < spongeBlocks P → contL iv i = true)
    (hsb : spongeBlocks P = Lvm.KSponge.nBlk (hashedLen P)) (hB : spongeBlocks P ≤ 7680)
    (hG : GkL iv x (qm, qr)) (hS : SBlkU qm qr) (hL : LaneLink P (wsOf (Lvm.X.laneOf (wOfCol qr))))
    (hpad : PadOkB (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))) (hashedLen P)) :
    Lvm.KSponge.stDigest (yState (YqU qm) (spongeBlocks P - 1)) =
      traceDigest (decode P (wsOf (Lvm.X.laneOf (wOfCol qr)))) := by
  have H := spongeRel_of_GkL h0 hG
  have hS' := stream_of_laneLinkB hst hL
  have hsz : hashedLen P ≤ (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))).length := by
    rw [wordsBytes_length]; exact hL.size
  have hin' : ∀ i, 0 < i → i < Lvm.KSponge.nBlk (hashedLen P) → contL iv i = true :=
    fun i h1 h2 => hin i h1 (by rw [hsb]; exact h2)
  rw [hsb] at hB ⊢
  obtain ⟨L, hL⟩ : ∃ L, hashedLen P = L := ⟨_, rfl⟩
  rw [hL] at hS' hsz hpad hB hin' ⊢
  have hnbL : Lvm.KSponge.nBlk L = L / 136 + 1 := rfl
  refine traceDigest_of_KS 13 _ (YqU qm) (MqU qm) _ H L (le_trans hB (by norm_num)) hin' ?_ _ ?_
  · intro p h1 h2
    have h2' : p < 136 * Lvm.KSponge.nBlk L := h2
    have := msgBytes_eq_streamU hS (p := p) (by show p / 136 < 2 ^ 14; omega)
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl, this, ← padAt_eq]
    exact hpad p h1 (by rw [nBlk_eq]; omega)
  · rw [← hS']
    refine List.ext_getElem (by rw [Lvm.KSponge.streamOf_length, List.length_take]; omega) fun p h1 h2 => ?_
    have hp : p < L := by rw [Lvm.KSponge.streamOf_length] at h1; exact h1
    simp only [Lvm.KSponge.streamOf, List.getElem_ofFn, List.getElem_take]
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl,
      msgBytes_eq_streamU hS (by show p / 136 < 2 ^ 14; omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]

end Lvm.E2U

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS

/-- The leaf walk's rows `w2RowC cfgB20 + r` continue exactly on its key leaf's rows (`contIvS_w2` at S2GB). -/
theorem contIvSB_w2 : w2RowC cfgB20 + (nStepRowsC + 48) ≤ 2 ^ 13 ∧
    (∀ r, r < nStepRowsC + 48 → ¬ (nStepRowsC + 1 ≤ r ∧ r ≤ nStepRowsC + 31) →
      Lvm.E2U.contL (Lvm.E2S.contIvSB Lvm.E2S.aSP) (w2RowC cfgB20 + r) = false) ∧
    (∀ r, nStepRowsC + 1 ≤ r → r ≤ nStepRowsC + 31 →
      Lvm.E2U.contL (Lvm.E2S.contIvSB Lvm.E2S.aSP) (w2RowC cfgB20 + r) = true) := by
  have hw : w2RowC cfgB20 = 7280 := by rw [w2RowC, nStepRowsC_eq]; decide
  rw [hw, nStepRowsC_eq]
  refine ⟨by norm_num, fun r h1 h2 => ?_, fun r h1 h2 => ?_⟩
  all_goals
    unfold Lvm.E2S.bB Lvm.E2S.aSP at *
    simp only [Lvm.E2U.contL, Lvm.E2S.contIvSB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
      Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not, Lvm.E2S.bB]
    omega

end Lvm.E2Q

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig Lvm.ASM

/-- `zeroBytes` reads only its range. -/
theorem zeroBytes_congr {π π' : ByteArray} : ∀ (n o : ℕ), (∀ k, o ≤ k → k < o + n → π'.get! k = π.get! k) →
    zeroBytes π' o n = zeroBytes π o n
  | 0, _, _ => rfl
  | n + 1, o, h => by
    simp only [zeroBytes]
    rw [h o le_rfl (by omega), zeroBytes_congr n (o + 1) fun k h1 h2 => h k (by omega) (by omega)]

/-- **`parseOkB` from `parseOkS` on a prefix** (proof help): a proof that extends a `parseOkS`-proof `π` by at most
`tailMax p` bytes passes `parseOkB` (`piStatic = piSize`; the header lies in `π`). -/
theorem parseOkB_of_S {p : Params} {vk c : Digest} {π π' : ByteArray} (hS : parseOkS p vk c π = true)
    (hpre : ∀ k < π.size, π'.get! k = π.get! k) (hfix : hdrFix ≤ π.size) (h1 : π.size ≤ π'.size)
    (h2 : π'.size ≤ π.size + tailMax p) : parseOkB p vk c π' = true := by
  have hH : Header.ofProof π' = Header.ofProof π := ofProof_congr fun k _ hk => hpre k (by omega)
  have h0 : π'.get! 0 = π.get! 0 := hpre 0 (by have : 0 < hdrFix := (by decide); omega)
  have hz : zeroBytes π' 1 7 = zeroBytes π 1 7 :=
    zeroBytes_congr 7 1 fun k _ hk => hpre k (by have : 8 ≤ hdrFix := (by decide); omega)
  have hs : π.size = piSize p := by
    simp only [parseOkS, Bool.and_eq_true, beq_iff_eq] at hS
    exact hS.1.1.1
  unfold parseOkB
  unfold parseOkS at hS
  rw [hH, h0, hz]
  rw [hs] at h1 h2
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hS ⊢
  exact ⟨⟨⟨⟨h1, h2⟩, hS.1.1.2⟩, hS.1.2⟩, hS.2⟩

end Lvm.NS

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.PlanChk (capLk)

/-- A node entry of a plan that passes the S2GB pass is 64 bytes (`node_of`'s twin). -/
theorem node_ofB {P : List PE} {tbl : List (ℕ × ℕ)} {n c sl : ℕ} (h : passRB (capLk tbl) n c sl P tbl 0 0 0 = true) :
    ∀ e ∈ P, ∀ pe h j lvl cap, e.k = .node pe h j lvl cap → e.len = 64 := by
  intro e he pe hh j lvl cap hk
  obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem he
  have h := (sound_ofB h).1 k hk'
  simp only [elemFB, Bool.and_eq_true] at h
  have h2 := h.1.2
  simp only [entFB, hk, Lvm.PlanChk.entF, Bool.and_eq_true, Nat.beq_eq] at h2
  exact h2.1.1.1.1.1.1

/-- **The S2GB plan's static facts at `P20B`** (`plan_static_ofR`'s twin): node queries of 64 bytes, and
`8 + Σ clen = piSize P20B` (the static part of π). -/
theorem plan_static_P20B : (∀ e ∈ plan P20B, nodeLenOk e = true) ∧ 8 + ((plan P20B).map clen).sum = piSize P20B := by
  have hc : clen = Lvm.PlanChk.clenC := by
    funext e
    rcases e with ⟨k, len⟩
    cases k <;> rfl
  refine ⟨fun e he => ?_, ?_⟩
  · rcases e with ⟨k, len⟩
    cases k with
    | node pe h j lvl cap =>
      simp only [nodeLenOk, beq_iff_eq]
      exact node_ofB passRB_P20B _ he pe h j lvl cap rfl
    | _ => rfl
  · rw [hc, (sound_ofB passRB_P20B).2.2.2.1]
    exact sizes_P20B.1.1.symm

theorem reassembleB_bl (p : Params) (tr : Trace) : bl (reassembleB p tr) = bl (reassemble p tr) ++ tailB p tr := by
  rw [bl_reassemble]; rfl

theorem isS_reassembleB (p : Params) (tr : Trace) : isS (reassembleB p tr) = true := rfl

/-- `drive_replayBP` at `P20B` (its static conditions: `PlanOkB`, the levels' indices and `c < cap` from `hQB20`;
the static size from `plan_static_P20B`). -/
theorem drive_replayB_P20B (tr : Trace) (hL : LinkOk P20B tr) (F : ByteArray → Bool) :
    (driveB P20B (reassembleB P20B tr) F).runSeq tr = some (F (traceBytesB tr)) ∧
      (tailB P20B tr).length ≤ tailMax P20B :=
  drive_replayBP P20B rfl planOkB_P20B hlvB20
    (fun o ho => by obtain ⟨-, -, -, h1, h2, -⟩ := hQB20.opens o ho; rw [h1]; exact h2) tr hL
    (size_reassembleP plan_static_P20B.1 plan_static_P20B.2 hL) F

/-- **The π tail fits**: on a trace of the S2GB schedule, `tailB` has at most `tailMax P20B` bytes (each opening's
heap-bottom slots send at most `2^cap − 1` uncovered layer nodes of 32 bytes: path `0` covers one). -/
theorem tailB_le (tr : Trace) (hL : LinkOk P20B tr) : (tailB P20B tr).length ≤ tailMax P20B :=
  (drive_replayB_P20B tr hL fun _ => true).2

/-- **Replay of the S2GB driver** (`drive_replayP`'s twin): on a trace of the S2GB schedule, `driveB` on
`reassembleB` asks exactly the trace (the paths, the layer from the paths' tops and the π tail, the heap, the
sent-cap check) and returns `F` of its stream. -/
theorem drive_replayB (tr : Trace) (hL : LinkOk P20B tr) (F : ByteArray → Bool) :
    (driveB P20B (reassembleB P20B tr) F).runSeq tr = some (F (traceBytesB tr)) :=
  (drive_replayB_P20B tr hL F).1

/-- **The header bridge at S2GB** (`hdrBridgeS`'s twin: `ChildOkS` on the stream's 18 header lanes is `parseOkB` on
the S2GB child `reassembleB`). -/
theorem hdrBridgeB :
    ∀ (M : Mem) (I : SigIn) (ws : List Word) (vk cL : RecursionFast.Digest),
      LinkOk P20B (decode P20B ws) → hashedLen P20B ≤ 8 * ws.length →
      (∀ k < 18, M.k (I.hd + k) = laneK ws (11 + k)) → ChildOkS I M.k → I.ln = 20 →
      digAt M.k I.vk = vk → digAt M.k I.cL = cL →
      parseOkB P20B vk cL (reassembleB P20B (decode P20B ws)) = true := by
  intro M I ws vk cL hlink hsz hhd hchild hln hvk hcL
  have hst := plan_static_P20B
  have hS := hdrBridgeS P20B rfl hst.1 hst.2 (by rw [sizes_P20B.1.2.2.1]; norm_num)
    (by rw [headerBytesP_P20B.2.1]; norm_num) M I ws vk cL hlink hsz hhd hchild hln hvk hcL
  have hsz0 := size_reassembleP hst.1 hst.2 hlink
  have hpi : piSize P20B = 269336 := sizes_P20B.1.1
  have ht := tailB_le _ hlink
  refine parseOkB_of_S hS (fun k hk => ?_) (by rw [hsz0, hpi]; decide) ?_ ?_
  · rw [get!_bl, get!_bl, reassembleB_bl, List.getD_append _ _ _ _ (by rw [← size_bl]; exact hk)]
  · rw [size_bl, size_bl, reassembleB_bl, List.length_append]; omega
  · rw [size_bl, size_bl, reassembleB_bl, List.length_append]; omega

/-- **The S2GB child is accepted** by `VSSB` (`accV_reassembleDS`'s twin: `parseOkB`, then the S2GB driver replays
the trace on `reassembleB`). -/
theorem accV_childB (vk cL : RecursionFast.Digest) (tr : Trace) (σ : Sig) (hL : LinkOk P20B tr)
    (hparse : parseOkB P20B vk cL (reassembleB P20B tr) = true)
    (hdec : Lvm.E2S.decideFBX NTB20 vk cL (traceBytesB tr) = true)
    (hsig : SigOk vk (traceDigest tr) σ = true) :
    accV (Lvm.E2S.VSSB NTB20) vk cL ⟨reassembleB P20B tr, tr, σ⟩ = true := by
  have hsize : (reassembleB P20B tr).size ≤ piStatic P20B + tailMax P20B := by
    have h := hparse
    unfold parseOkB at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.2
  have hrun : ((Lvm.E2S.VSSB NTB20) vk cL (reassembleB P20B tr)).runSeq tr = some true := by
    show (if parseOkB P20B vk cL (reassembleB P20B tr) then
      driveB P20B (reassembleB P20B tr) (Lvm.E2S.decideFBX NTB20 vk cL) else .ret false).runSeq tr = some true
    rw [hparse, if_pos rfl, drive_replayB tr hL, hdec]
  have hR := sound_ofB passRB_P20B
  obtain ⟨hn, hG⟩ := hL
  simp only [accV, accWith, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, fun e he => ?_⟩, ?_⟩, ?_⟩
  · rw [sizes_P20B.1.1, sizes_P20B.1.2.2.2.2.2.2] at hsize; omega
  · rw [hn, hR.2.2.1]; decide
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hGi := (hG i hi).1
    have hq1 : (qOf tr i) = tr[i].1 := by
      simp [qOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hi' : i < (plan P20B).length := hn ▸ hi
    have hc := (hR.1 i hi')
    simp only [elemFB, Bool.and_eq_true, Nat.ble_eq] at hc
    rw [← hq1, hGi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    exact hc.2
  · rw [SigOkF_eq, traceDigestF_eq]; exact hsig
  · rw [V_S _ _ _ _ (isS_reassembleB P20B tr)]; exact hrun

end Lvm.E2Q
