-- New for lvm2 E2-FT (E2F-C): the left child of an S2GF node is accepted by S2GF's verifier `VSFX N` (roll 11's
-- `accV_childW_ofT` at `P20F`, on the spec-level child `childSP P20F`): replay through `accV_reassembleD`, the header
-- bridge through `hdrBridgeP`, the plan's facts from `LvmE2QPlanF`.
import LvmE2QPlanF
import LvmNodeSoundT
import LvmNodeSoundHdr
import LvmE2VRefines

/-!
# The left child at S2GF

* `plan_static_P20F`: node queries of 64 bytes and `8 + Σ clen = piSize P20F = 306,992`.
* **`accV_childSP_of`**: from what the circuit's memory gives (Q_link's `LinkOk` at `P20F`, Q_arith's
  `decideFFX P20F N`, Q_sig's signature check, `ChildOk`, the `PUB` and header cells), `VSFX N` accepts the left child
  `childSP P20F q`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig Lvm.NS

/-- **The static facts at `P20F`**: node queries of 64 bytes, and `8 + Σ clen = piSize P20F`. -/
theorem plan_static_P20F :
    (∀ e ∈ plan P20F, nodeLenOk e = true) ∧ 8 + ((plan P20F).map clen).sum = piSize P20F := by
  have hc : clen = Lvm.PlanChk.clenC := by
    funext e
    rcases e with ⟨k, len⟩
    cases k <;> rfl
  refine ⟨fun e he => ?_, ?_⟩
  · rcases e with ⟨k, len⟩
    cases k with
    | node pe h j lvl cap =>
      simp only [nodeLenOk, beq_iff_eq]
      exact Lvm.PlanChk.node_of passR_P20F _ he pe h j lvl cap rfl
    | _ => rfl
  · rw [hc, (Lvm.PlanChk.sound_of passR_P20F).2.2.2.1, show piSize P20F = 306992 from checks_P20F.1.1]

/-- **The left child is accepted by `VSFX N`** from what the circuit's memory gives (`accV_childW_ofT` at S2GF). -/
theorem accV_childSP_of (N : TypedV.TNat) {M : Mem} {I : SigIn} (q : LeanVM.Protocol.Column 19)
    {vk cL : RecursionFast.Digest} {σl : Sig}
    (hlink : LinkOk P20F (decode P20F (wsOf (Lvm.X.laneOf (wOfCol q)))))
    (harith : E2V.decideFFX P20F N vk cL (traceBytesB (decode P20F (wsOf (Lvm.X.laneOf (wOfCol q))))) = true)
    (hsig : SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true)
    (hchild : ChildOk I M.k) (hln : I.ln = 20)
    (hvk : digAt M.k I.vk = vk) (hcL : digAt M.k I.cL = cL) (hsl : sigAt' M.k I.sl = σl)
    (hmd : digAt M.k I.md = traceDigest (decode P20F (wsOf (Lvm.X.laneOf (wOfCol q)))))
    (hsg : sigAt' M.k I.sg = Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol q)))
    (hhd : ∀ k < 615, M.k (I.hd + k) = laneK (wsOf (Lvm.X.laneOf (wOfCol q))) (11 + k))
    (hσl : SigOk vk (traceDigest []) σl = true) :
    accV (E2V.VSFX N) vk cL (childSP P20F q) = true := by
  have hH : hashedLen P20F = 584008 := checks_P20F.1.2.2.1
  have hws : hashedLen P20F ≤ 8 * (wsOf (Lvm.X.laneOf (wOfCol q))).length := by
    rw [wsOf, List.length_map, List.length_range, hH]; norm_num
  obtain ⟨hn, hc⟩ := plan_static_P20F
  refine accV_reassembleD (E2V.VSFX N) P20F (E2V.decideFFX P20F N) (fun _ _ _ => rfl) vk cL _ _ planOk_P20F
    (by rw [plan_P20F]; decide) planCap_P20F (by rw [show piSize P20F = 306992 from checks_P20F.1.1]; norm_num)
    hlink (hdrBridgeP P20F rfl hn hc (by rw [hH]; norm_num) M I _ vk cL σl hlink hws hhd hchild hln hvk hcL hsl hσl)
    harith ?_
  rw [← hsg, ← hmd, ← hvk]
  exact hsig

end Lvm.E2Q
