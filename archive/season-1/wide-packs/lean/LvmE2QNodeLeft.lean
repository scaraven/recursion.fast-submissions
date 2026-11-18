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

/-- **The plan's static facts** at a stage whose one-pass decision holds: node queries of 64 bytes, and
`8 + Σ clen = piSize p` (`hpi : piSize p = 8 + t₁`). -/
theorem plan_static_ofR {p : Params} {tbl : List (ℕ × ℕ)} {n t1 t2 : ℕ}
    (hR : Lvm.PlanChk.passR (Lvm.PlanChk.capLk tbl) n t1 t2 (plan p) tbl 0 0 0 = true) (hpi : piSize p = 8 + t1) :
    (∀ e ∈ plan p, nodeLenOk e = true) ∧ 8 + ((plan p).map clen).sum = piSize p := by
  have hc : clen = Lvm.PlanChk.clenC := by
    funext e
    rcases e with ⟨k, len⟩
    cases k <;> rfl
  refine ⟨fun e he => ?_, ?_⟩
  · rcases e with ⟨k, len⟩
    cases k with
    | node pe h j lvl cap =>
      simp only [nodeLenOk, beq_iff_eq]
      exact Lvm.PlanChk.node_of hR _ he pe h j lvl cap rfl
    | _ => rfl
  · rw [hc, (Lvm.PlanChk.sound_of hR).2.2.2.1, hpi]

/-- **The static facts at `P20F`**: node queries of 64 bytes, and `8 + Σ clen = piSize P20F`. -/
theorem plan_static_P20F :
    (∀ e ∈ plan P20F, nodeLenOk e = true) ∧ 8 + ((plan P20F).map clen).sum = piSize P20F :=
  plan_static_ofR passR_P20F checks_P20F.1.1

/-- **The plan's static facts a stage's left child reads** (`accV_reassembleD`, `hdrBridgeP`). -/
structure PlanC (p : Params) : Prop where
  ok : PlanOk p
  len : (plan p).length ≤ qVlvm
  cap : ∀ i < (plan p).length, ((plan p).getD i default).len ≤ queryCap
  node : ∀ e ∈ plan p, nodeLenOk e = true
  clen : 8 + ((plan p).map clen).sum = piSize p
  pi : piSize p < 2 ^ 64
  hlo : 6064 ≤ hashedLen p
  hhi : hashedLen p ≤ 8 * (17 * 2 ^ 14)
  logN : p.logN = 20
  /-- The header carries `σ_leaf` (every stage before `S2GS`; `hdrBridgeP`'s lanes `11 … 625`). -/
  lo : p.leafOut = false

/-- **The left child is accepted by a stage's `V_S`** (`VS = parseOk p, then drive p D`) from what the circuit's
memory gives (`accV_childW_ofT` at any stage). -/
theorem accV_childC (p : Params) (VS : SProg) (D : RecursionFast.Digest → RecursionFast.Digest → ByteArray → Bool)
    (hVS : ∀ vk c π, VS vk c π = if parseOk p vk c π then drive p π (D vk c) else .ret false) (P : PlanC p)
    {M : Mem} {I : SigIn} (q : LeanVM.Protocol.Column 19) {vk cL : RecursionFast.Digest} {σl : Sig}
    (hlink : LinkOk p (decode p (wsOf (Lvm.X.laneOf (wOfCol q)))))
    (harith : D vk cL (traceBytesB (decode p (wsOf (Lvm.X.laneOf (wOfCol q))))) = true)
    (hsig : SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true)
    (hchild : ChildOk I M.k) (hln : I.ln = 20)
    (hvk : digAt M.k I.vk = vk) (hcL : digAt M.k I.cL = cL) (hsl : sigAt' M.k I.sl = σl)
    (hmd : digAt M.k I.md = traceDigest (decode p (wsOf (Lvm.X.laneOf (wOfCol q)))))
    (hsg : sigAt' M.k I.sg = Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol q)))
    (hhd : ∀ k < 615, M.k (I.hd + k) = laneK (wsOf (Lvm.X.laneOf (wOfCol q))) (11 + k))
    (hσl : SigOk vk (traceDigest []) σl = true) :
    accV VS vk cL (childSP p q) = true := by
  have hws : hashedLen p ≤ 8 * (wsOf (Lvm.X.laneOf (wOfCol q))).length := by
    rw [wsOf, List.length_map, List.length_range]; exact P.hhi
  refine accV_reassembleD VS p D hVS vk cL _ _ P.ok P.len P.cap P.pi hlink
    (hdrBridgeP p P.logN P.node P.clen P.hlo P.lo M I _ vk cL σl hlink hws hhd hchild hln hvk hcL hsl hσl) harith ?_
  rw [← hsg, ← hmd, ← hvk]
  exact hsig

/-- **The plan's facts** at a stage from its one-pass decision, `PlanOk` and its sizes. -/
theorem planC_ofR {p : Params} {tbl : List (ℕ × ℕ)} {n t1 t2 : ℕ}
    (hR : Lvm.PlanChk.passR (Lvm.PlanChk.capLk tbl) n t1 t2 (plan p) tbl 0 0 0 = true) (hP : PlanOk p)
    (hn : n ≤ qVlvm) (hpi : piSize p = 8 + t1) (hpi' : 8 + t1 < 2 ^ 64) (hH : hashedLen p = t2 + 1)
    (hlo : 6063 ≤ t2) (hhi : t2 + 1 ≤ 8 * (17 * 2 ^ 14)) (hlog : p.logN = 20)
    (hl : p.leafOut = false := by rfl) : PlanC p :=
  ⟨hP, by rw [(Lvm.PlanChk.sound_of hR).2.2.1]; exact hn, planCap_ofR hR, (plan_static_ofR hR hpi).1,
    (plan_static_ofR hR hpi).2, by rw [hpi]; exact hpi', by rw [hH]; omega, by rw [hH]; exact hhi, hlog, hl⟩

/-- S2GF's plan facts. -/
theorem planC_P20F : PlanC P20F :=
  planC_ofR passR_P20F planOk_P20F (by decide) checks_P20F.1.1 (by norm_num) checks_P20F.1.2.2.1 (by norm_num)
    (by norm_num) rfl

/-- **The left child is accepted by `VSFX N`** from what the circuit's memory gives (`accV_childC` at S2GF). -/
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
    accV (E2V.VSFX N) vk cL (childSP P20F q) = true :=
  accV_childC P20F (E2V.VSFX N) (E2V.decideFFX P20F N) (fun _ _ _ => rfl) planC_P20F q hlink harith hsig hchild hln
    hvk hcL hsl hmd hsg hhd hσl

end Lvm.E2Q
