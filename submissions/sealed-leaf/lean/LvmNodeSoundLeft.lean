-- WP-14c (NodeSound, O10). New for lvm: the left child's acceptance from what the circuit's memory
-- gives, part by part (Q_link, Q_sig, Q_arith) and through the input map (BLUEPRINT §4.6, A19).
import LvmNodeSound
import LvmQLinkBridge
import LvmQLinkSound
import LvmQSigSound
import LvmPlanP20

-- (GOLF2: 4 declarations that `certified` does not use moved verbatim to `LvmNodeSoundTOff`, outside its import closure.)

/-!
# The left child from the circuit's memory

`ws = wsOf W` are the stream lanes of the child (`W = laneOf w`: lane `u` at `C_rec` word
`crecIdx u`; `17·2^14` lanes, `streamCap P20`). In a memory `M` where the circuit's parts hold with
the gate on, **`accV_childW_of`** gives the acceptance of the child `childW w` under `c_L` from
exactly what each part provides:

| hypothesis | what | owner |
|---|---|---|
| `hlink` | `LinkOk P20 (decode P20 ws)` | Q_link: QL's `qlink_sound` + `linkOk_of_laneLink` |
| `harith` | `decideF P20 m vk c_L (traceBytesB (decode P20 ws)) = true` | Q_arith (`Q_arith_eq`): QA1/QA2/QL |
| `hsig`, `hchild` | `SigOk` on the digest cells, `ChildOk` | Q_sig: WP-12 `qsig_sound_in` |
| `hvk`, `hcL`, `hsl` | the `PUB` cells: `vk`, `c_L`, `σ_leaf` | input map (A19, `inKOf_pub`) |
| `hmd` | the trace-digest cells are `traceDigest` of the decoded trace | `KS` (WP-8 `traceDigest_of_KS`) + input map |
| `hsg` | the `σ'` cells are `C_rec`'s column 17 | input map (`C_rec` input array) |
| `hhd` | Q_sig's child-header cells are stream lanes `11 …` | layout (`I.hd = sb + 11`) |
| `htr` | `readTraceL W = decode P20 (wsOf W)` (WP-13a's reader = QL's) | WP-14c |
| `hparse` | `ChildOk` with the `PUB` cells ⇒ `parseOk` on the reassembled child | WP-14c |
| `hσl` | `σ_leaf` signs `traceDigest []` | `V`'s native check (`okS`, `b = 1`) |
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig

/-- **The child's stream lanes**: `17·2^14` lanes of `W` (`C_rec`'s stream columns). -/
def wsOf (W : ℕ → Word) : List Word := (List.range (17 * 2 ^ 14)).map W

/-- **The header bridge** (stated here; proved in `LvmNodeSoundHdr`): Q_sig's `ChildOk` on the
stream's header lanes, with the `PUB` cells, is `V_S`'s native check on the reassembled child. -/
def HdrBridge : Prop :=
  ∀ (M : Mem) (I : SigIn) (ws : List Word) (vk cL : RecursionFast.Digest) (σl : Sig),
    LinkOk P20 (decode P20 ws) → hashedLen P20 ≤ 8 * ws.length →
    (∀ k < 615, M.k (I.hd + k) = laneK ws (11 + k)) → ChildOk I M.k → I.ln = 20 →
    digAt M.k I.vk = vk → digAt M.k I.cL = cL → sigAt' M.k I.sl = σl →
    SigOk vk (traceDigest []) σl = true →
    parseOk P20 vk cL (reassemble P20 (decode P20 ws)) = true

/-- **The left child of a `C_rec` candidate read with the schedule of `p`** (lvm2 E2-FT, S2GF's `NodeSound` child at
`P20F`): the trace `decode p` of its stream lanes, the proof `reassemble p` of that trace, the signature of column 17.
At `P20`, `TrBridge` makes it `childS`'s extractor reading. -/
def childSP (p : Params) (q : LeanVM.Protocol.Column 19) : Signed :=
  ⟨reassemble p (decode p (wsOf (Lvm.X.laneOf (wOfCol q)))), decode p (wsOf (Lvm.X.laneOf (wOfCol q))),
    Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol q))⟩

end Lvm.NS
