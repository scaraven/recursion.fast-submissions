-- New for lvm6 (WP NODE). The node circuit's frozen statements: `node6` with the key pinned, what the
-- circuit establishes about the child, and the CA3 bridges (header check and magic of the reassembled proof).
import Lvm6AsmSpec
import Lvm6QAccept
import Lvm6FormatP17

/-!
# `node6`'s statements (WP NODE, frozen before any proof)

* **Finding (S), adopted by S (`lvm6/S` `5697db44`).** `Stmt.node6` quantified the verifying key `vk` of `Rel (accV VS vk)` with no tie to the
  header: `NodeSound6` has `HdrWF`, `stmtOk c x` and the good relation, none of which mentions `vk`. In node
  mode the relation asks `accV VS vk c' child`, whose signature check `SigOk vk …` depends on `vk`, while the
  circuit checks the child's signature against the header's key `x.vk` (`Q_sig`'s `vk` cells are `PUB` lanes).
  So `Stmt.node6` is unprovable in node mode for any satisfiable `rest`. The scheme's check `hdrOkWith … vk c`
  does compare the header's key with `vk` (byte 88), so the fix is one hypothesis: S's **`NodeSound6V`** adds
  `x.vk = vk`, and S's **`Stmt.hdrView_okV`** adds the conclusion `(hdrView P17 x).vk = vk` (`Lvm6Stmt`).
* **`ChildOk Φ vk c tr σ`**: what the node circuit establishes about the child's decoded trace `tr` and
  signature `σ`: the trace meets the plan for `c` (`LinkOk6`, CA-2), its header passes (`ChildHdr6`, CA-3), the
  grinds (`PowOK6`), V1's decision `F6 Φ` on `accOf` (the phase HARs), `σ` signs `traceDigest tr` under `vk`.
* **`Stmt.hdrOk_of_childHdr6`**, **`Stmt.isS_of_childHdr6`** (CA3's open items): on a linked trace of
  `planOf P17`, `ChildHdr6` gives `V_S`'s header check on the reassembled proof's `HDR`, and its first byte is
  `'S'`.
-/

set_option autoImplicit false

namespace Lvm6.Node

open RecursionFast Lvm.T Lvm6.Q

/-- The plan of the child proofs (`P17`, PORT17: the node's shape; `P18`'s plan is `planOf P18`). -/
abbrev P6 : List PE6 := planOf P17

/-- **What the node circuit establishes about the child** (decoded trace `tr`, signature `σ`, statement `c`,
key `vk`). -/
structure ChildOk (Φ : Phases) (vk c : Digest) (tr : Trace) (σ : Sig) : Prop where
  /-- The trace meets the plan for `c` (`Q_link`, CA-2). -/
  link : LinkOk6 P6 c tr
  /-- Its header passes `V_S`'s parse for `vk` and `c` (`Q_sig`'s header copy, CA-3). -/
  hdr : ChildHdr6 vk c tr
  /-- Every grind passes (the PoW range rows). -/
  pow : PowOK6 P6 tr
  /-- V1's decision on V1's transcript (the phase HARs along `prog6`). -/
  dec : F6 Φ P17 vk (reassemble6 P6 tr) (accOf P17 (reassemble6 P6 tr) tr) = true
  /-- `σ` signs the trace's digest (`Q_sig` and CB's trace digest). -/
  sig : SigOk vk (traceDigest tr) σ = true

/-- **CA3 open item 1**: on a linked trace, `ChildHdr6` is `V_S`'s header check on the reassembled `HDR`. -/
def Stmt.hdrOk_of_childHdr6 : Prop :=
  ∀ (vk c : Digest) (tr : Trace), LinkOk6 P6 c tr → ChildHdr6 vk c tr →
    V.hdrOkWith leafStmtF nodeStmtF (2 ^ P17.logN) vk c ((reassemble6 P6 tr).extract 0 (hdrLen P17)) = true

/-- **CA3 open item 2**: the reassembled proof of a linked trace whose header passes starts with `'S'`. -/
def Stmt.isS_of_childHdr6 : Prop :=
  ∀ (vk c : Digest) (tr : Trace), LinkOk6 P6 c tr → ChildHdr6 vk c tr → isS (reassemble6 P6 tr) = true

end Lvm6.Node
