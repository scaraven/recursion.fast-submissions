-- New for lvm6 (WP CA). The child is accepted: season 1's `accV_reassembleD`, re-done for the
-- plan-driven program. This is the seam CD's `node6` uses (CA's Q_link + replay, CB/CD's decision).
import Lvm6QDrive
import LvmVerifier
import Lvm6QDriveV
import Lvm6QLink
import Lvm6QSigHdr

/-!
# A linked trace is an accepted child (CA-4)

**`acc_of_link`**: if `V vk c` runs the plan-driven program on the reassembled proof (WP-S's
obligation for its `V`: on a proof starting with `'S'`, `V = drive6 (plan of the Shape) … F`, with
the header and arithmetic checks in `F`), the trace meets its plan, `F` accepts it, the plan fits
`qV` and `queryCap`, and `σ` signs the trace's digest, then the contract's `acc` accepts the signed
proof `⟨reassemble6 P tr, tr, σ⟩`.

**`accV_of_link`** (WP CA3): the same for the relation's `accV` with V1's `V_S` itself, `VS6 (toV sh) F`,
through `vs6_of_drive6`: no hypothesis `VS = drive6 …` is left. The header check, `PowOK6` and `F` on
`accOf` are its hypotheses (CD's decision). (`accV_of_drive6` is the earlier form, for any `VS` that is
`drive6 …` on the proof.)

**`childLink6`** (WP CA3, FORMAT6 v2.5): `Q_link` and `Q_sig` run on the same stream cells, with `Q_sig`'s
statement cells `I.cL` the cells `lay.cp`, give the decoded trace's link facts and its `ChildHdr6` for the
same statement `c`, and both signatures. **`seedLane_hdrW`**: the seed entry's `HDR` word `k` is stream word
`hdrW k` in `Q_link`'s lane map (the cells `hdrCopy6` reads).
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Replay Lvm.T

theorem size_of_link {P : List PE6} {c : Digest} {tr : Trace} (hL : LinkOk6 P c tr)
    {B : ℕ} (hcap : ∀ e ∈ P, e.len ≤ B) : ∀ e ∈ tr, e.1.size ≤ B := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hG := (hL.2 i hi).1
  have hq : qOf tr i = tr[i].1 := by
    simp only [qOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [← hq, hG]
  apply hcap
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hL.1 ▸ hi), Option.getD_some]
  exact List.getElem_mem _

/-- **A linked trace is an accepted child** (CA-4). -/
theorem acc_of_link (S : Submission) {P : List PE6} {vk c : Digest} {tr : Trace} {σ : Sig}
    {F : Trace → Bool} (hV : S.V vk c (reassemble6 P tr) = drive6 P c (reassemble6 P tr) F)
    (hR : refsOK P = true) (hL : LinkOk6 P c tr) (hF : F tr = true) (hq : P.length ≤ S.qV)
    (hcap : ∀ e ∈ P, e.len ≤ queryCap) (hπ : (reassemble6 P tr).size < 2 ^ 64)
    (hsig : SigOk vk (traceDigest tr) σ = true) :
    S.acc vk c ⟨reassemble6 P tr, tr, σ⟩ = true := by
  simp only [Submission.acc, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨hπ, hL.1 ▸ hq⟩, size_of_link hL hcap⟩, hsig⟩, ?_⟩
  rw [hV, replay6 hR hL F, hF]

/-- **The same for the relation's `accV`**, for any `VS` that is the plan-driven program on the
reassembled proof (a proof starting with `'S'`, its magic). -/
theorem accV_of_drive6 (VS : SProg) {P : List PE6} {vk c : Digest} {tr : Trace} {σ : Sig}
    {F : Trace → Bool} (hS : isS (reassemble6 P tr) = true)
    (hV : VS vk c (reassemble6 P tr) = drive6 P c (reassemble6 P tr) F)
    (hR : refsOK P = true) (hL : LinkOk6 P c tr) (hF : F tr = true) (hq : P.length ≤ qVlvm)
    (hcap : ∀ e ∈ P, e.len ≤ queryCap) (hπ : (reassemble6 P tr).size < 2 ^ 64)
    (hsig : SigOk vk (traceDigest tr) σ = true) :
    accV VS vk c ⟨reassemble6 P tr, tr, σ⟩ = true := by
  simp only [accV, accWith, Bool.and_eq_true, decide_eq_true_eq, SigOkF_eq, traceDigestF_eq]
  refine ⟨⟨⟨⟨hπ, hL.1 ▸ hq⟩, size_of_link hL hcap⟩, hsig⟩, ?_⟩
  rw [Vwith, if_pos hS, hV, replay6 hR hL F, hF]

/-- **A linked trace is accepted by the relation's `accV` with V1's `V_S`** (S's `NodeSound6` uses
`Rel (accV VS vk)`; CA-4 at `VS = VS6 (toV sh) F`): the plan of a shape whose static facts hold
(`simOK`, `refsOK`; both decided at `P18`), a linked trace, `V_S`'s header check on the reassembled
proof's `HDR`, the grinds, `F` on V1's transcript `accOf`, the sizes and the signature. -/
theorem accV_of_link (sh : Lvm6.Shape) (hSim : simOK sh = true) (hR : refsOK (planOf sh) = true)
    {F : ByteArray → List V.NV → Bool} {vk c : Digest} {tr : Trace} {σ : Sig}
    (hS : isS (reassemble6 (planOf sh) tr) = true) (hL : LinkOk6 (planOf sh) c tr)
    (hH : V.hdrOkWith leafStmtF nodeStmtF (2 ^ sh.logN) vk c
      ((reassemble6 (planOf sh) tr).extract 0 (Lvm6.hdrLen sh)) = true)
    (hPow : PowOK6 (planOf sh) tr)
    (hF : F (reassemble6 (planOf sh) tr) (accOf sh (reassemble6 (planOf sh) tr) tr) = true)
    (hq : (planOf sh).length ≤ qVlvm) (hcap : ∀ e ∈ planOf sh, e.len ≤ queryCap)
    (hπ : (reassemble6 (planOf sh) tr).size < 2 ^ 64) (hsig : SigOk vk (traceDigest tr) σ = true) :
    accV (V.VS6 (Lvm6.toV sh) F) vk c ⟨reassemble6 (planOf sh) tr, tr, σ⟩ = true := by
  simp only [accV, accWith, Bool.and_eq_true, decide_eq_true_eq, SigOkF_eq, traceDigestF_eq]
  refine ⟨⟨⟨⟨hπ, hL.1 ▸ hq⟩, size_of_link hL hcap⟩, hsig⟩, ?_⟩
  rw [Vwith, if_pos hS]
  exact vs6_of_drive6 sh hSim (F' := fun _ => true) (replay6 hR hL _) fun _ => ⟨hH, hPow, hF⟩

/-! ## `Q_link` and `Q_sig` on the same stream (FORMAT6 v2.5) -/

/-- **The seed entry's `HDR` words are where `Q_sig` reads them**: in `Q_link`'s lane map the seed's
query starts at word `eLane6 P 1 + 1`, `a₀` takes 4 words, so `HDR` word `k` is stream word `hdrW k`. -/
theorem seedLane_hdrW {P : List PE6} (h0 : (P.getD 0 default).len = 7) (hP : 2 ≤ P.length) (k : ℕ) :
    eLane6 P 1 + 5 + k = hdrW k := by
  simp only [eLane6, bOff6, lens6, slen1 h0 hP, hdrW, seedW]

open Lvm.QSig Lvm.QLink Lvm.Loop Lvm.Loop.Build in
/-- **`Q_link` and `Q_sig` bind one child** (CA-2 + CA-3 at FORMAT6 v2.5): with the stream at the cells
from `lay.sb` for both, `Q_sig`'s statement cells `I.cL = lay.cp`, the rows and asserts of both and their
inputs, the decoded trace meets its plan (`QLinkConcl`, and `LaneLink6` for CB's trace digest), its `HDR` passes `V_S`'s header and statement
checks for the statement in the cells `I.cL` (`ChildHdr6`), the child's signature verifies on the digest
cells and `σ_leaf` on `traceDigest []`. -/
theorem childLink6 {P : List PE6} {os : List Open6Q} {lay : Layout6} {ws : List Word} {c : Ctx} {M : Mem}
    (hS : streamOkL6 P = true) (hP2 : 2 ≤ P.length) (hO : opensOK P os = true)
    (hQ : qOk6 P os lay = true) (hin : QIn6 P os lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink6 P os lay pt).2) (hA : SegsAssert M pt (qlink6 P os lay pt).2)
    (h0 : (P.getD 0 default).len = 7) (h1 : 152 ≤ (P.getD 1 default).len)
    (hBm : 56 + (P.getD 1 default).len ≤ 8 * 2 ^ lay.m) (h27 : 27 ≤ 2 ^ lay.m)
    {I Il : SigIn} (hcL : I.cL = lay.cp) {p : Ptr}
    (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) (hq : Ok c M (qsig6 I Il lay.sb) p) (hg : M.k I.flag = 1)
    (hks : SigKSin I M.k) (hbits : SigBits I (qsig6 I Il lay.sb p).1.1 M.k)
    (hinj' : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b)
    (hgl : M.k Il.flag = 1) (hksL : SigKSinC Il M.k) (hbitsL : SigBitsC Il (qsig6 I Il lay.sb p).1.2.pa M.k) :
    QLinkConcl P (digAt M.k I.cL) ws ∧ LaneLink6 P (digAt M.k I.cL) ws ∧
      ChildHdr6 (digAt M.k I.vk) (digAt M.k I.cL) (decode6 P ws) ∧
      SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true ∧
      SigOk (digAt M.k Il.vk) (traceDigest []) (sigAtP M.k Il.sg) = true := by
  obtain ⟨hsig, hleaf, hch, hcp, hmg, hnk⟩ := qsig6_sound hln hq hg hks hbits hinj' hgl hksL hbitsL
  obtain ⟨hC, hLL⟩ := qlink6_sound_lanes hS hP2 hO hQ hin hws hinj hN hNs h hA
  refine ⟨hcL ▸ hC, hcL ▸ hLL, ?_, hsig, hleaf⟩
  refine childHdr6_of_cells h0 hP2 h1 ?_ (fun j hj => hin.stream j (by omega)) hcp hmg hnk hch
  rw [wordsBytes_length]
  omega

end Lvm6.Q
