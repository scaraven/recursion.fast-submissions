-- New for lvm2 MP-B cap pruning (CAP-X, 2026-11-17): S2GB's extractor program, its specification and the KCert over
-- `schemeSWB` (definitions of `LvmS2GBExt`'s statements).
import LvmS2GBTail
import LvmS2GBFill
import LvmS2GBExtDyn
import LvmS2GBExtTail
import LvmS2GSXS
import LvmCertStage

/-!
# S2GB's extractor: the program and the specification

See `LvmS2GBExt`.
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS Lvm.Replay

/-! ## The parse with the size range -/

/-- The kind flag and the size flag `rIsSz := [lo ≤ |π| ≤ hi]`. -/
def kindPsB (lo hi : ℕ) : List Prim :=
  [.const rK 0xFF, .op .and rB0 rB0 rK, .const rK kindS, .op .eq rIsK rB0 rK,
   .const rK (BitVec.ofNat 64 lo), .op .ltu rT rLen rK, .const rK (BitVec.ofNat 64 hi), .op .ltu rK rK rLen,
   .op .or rT rT rK, .const rK 0, .op .eq rIsSz rT rK]

/-- The parse: `rLen := |π|`, `rB0 :=` the first byte, the flags. -/
def parseIRB (lo hi : ℕ) : XIR := .seq (readAt rLen 4) (.seq (readAt rB0 5) (.blk (kindPsB lo hi)))

/-- **The extractor's program with a size range** (`extIRWith` with `lo ≤ |π| ≤ hi`). -/
def extIRWithB (lo hi : ℕ) (dec : XIR) : XIR :=
  .seq (parseIRB lo hi) (.ite rIsK (.ite rIsSz dec (.blk [])) wIR)

/-! ## The node branch -/

/-- S2GB's column reads walk from the sent caps: level 0 from 2 nodes (18 levels), levels 1, 2 from the root
(16, 13 levels). -/
def read0B : XIR := readGIRD memM (capWS stB20 0) wB0M (2 ^ 19) 18 (64 - stB20.occ0) stB20.occ0
/-- Level 1's word. -/
def read1B : XIR := readGIRD memM (capWS stB20 1) wB1M (2 ^ 16) 16 0 48
/-- Level 2's word. -/
def read2B : XIR := readGIRD memM (capWS stB20 2) wB2M (2 ^ 13) 13 0 48

/-! ## The node output: the child's static part and π tail -/

/-- Entry `i`'s lane and query length in the stream (`entLS`; entry `0` is `q₀`). -/
def laneE (st : XStage) (i : ℕ) : ℕ × ℕ := (entLS st).getD (i - 1) (0, 0)

/-- **A level's tail data** at plan entry `i` (its first heap entry, slot `2^m − 1`), bitmap at `bm`: the memory words
(after `copyIR`, lane `u` at `sgB + u`) of the paths' position bits and of the bottom heap queries. -/
def tlvAt (st : XStage) (bm i : ℕ) (e : Replay.PE) : Option TLv :=
  match e.k with
  | .heap pe h t path _ m k _ =>
    if k + 1 = 2 ^ m then
      some ⟨m, bm, (List.range t).map (fun j =>
          (sgB + (laneE st (pe + j / 8)).1 + 1 + (laneE st (pe + j / 8)).2 / 8 + (j % 8 * h + path) / 64,
            (j % 8 * h + path) % 64)),
        (List.range (2 ^ (m - 1))).map fun y => sgB + (laneE st (i + 2 ^ (m - 1) - 1 - y)).1 + 1⟩
    else none
  | _ => none

/-- The levels' tail data in plan order, bitmaps packed from `bm`. -/
def tlvsFrom (st : XStage) : ℕ → List (ℕ × Replay.PE) → List TLv
  | _, [] => []
  | bm, (i, e) :: r =>
    match tlvAt st bm i e with
    | some l => l :: tlvsFrom st (bm + 2 ^ l.m) r
    | none => tlvsFrom st bm r

/-- **S2GB's tail data** (bitmaps from `wB2M`, level 2's rows, dead after decoding). -/
def tlvB20 : List TLv :=
  tlvsFrom stB20 wB2M ((List.range (Replay.plan P20B).length).map fun i => (i, (Replay.plan P20B).getD i default))

/-- **The node output at S2GB** (`outIRS` with the child's size `piStatic + 32 · (the number of uncovered nodes)` and the π tail after the
static part). -/
def outIRB (mB : ℕ) : XIR :=
  .seq (emitIR (toWord 1)) (.seq (tcpIR 11 4) (.seq (leafStmtIR 20 19)
  (.seq (copyIR mB) (.seq (bmIR tlvB20) (.seq (sizeWIR (piStatic P20B) tlvB20)
  (.seq (setR sgB) (.seq (segIR apC 0 (pSegS stB20)) (.seq (tailIR tlvB20) (.seq (segIR apC 0 (trSegS stB20))
  (.seq (setR (sigB mB)) (.seq (segIR apC 0 (.cp 0 597))
  (.seq (emitIR (toWord 48)) (.seq (emitIR (toWord 0)) (.seq (tcpIR 15 5)
  (.seq (emitIR (toWord 0)) (rsigIR stB20 mB))))))))))))))))

/-- After level 0's decoder: the stream block and the node output. -/
def okL0B : XIR :=
  .seq (.blk [.const eA (toWord (okM dB0M))]) (.seq (.load eW eA)
    (.ite eW (.seq (streamS stB20) (outIRB mBM)) (.blk [])))

/-- After level 1's decoder. -/
def okL1B : XIR :=
  .seq (.blk [.const eA (toWord (ok1M dB1M))]) (.seq (.load eW eA)
    (.ite eW (.seq (dec0S stB20) okL0B) (.blk [])))

/-- After level 2's decoder. -/
def okL2B : XIR :=
  .seq (.blk [.const eA (toWord (ok1M dB2M))]) (.seq (.load eW eA)
    (.ite eW (.seq (decMP1IR dB1M wB1M aB1M fB1M fB0M) okL1B) (.blk [])))

/-- **S2GB's node branch.** -/
def nodeB20 : XIR :=
  .seq (idxIR4D memM) (.seq (chainIRD (nChainS stB20) (chTabS stB20) sdL) (.seq read0B (.seq read1B (.seq read2B
    (.seq (acpS stB20) (.seq (thcpIR (resWS stB20) fB2M (3 * 2 ^ 9)) (.seq (decMP2IR dB2M wB2M aB2M fB2M fB1M)
      okL2B)))))))

/-- **S2GB's SNARK branch**: by the flag `b` (tape word 6). -/
def decXB20 : XIR := .seq (readAt rBb 6) (.ite rBb nodeB20 leafIR)

/-- The size range's ends. -/
abbrev loB : ℕ := piStatic P20B
/-- The size range's upper end. -/
abbrev hiB : ℕ := piStatic P20B + tailMax P20B

/-- `hiB` unfolded, once: the kernel checks `hiB ≡ piStatic P20B + tailMax P20B` by evaluating the schedule
(~4.6 M hb), so every use goes through this theorem. -/
theorem hiB_eq : hiB = piStatic P20B + tailMax P20B := rfl

theorem hiB_val : hiB = 285624 := by rw [hiB_eq, sizes_P20B.1.1, sizes_P20B.1.2.2.2.2.2.2]

/-- **S2GB's extractor program.** -/
def extXB20 : XProg := toProg memM mpwX (extIRWithB loB hiB decXB20)

/-! ## The specification -/

/-- The in-domain extractor: the program's decoded denotation. -/
def EdXB20 : Digest → Proof → Log → Option Wit := Eden memM mpwX (extIRWithB loB hiB decXB20)

/-- **The extractor outside the domain** at S2GB (`EoutXS` with the size range). -/
def EoutXB20 (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (_L : Log) : Option Wit :=
  if π.data[0]? = some 0x53 then
    (if SzB π then (if pw π 1 = 0 then some (leafW π) else search A (hdD π 2) c) else none)
  else WitnessSending.decode π

/-- **S2GB's extractor specification**: `EdXB20` on the domain, `EoutXB20 A` outside. -/
def EXB20 (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if InDomE c π L then EdXB20 c π L else EoutXB20 A c π L

end Lvm.XB

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open scoped NNReal ENNReal

section ChainB

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM} {Lm : ℝ≥0∞}
variable (f : SFmt) {VS : SProg} {vk : RecursionFast.Digest}

/-- **`kcertSMWSτ` at S2GB** (the same construction over `schemeSWB`). -/
noncomputable def kcertSMWBτ {τ : ℝ≥0∞} (hmid : MidSpecMτ mid Good εS Lm τ) (hτ : leadOpenM ≤ τ) (hLm : Lm ≤ εS)
    (hsh : MidShapeM mid) (X : ExtJMS mid Good VS vk) : KCert (schemeSWB f vk (PSWithM mid)) (Rel (accV VS vk)) :=
  kcertOfInv (S := schemeSWB f vk (PSWithM mid)) (εI := 7 * (2 : ℝ≥0)⁻¹ ^ 131) (εL := (2 : ℝ≥0)⁻¹ ^ 132)
    (Ext := ExtIM mid Good)
    (fun x ↦ (psInvMτ hmid hτ hLm hsh x).mono (fun _ h ↦ h) (fun _ _ h ↦ h) coe_εS.ge le_rfl le_rfl)
    zero_le (fun x _ hr ↦ NoGrind.reach_grindBits (ng_PSWithM hsh.noGrind x) hr)
    X.BL X.BL_nil X.BL_read X.BL_commit X.BL_group
    (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) X.ext X.extract

/-- **Its error**: `εFS ≤ 2^-128`. -/
theorem εFS_kcertSMWBτ {τ : ℝ≥0∞} (hmid : MidSpecMτ mid Good εS Lm τ) (hτ : leadOpenM ≤ τ) (hLm : Lm ≤ εS)
    (hsh : MidShapeM mid) (X : ExtJMS mid Good VS vk) :
    Scheme.εFS (kcertSMWBτ f hmid hτ hLm hsh X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  Scheme.εFS_le_of _ (by
    show (0 : ℝ≥0) + (7 * (2 : ℝ≥0)⁻¹ ^ 131 + (2 : ℝ≥0)⁻¹ ^ 132) + (2 : ℝ≥0)⁻¹ ^ 139 ≤ (2 : ℝ≥0)⁻¹ ^ 128
    rw [← NNReal.coe_le_coe]; push_cast; norm_num)

end ChainB

end Lvm.ASM

namespace Lvm.E2F

open RecursionFast Lvm.FS Lvm.T Lvm.ASM
open LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
variable {Lm : ℝ≥0∞} (f : SFmt)

/-- **`kcertSFWSτ` at S2GB** (over `schemeSWB`). -/
noncomputable def kcertSFWBτ {τ : ℝ≥0∞} (hm : MidSpecPinτ mid Good εS Lm τ) (hτ : leadOpenM ≤ τ) (hsh : MidShapeM mid)
    (hL : leadP Lm ≤ εS) {VS : SProg} {vk : RecursionFast.Digest} (X : ExtJMS (midP mid) Good VS vk) :
    KCert (schemeSWB f vk (PSWithM (midP mid))) (Rel (accV VS vk)) :=
  kcertSMWBτ f (midSpecP_ofτ hm hsh hL) hτ hL (midShapeP_of hsh) X

end Lvm.E2F

