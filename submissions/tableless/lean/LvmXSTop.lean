-- New for lvm2 E2F (E2F-L, 2026-11-13): the extractor program generic in the stage (`decXM`/`extXM`/`EXM` of
-- `LvmMPXTop`/`LvmMPXComputes` with the stage's chain, cap and residual offsets, `C_main`'s root occupancy, `|π|`,
-- and the node output `outIRS` over the stage's trace blocks). Definitions only; the facts are in `LvmXSComputes`
-- (program) and `LvmXSOut` (output).
import LvmXSOutIR
import LvmMPXComputes

/-!
# The extractor program at a stage

* the chain: `tabEntS`, `chTabS`, `chainLS` (`chainIR` over the stage's messages `msgLS`);
* the node output **`outIRS`** (`LvmXSOutIR`);
* the node branch **`nodeS`** (`nodeM`'s steps at the stage's offsets `capWS`, `resWS`, `foldPosS` and `occ0`),
  **`decXS`**, **`extXS`**;
* the specification: `EdXS` (the program's denotation), `EoutXS` (outside the domain), **`EXS A`**.
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

/-! ## The chain -/

/-- One table entry: `tl`, the tape word of the message, two unused words (`q₀`: `tl = 7`). -/
def tabEntS (st : XStage) (p : ℕ) : List Word :=
  if p = 0 then [toWord 7, 0, 0, 0] else [toWord (32 + (msgLS st p).2), toWord (5 + (msgLS st p).1 / 8), 0, 0]

/-- **The chain's table**: entries `0 … nChainS`. -/
def chTabS (st : XStage) : List Word := (List.range (nChainS st + 1)).flatMap (tabEntS st)

/-- The log's position in the tape at the stage's `|π|`. -/
def pLS (st : XStage) : ℕ := posL st.pz

/-- **The chain scan** through position `nChainS st − 1`. -/
def chainLS (st : XStage) : XIR := chainIR (pLS st) (nChainS st) (chTabS st) sdL

/-! ## The node branch -/

/-- The tape word of `C_main`'s level-`i` cap. -/
def capWS (st : XStage) (i : ℕ) : ℕ := 5 + capOffS st i / 8

/-- The tape word of the residual. -/
def resWS (st : XStage) : ℕ := 5 + resOffS st / 8

/-- The fold challenges to `aB0M`, `aB1M`, `aB2M` (`acpM`). -/
def acpS (st : XStage) : XIR :=
  .seq (acp3IR (ansB + 4 * foldPosS st 0 0) aB0M 6) (.seq (acp3IR (ansB + 4 * foldPosS st 1 0) aB1M 4)
    (acp3IR (ansB + 4 * foldPosS st 2 0) aB2M 4))

/-- **S2GU's level-0 decoder** (lvm2 U-TAPE, decision D-WIN (B)): `eW := [n ≤ 2^18]` (`n` tape word 19, as
`streamM`); the small shape decodes lanes 32–39 (`decMP0IR … 32 8`), the big shape lanes 40–47 (`decMP0IRW`). Both
write the window to the same buffer. -/
def dec0U : XIR :=
  .seq (readAt eW 19) (.seq (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA])
    (.ite eW (decMP0IR 19 19 17 32 8 dB0M wB0M aB0M fB0M) (decMP0IRW dB0M wB0M aB0M fB0M)))

/-- **S2GU's stream block** from the decoded window: the stream starts the window in both shapes (small: window words
`2i`, big: window words `i`). -/
def streamU : XIR :=
  .seq (readAt eW 19) (.seq (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA])
    (.ite eW (mcpIR (2 ^ 19) winM 2 mBM) (mcpIR (2 ^ 19) winM 1 mBM)))

/-- The stage's level-0 decoder: S2GU's (`dec0U`) at stage `3`, M′'s window `40 … 47` otherwise. -/
def dec0S (st : XStage) : XIR := if st.p.stage = 3 then dec0U else decMP0IRW dB0M wB0M aB0M fB0M

/-- The stage's stream block: S2GU's (`streamU`) at stage `3`, `streamM` otherwise. -/
def streamS (st : XStage) : XIR := if st.p.stage = 3 then streamU else streamM

/-- After level 0's decoder: the stream block and the node output (`okL0`). -/
def okL0S (st : XStage) : XIR :=
  .seq (.blk [.const eA (toWord (okM dB0M))]) (.seq (.load eW eA)
    (.ite eW (.seq (streamS st) (outIRS st mBM)) (.blk [])))

/-- After level 1's decoder (`okL1`). -/
def okL1S (st : XStage) : XIR :=
  .seq (.blk [.const eA (toWord (ok1M dB1M))]) (.seq (.load eW eA)
    (.ite eW (.seq (dec0S st) (okL0S st)) (.blk [])))

/-- After level 2's decoder (`okL2`). -/
def okL2S (st : XStage) : XIR :=
  .seq (.blk [.const eA (toWord (ok1M dB2M))]) (.seq (.load eW eA)
    (.ite eW (.seq (decMP1IR dB1M wB1M aB1M fB1M fB0M) (okL1S st)) (.blk [])))

/-- Level 0's column read (`read0M` with the stage's root occupancy: `64 − occ0` zero words, then `occ0`). -/
def read0S (st : XStage) : XIR := readGIR memM (pLS st) (capWS st 0) wB0M (2 ^ 19) 11 (64 - st.occ0) st.occ0

/-- **The node branch at a stage** (`nodeM`). -/
def nodeS (st : XStage) : XIR :=
  .seq (idxIR4 memM (pLS st)) (.seq (chainLS st) (.seq (read0S st)
    (.seq (read1M memM (pLS st) (capWS st 1) wB1M) (.seq (read2M memM (pLS st) (capWS st 2) wB2M) (.seq (acpS st)
      (.seq (thcpIR (resWS st) fB2M (3 * 2 ^ 9)) (.seq (decMP2IR dB2M wB2M aB2M fB2M fB1M) (okL2S st))))))))

/-- **The SNARK branch at a stage**: by the flag `b` (tape word 6). -/
def decXS (st : XStage) : XIR := .seq (readAt rBb 6) (.ite rBb (nodeS st) leafIR)

/-- **The extractor program at a stage.** -/
def extXS (st : XStage) : XProg := extWithM st.pz (decXS st)

/-! ## The specification -/

/-- The in-domain extractor: the program's decoded denotation. -/
def EdXS (st : XStage) : Digest → Proof → Log → Option Wit := Eden memM mpwX (extIRWith st.pz (decXS st))

/-- **The extractor outside the domain** at a stage (`EoutX` at `|π| = st.pz`). -/
def EoutXS (st : XStage) (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (_L : Log) :
    Option Wit :=
  if π.data[0]? = some 0x53 then
    (if π.size = st.pz then (if pw π 1 = 0 then some (leafW π) else search A (hdD π 2) c) else none)
  else WitnessSending.decode π

/-- **The extractor specification at a stage**: `EdXS` on the domain, `EoutXS A` outside. -/
def EXS (st : XStage) (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if InDomE c π L then EdXS st c π L else EoutXS st A c π L

end Lvm.XS
