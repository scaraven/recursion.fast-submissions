-- New for lvm2 E2-FT (E2F-C): the S2GF node program's Q_arith is V_S's decision (`harithF20`, roll 11's
-- `harithT20` at S2GF): from Q_arith's segments on a good pair's memory, `decideFFX P20F NTF20` accepts the child's
-- stream, composed by `core_of_phasesF` from the gadgets' phase lemmas (pin, typed, tape + wire, `KS`, `KS` link,
-- the opening) and `decideFFX_of`; the typed claims stand for V's (`typedClaimsC_ok`, `e3s_rel`).
import LvmE2QInst
import LvmE2QNodeG
import LvmE2QHarTop
import LvmE2QHarPos
import LvmQTypedHarB
import LvmQTypedHarS
import LvmE2QHarFront
import LvmE2QHarIn
import LvmE2QHarPosOk
import LvmE2QTypedReg
import LvmE2QHarGen
import LvmE2QInstOff

/-!
# Q_arith at S2GF (`harithF20`)

* **`qaF20`**: Q_arith of the S2GF node program (the root pin, the `E2` front, `qarithF`), so that
  `QF20 = toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qaF20)` (`QF20_qa`).
* **`harithF20`**: on a stream-block pair of the S2GF good relation whose memory carries the input map, with Q_link's
  `LaneLink`/`LinkOk`, Q_arith's segments ⇒ `decideFFX P20F NTF20 vk c_L Σ = true` (`nodeSoundFG`'s `harith`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed LeanVM.Protocol

-- `posLanesDec` is in `LvmE2QTypedReg` (moved, lvm2 U-TAPE).

-- `typedRegB`, `typedRegB_sound` are in `LvmE2QTypedReg` (moved, lvm2 U-TAPE).

/-- **The HAR's static checks at S2GF** (roll 11's `harChkB`: the regions and the phases' positions in `Σ`), decided
by the S2GF guard (`staticOkBF20`, natively): the circuit's typed regions are V_S's (`tdMatchB`), the typed phases
start on a lane boundary, end where the tape phase starts, and inside the stream; the opening starts inside the stream
(the front's lane bounds); every proof-of-work answer of the front is streamed with `g ≤ 64` (`powOkF`'s `hpw`).
(The opening's claim shapes follow with `open_phase`.) -/
def harChkBF20 : Bool :=
  Lvm.QTyped.tdMatchB tdataF20 NTF20 && typedPosF P20F % 8 == 0 &&
    typedEndX tdataF20 (typedPosF P20F) == posOf P20F (phaseItem0 P20F .tape) &&
    decide (typedEndX tdataF20 (typedPosF P20F) + 40 ≤ 8 * streamLanes P20F) &&
    decide (posOf P20F (phaseItem0 P20F .openMain) + 48 ≤ 8 * streamLanes P20F) &&
    (powFront P20F).all (fun a => decide (a.1 + 2 < streamLanes P20F) && decide (a.2 ≤ 64)) &&
    posOf P20F (phaseItem0 P20F .openMain) == 8 * (phaseLane P20F .openMain 0 - 5) &&
    Lvm.Har.LayOk (cfgMainF P20F (fun _ => 0) (fun _ => 0)) (streamLanes P20F) &&
    8 * Lvm.Har.stackEndL P20F.grind P20F.mainOod P20F.mainLevels (phaseLane P20F .openMain 0 - 5 + 15) ==
      hashedLen P20F &&
    decide (P20F.mainLevels.length ≤ (Lvm.QLink.opens P20F).length) && decide (1 ≤ 64 - P20F.grind) &&
    decide (Lvm.Fin.PosLanes P20F P20F.grind P20F.mainOod P20F.mainLevels (phaseLane P20F .openMain 0 - 5 + 15) 0) &&
    typedRegB tdataF20 (layout0 P20F).s

-- `cfgMainF_*`, `layOkF_pb` and the generic lemmas below `qaF20` are in `LvmE2QHarGen` (moved, lvm2 U-TAPE).

end Lvm.E2Q
