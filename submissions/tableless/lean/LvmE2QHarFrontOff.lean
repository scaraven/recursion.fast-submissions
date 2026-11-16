/- `LvmE2QHarFrontOff` (GOLF2 off-path move, group 46 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmE2QPlanF, LvmE2QNodeFacts, LvmE2QHarFront,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmE2QPlanF
import LvmE2QNodeFacts
import LvmE2QHarFront
import LvmE2QHarPosOff
import LvmChainTablePad
import LvmJBMutual
import LvmMlListLemmas
import LvmQAsmHar47
import LvmQShapeC
import LvmSpecRulesCert
import LvmTensorSwitch
import LvmVerifierF

-- ===== from `LvmE2QPlanF` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.Replay Lvm.PlanChk Lvm.QLink

/-- The plan has 3,959 entries. -/
theorem plan_P20F : (plan P20F).length = 3959 := (sound_of passR_P20F).2.2.1

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.Replay Lvm.PlanChk Lvm.QLink

/-- Every planned query at `P20F` is within `queryCap`. -/
theorem planCap_P20F : ∀ i < (plan P20F).length, ((plan P20F).getD i default).len ≤ queryCap :=
  planCap_ofR passR_P20F

end Lvm.E2Q
end

-- ===== from `LvmE2QNodeFacts` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay

/-- `P20F` at its own stage record is `P20F`. -/
theorem P20F_withF : P20F.withF accVF = P20F := rfl

end Lvm.E2Q
end

-- ===== from `LvmE2QHarFront` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Har Lvm.QSig Lvm.QAsm
variable {c : Ctx} {M : Mem}

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Har Lvm.QSig Lvm.QAsm
variable {c : Ctx} {M : Mem}

/-- The `KS` link's bounds at S2GF (stated at `cfgF20.p`, as `front_phasesG` reads them). -/
theorem blk_cfgF20 : spongeBlocks cfgF20.p - 1 < 2 ^ cfgF20.p.ksLog := by
  rw [show cfgF20.p = P20F from rfl, spongeBlocks_P20F.1]; decide

theorem ksp_cfgF20 : ksSplit cfgF20.p + 399 + 31 < 2 ^ cfgF20.p.ksLog := by
  rw [show cfgF20.p = P20F from rfl, ksSplit_P20F]; decide

set_option maxRecDepth 100000 in
/-- **The front's phases at `P20F`** (`front_phasesG` at `cfgF20`; roll 11's `p47_at` for `frontF cfgF20`): from the front's rows and assertions
(gate on), the proof-of-work answers (`powFront`), the row switches' words (the two `rowAux` blocks), `n'`'s bits and
range and the bits of `s'`, V's tape (with the wiring), `KS` and `KS` link phases run from their starts to the next
phase's start. -/
theorem front_phasesF {sig : ByteArray} {q : Ptr} (hS : Lvm.Q1.Streamed M sig (streamLanes P20F))
    (hTo : posOf P20F (phaseItem0 P20F .openMain) + 48 ≤ 8 * streamLanes P20F)
    (hg : M.k (pbB cfgF20) = 1) (hpow : Lvm.Q1.PowOkV (feAt sig) (powFront P20F))
    (hrw : ∀ j < 128, M.k (tBw cfgF20 + j) = rowWordD (Lvm.Q2.slicesOf M (wireSlices P20F)) j)
    (hrk : ∀ j < 128, M.k (tBk cfgF20 + j) = rowWordD (Lvm.Q2.slicesOf M (ksSlices P20F)) j)
    (pub : Pub) (hnb : ∀ j < 20, (kc ((sigIn cfgF20).bn + 2 + j)).val M = bitE pub.n j)
    (hn : 1 ≤ pub.n ∧ pub.n ≤ 2 ^ 20) (hsb : ∀ i < 256, M.k (bsB cfgF20 + i) = if sBitsD pub.s i then 1 else 0)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) (zc : Cell) (b : Bool)
    (hsm : b = true → pub.n ≤ 2 ^ 18) (h : Lvm.QSig.Ok c M (frontF cfgF20) q) :
    ∃ tp co lo,
      Lvm.Har.PhaseAt (tapeD P20F.logN (dSelBits P20F) (dSel P20F) pub.s pub.n) sig
        (posOf P20F (phaseItem0 P20F .tape)) (posOf P20F (phaseItem0 P20F .ks)) tp ∧
      Lvm.Har.PhaseAt (callerD P20F.ksLog) sig (posOf P20F (phaseItem0 P20F .ks))
        (posOf P20F (phaseItem0 P20F .ksLink)) co ∧
      Lvm.Har.PhaseAt (ksLinkD P20F.ksLog (ksXLog P20F) E2V.contRowsF) sig (posOf P20F (phaseItem0 P20F .ksLink))
        (posOf P20F (phaseItem0 P20F .openMain)) lo ∧
      List.Forall₂ (Lvm.Q2.FRelZ M zc b) (frontF cfgF20 q).1.cs (frontClaimsD P20F pub tp co lo) ∧
      vs M (frontF cfgF20 q).1.mb = selectorPoint (pub.n - 1) 20 := by
  rw [contRowsF_eq]
  exact front_phasesG (C := cfgF20) stE2_P20F alignF regs_P20F dsel_P20F
    blk_cfgF20 ksp_cfgF20 hS hTo hg hpow hrw hrk pub hnb hn hsb hh zc b
    hsm h

end Lvm.E2Q
end
