-- New for lvm2 (WP S2-CERT): WP-16b's certificate glue at WP-16a's P20 node program (`M3.tabsP20`,
-- `LvmQAsmV`), split out of `LvmCertSFinal`: INB's `hinb20` gives `NodeHyp` from `NodeBase` (`nodeHyp20`).
-- Lvm2 roll 8 (wave L): `accMidHyp_P20`, `openS_of20` and `certificateR_node20` are gone with the bus certificate;
-- outside `certified`'s import closure.
import LvmCertSFinal
import LvmSubmissionS20
import LvmAccNodeTabs
import LvmQAsmInb

/-!
# The certificate at `M3.tabsP20`

* **`nodeHyp20`**: `NodeHyp` for WP-16a's P20 program from `NodeBase`, the position classes' cell
  bounds and Q_arith's no-`readd` fact (INB's `hinb20`);
* (gone at B1, with the bus certificate: `accMidHyp_P20` (L-D, with `length_pre20`), `openS_of20`,
  `certificateR_node20`: roll 7's certificate of `Lvm.T.submission` from `MidHyp M3.tabsP20`, `NodeHyp …`,
  `colsRegB`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm Lvm.M3 Lvm.VEq Lvm.Acc

section Node20

open Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.SigBits Lvm.NS LeanVM.Protocol
open Lvm.QAsm (cfg20 lay sigIn qarith nK aux QData PosCellsLt)

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {D : QData}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
    (aux cfg20 D), t.τ ≤ lay26.μ} {bpl : ℕ → ℕ → Bool × ℕ} {rest : List Tab} {pb : ℕ}

/-- **`NodeHyp` for WP-16a's P20 program** from `NodeBase`, the position classes' cell bounds and
Q_arith's no-`readd` fact `hna` (INB's `hinb20`). -/
theorem nodeHyp20
    (B : NodeBase (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ'
      bpl rest pb M3.tabsP20)
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    (hna : Lvm.Loop.Build.noReaddSegs (qarith cfg20 (Lvm.QAsm.p2C cfg20)).2 = true) :
    NodeHyp (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' bpl rest
      pb M3.tabsP20 :=
  { B with hinb := Lvm.QAsm.hinb20 (D := D) B.hT B.hst B.hQ B.hqlt hpc hna }

end Node20

end Lvm.ASM
