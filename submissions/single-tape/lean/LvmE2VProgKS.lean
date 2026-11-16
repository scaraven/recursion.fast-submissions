-- New for lvm2 S1 (E2-F, E2F-V): the `KS` phase's and the `KS` link's programs at `E2` (split from LvmE2VKS so that the
-- middle phases and V_S import the programs without the specifications).
import LvmE2VProg

/-!
# `KS` and its link at `E2`: the programs

`verifyKeccakE2` (`verifyKeccak`, `12 × 2`), `callerProgE2` (`callerProg`), `ksLinkProgE2` (`ksLinkProg`); the
specifications are in `LvmE2VKS`.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The programs -/

/-- A column claim at `E2` (`ColumnClaim`): column, point, value. -/
structure ColClaimE2 where
  /-- The column. -/
  column : ℕ
  /-- The point. -/
  point : List E2
  /-- The value. -/
  value : E2

/-- `open` at `E2` (`keccakOpen`): slot rounds (`c = 2`), the folded weights, the last claim. -/
def keccakOpenE2 (logSteps : ℕ) (claim : KClaim E2) (first count : ℕ) (value : E2) :
    VerifierProgram (List E2 × List E2 × E2) :=
  sumcheckE2 gC2 value 3 (List.replicate qkeccakSlotBits none) >>= fun sv ↦
  pure (sv.1, foldRowsF sv.1 (slotWeightsF logSteps claim first count), sv.2)

/-- **`verify_keccak` at `E2`** (`verifyKeccak`, `12 × 2`). -/
def verifyKeccakE2 (logSteps : ℕ) (inst output : List E2) :
    VerifierProgram (List ColClaimE2 × List E2 × List E2) :=
  let packBits := logSteps - 4
  let rLow := inst.take 4
  e2Samples gC1 keccakSegmentBits >>= fun segment ↦
  e2Samples gC1 keccakLaneBits >>= fun lanePoint ↦
  (if 1 < keccakSegments then e2Read else pure 0) >>= fun committed ↦
  let first := firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed
  keccakLayersE2 LeanVM.Protocol.KeccakGkr.Shape.v1 logSteps (List.range keccakDepth) first >>= fun claim ↦
  (if 1 < keccakSegments then
      keccakOpenE2 logSteps first 1 (keccakSegments - 1) committed >>= fun o ↦
      e2Read >>= fun word ↦
      VerifierProgram.require (o.2.1.headD 0 * word = o.2.2) >>= fun _ ↦
      pure [(⟨qkeccak, rLow ++ inst.drop 4 ++ o.1, word⟩ : ColClaimE2)]
    else pure []) >>= fun outputs ↦
  sumcheckE2 gC2 claim.value 3 (List.replicate 4 none) >>= fun lv ↦
  keccakOpenE2 logSteps claim 0 keccakSegments lv.2 >>= fun o ↦
  e2Reads kBits >>= fun slices ↦
  VerifierProgram.require (multilinearEvalF claim.mu lv.1 * dotF o.2.1 slices = o.2.2) >>= fun _ ↦
  pure (outputs, lv.1 ++ claim.point.take packBits ++ o.1, slices)

/-- What the `KS` caller returns: `r`, the 25 scalars, the reduction's output, the row switch. -/
abbrev CallerOutE2 : Type := List E2 × List E2 × (List ColClaimE2 × List E2 × List E2) × (E × (List E → E))

/-- **The Keccak phase with caller claims at `E2`** (`callerProg`). -/
def callerProgE2 (h : ℕ) : VerifierProgram CallerOutE2 :=
  e2Samples gC1 h >>= fun r ↦
  e2Reads 25 >>= fun v ↦
  verifyKeccakE2 h r v >>= fun res ↦
  rowSwitch res.2.1 res.2.2 >>= fun row ↦
  pure (r, v, res, row)

/-- `Sc(ρ, ρ') = Σ_{i ∈ rows} eq(ρ, i)·eq(ρ', i − 1)` (`contShiftE`). -/
def contShiftF {F : Type} [Field F] (rows : List ℕ) (rho rho' : List F) : F :=
  sumF (rows.map fun i ↦ eqAtF rho i * eqAtF rho' (i - 1))

/-- The selector of the rows from the split, `Π_{j ≥ xl} ρ'_j` (`selX`). -/
def selXF {F : Type} [Field F] (xl : ℕ) (pt : List F) : F := prodF (pt.drop xl)

/-- **The `KS` link at `E2`** (`ksLinkProg`). -/
def ksLinkProgE2 (hk xl : ℕ) (rows : List ℕ) : VerifierProgram (List E2 × (List E2 × E2) × List E2) :=
  e2Samples gC1 (hk + 5) >>= fun kchal ↦
  sumcheckE2 gC2 0 3 (List.replicate hk none) >>= fun kshift ↦
  e2Reads 4 >>= fun vals ↦
  VerifierProgram.require (kshift.2 =
    contShiftF rows (kchal.take hk) kshift.1 * vals.getD 0 0 +
      eqEvalF (kchal.take hk) kshift.1 * (vals.getD 1 0 + vals.getD 2 0 +
        selXF xl kshift.1 * vals.getD 3 0)) >>= fun _ ↦
  pure (kchal, kshift, vals)

end Lvm.E2V
