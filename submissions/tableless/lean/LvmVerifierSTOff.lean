/- `LvmVerifierSTOff` (GOLF2 off-path move, group 37 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmTypedV, LvmVerifierST,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmTypedV
import LvmVerifierST

-- ===== from `LvmTypedV` =====

section
section
set_option autoImplicit false
namespace Lvm
open DM

theorem weightedS_eq (q : List FE) (eqL : Array FE) (lw : LWts) :
    weightedS q eqL lw = weightedRef (eqKernelA q) eqL lw.toList := by
  cases lw with
  | mat w => rfl
  | outer p laneW =>
    show (if (q.length == 6 && p.length == 6) = true then weightedC (corrA (corrTab q p)) eqL laneW
      else weightedRef (eqKernelA q) eqL (LWts.outer p laneW).toList) = _
    by_cases h : (q.length == 6 && p.length == 6) = true
    · simp only [h, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have hc : corrA (corrTab q p) = corrG (eqKernelA p) (eqKernelA q) := funext (corrA_eq q p h.1 h.2)
      rw [hc, weightedC_eq]; rfl
    · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem rcSum_eq (lw : LWts) (rc : UInt64) : rcSum lw rc = rcRef lw.toList rc := by
  cases lw with
  | mat w => rfl
  | outer p laneW => exact rcOuter_eq _ _ _

end Lvm
end
end

section
section
set_option autoImplicit false
namespace Lvm
open DM

theorem verifyKeccakLayerGS_eq (depth segs logSteps step : Nat) (c : SClaim) :
    (SClaim.toClaim <$> verifyKeccakLayerGS depth segs logSteps step c) =
      verifyKeccakLayerG depth segs logSteps step c.toClaim := by
  unfold verifyKeccakLayerGS verifyKeccakLayerG
  simp only [rcSum_eq, weightedS_eq, map_bind, map_pure, SClaim.toClaim, LWts.toList, outerUG, weightedRef, rcRef]

theorem keccakLayersGS_eq (depth segs logSteps : Nat) (steps : List Nat) (c : SClaim) :
    (SClaim.toClaim <$> keccakLayersGS depth segs logSteps steps c) =
      keccakLayersG depth segs logSteps steps c.toClaim := by
  induction steps generalizing c with
  | nil => rfl
  | cons st steps ih =>
    simp only [keccakLayersGS, keccakLayersG, map_bind, ih]
    rw [← verifyKeccakLayerGS_eq, bind_map_left]

end Lvm
end
end

section
section
set_option autoImplicit false
namespace Lvm
open DM

theorem dTapeS_eq (logN : Nat) : dTapeS logN = dTape logN := by
  unfold dTapeS dTape tapeGkrFS tapeGkrF
  have h (inst lp out : List FE) : keccakLayersG tapeDepth 1 logN (List.range tapeDepth) (tapeFirstClaimF inst lp out) =
      SClaim.toClaim <$> keccakLayersGS tapeDepth 1 logN (List.range tapeDepth)
        (SClaim.ofClaim (tapeFirstClaimF inst lp out)) := by
    rw [keccakLayersGS_eq]; simp [SClaim.toClaim, SClaim.ofClaim, LWts.toList]
  simp only [h, bind_map_left]

end Lvm
end
end

section
section
set_option autoImplicit false
namespace Lvm
open DM

/-- `KS`'s layers are the generic layers at `12 × 2`. -/
theorem keccakLayers_eq_G (logSteps : Nat) (steps : List Nat) (c : KeccakClaim) :
    keccakLayers logSteps steps c = keccakLayersG gkrDepth gkrSegments logSteps steps c := by
  induction steps generalizing c with
  | nil => rfl
  | cons st steps ih => simp only [keccakLayers, keccakLayersG, ih, verifyKeccakLayer_eq_G]

theorem verifyKeccakS_eq (logSteps : Nat) (inst output : List FE) :
    verifyKeccakS logSteps inst output = verifyKeccak logSteps inst output := by
  unfold verifyKeccakS verifyKeccak
  have h (first : KeccakClaim) : keccakLayers logSteps (List.range gkrDepth) first =
      SClaim.toClaim <$> keccakLayersGS gkrDepth gkrSegments logSteps (List.range gkrDepth)
        (SClaim.ofClaim first) := by
    rw [keccakLayersGS_eq, keccakLayers_eq_G]; simp [SClaim.toClaim, SClaim.ofClaim, LWts.toList]
  simp only [h, bind_map_left]

end Lvm
end
end

section
set_option autoImplicit false
namespace Lvm.TypedV
open Lvm DM
open Lvm.Typed (YSrc xVars yVars)

/-- The spec side's small claim is `onStackZBN 23`. -/
theorem onStackZBN_23 : onStackZBN 23 = Shape.onStackZB := rfl

end Lvm.TypedV
end

section
set_option autoImplicit false
namespace Lvm.TypedV
open Lvm DM
open Lvm.Typed (YSrc xVars yVars)

theorem decideProgTS_eq (p : Params) (N : TNat) (vk c : Vector UInt8 32) :
    decideProgTS p N vk c = decideProgT p N vk c := by
  unfold decideProgTS decideProgT
  simp only [dTapeS_eq, verifyKeccakS_eq]

end Lvm.TypedV
end

section
set_option autoImplicit false
namespace Lvm.TypedV
open Lvm DM
open Lvm.Typed (YSrc xVars yVars)

/-- The folded accumulator of the typed program. -/
def accOutOfT (p : Params) (N : TNat) (vk c : Vector UInt8 32) (sig : ByteArray) : Acc :=
  ((decideProgT p N vk c).runOn sig).1

end Lvm.TypedV
end

section
set_option autoImplicit false
namespace Lvm.TypedV
open Lvm DM
open Lvm.Typed (YSrc xVars yVars)

/-- **The split** (as `decideF_eq`): `decideFT = decideCoreT ∧ Φ_Q(accOutOfT) = y`. -/
theorem decideFT_eq (p : Params) (N : TNat) (vk c : Vector UInt8 32) (sig : ByteArray) :
    decideFT p N vk c sig =
      (decideCoreT p N vk c sig && N.phi (accOutOfT p N vk c sig).pt == (accOutOfT p N vk c sig).y) := by
  -- the three bodies by `delta` on the bare constants and the run generalized: `unfold` and the closing `rfl` left the
  -- kernel a `match` on `(decideProgT …).runOn sig`, which it reduced by running the program (GOLF-DEC2, after GOLF-HAR)
  have eF : @decideFT = @decideFT := rfl
  conv at eF => rhs; delta decideFT
  have eC : @decideCoreT = @decideCoreT := rfl
  conv at eC => rhs; delta decideCoreT
  have eA : @accOutOfT = @accOutOfT := rfl
  conv at eA => rhs; delta accOutOfT
  rw [eF, eC, eA]
  beta_reduce
  rewrite [decideProgTS_eq]
  generalize (decideProgT p N vk c).runOn sig = r
  rcases r with ⟨a, s⟩
  rfl

end Lvm.TypedV
end

-- ===== from `LvmVerifierST` =====

section
set_option autoImplicit false
namespace Lvm
open RecursionFast

/-- **The typed `V_S`** (lvm2 roll 8, B1: B-DES §1.2, the typed bus-free backend): parse, then drive the schedule
(`LvmSchedule.phases`, the typed phases: `LvmTypedVSched.scheduleT_eq`) and decide with `TypedV.decideFT` on the
native typed instance `N` (the regions with their targets, `Φ_Q`, the mini-bus's tables). -/
def VST (p : Params) (N : TypedV.TNat) (vk c : Digest) (π : Proof) : OProg Bool :=
  if parseOk p vk c π then drive p π (TypedV.decideFT p N vk c) else .ret false

/-- A rejected header asks no query (typed). -/
theorem VST_reject {p : Params} {N : TypedV.TNat} {vk c : Digest} {π : Proof} (h : parseOk p vk c π = false) :
    VST p N vk c π = .ret false := by
  simp [VST, h]

end Lvm
end
