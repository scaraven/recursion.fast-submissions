-- New for lvm6 K0: roll #34's Keccak GKR layer at `E2` (`LvmE2VProg.verifyKeccakLayerE2`,
-- `LvmE2VGkrSpec.layerSpecE2`/`layersSpecE2`) with the normalized pack rounds of leanVM #767 (`Lvm6KPack`), as
-- leanVM formal's `verifyKeccakLayerPacked` (`Protocol/Verifier/KeccakPack.lean`, `fdb317982`) reads it.
import LvmE2VGkrSpec
import Lvm6KPack

/-!
# The normalized Keccak layer at `E2`

`verifyKeccakLayerE2N` is `crates/verifier/src/keccak.rs:120-207` (`verify_keccak_layer`) on season 1's `E2`
transcript (ground challenges with their nonces, the separator after `U`): the product polynomial and its check,
`s`, the pack and segment rounds **normalized** (`packRoundsN`), the eleven position rounds, `t`, the final check
`dot(eq, w) · (κ t0 + (κ + t1) t2) = value` with **no scale factor**, `β`, the next claim. It differs from #34's
`verifyKeccakLayerE2` only in those two places.

* **`layerSpecE2N`**: from doom of "the claim holds of the states after the round" to doom of "the next claim
  holds of the states before it", the groups of #34's `layerSpecE2` (`(46, 6)`, `(3, 2)` per round, `(2, 2)`);
  the pack rounds through `packGNSpec` on `FPF_eqFamily` (unchanged: `FPF` is the normalized family), the
  position rounds on `FXF … 1`;
* **`layersSpecE2N`**: the layers of a shape from depth `d` (the twin of `layersSpecE2`).
-/

set_option autoImplicit false

namespace Lvm6.KPack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (States Shape afterRoundS statesOfS)
open Lvm.E2V
open Lvm.ASM (εS)
open scoped ENNReal

/-! ## The programs -/

/-- A normalized layer's tail: `t`, the final check (no scale), `β`, the next claim. -/
def layerTailE2N (claim : KClaim E2) (s : E2) (point : List E2) (lv : List E2 × E2) :
    VerifierProgram (KClaim E2) :=
  e2Reads 3 >>= fun t ↦
  VerifierProgram.require (dotF ((eqKernelF lv.1).take keccakBits) claim.weights *
    (sumF (instWeightsF s) * t.getD 0 0 + (sumF (instWeightsF s) + t.getD 1 0) * t.getD 2 0) =
      lv.2) >>= fun _ ↦
  e2Sample gC2 >>= fun beta ↦
  pure ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), instWeightsF s, point,
    linearTransposeF (batchWF lv.1 beta)⟩

/-- **One normalized layer of the GKR at the shape `sh`** at `E2` (`verifyKeccakLayerPacked`). -/
def verifyKeccakLayerE2N (sh : Shape) (logSteps step : ℕ) (claim : KClaim E2) :
    VerifierProgram (KClaim E2) :=
  e2Reads productBits >>= fun product ↦
  VerifierProgram.require (projectedF claim product + iotaSF sh logSteps step claim *
    sumF claim.mu = claim.value) >>= fun _ ↦
  e2Sep >>= fun _ ↦
  e2Sample gC46 >>= fun s ↦
  packRoundsN gC3 claim.point (polyEvalF product s) >>= fun vp ↦
  sumcheckE2 gC3 vp.1 4 (List.replicate keccakLocalBits none) >>= fun lv ↦
  layerTailE2N claim s vp.2 lv

/-- The normalized layers (`keccakLayersE2` with `verifyKeccakLayerE2N`). -/
def keccakLayersE2N (sh : Shape) (logSteps : ℕ) : List ℕ → KClaim E2 → VerifierProgram (KClaim E2)
  | [], claim => pure claim
  | step :: steps, claim =>
    verifyKeccakLayerE2N sh logSteps step claim >>= fun claim ↦ keccakLayersE2N sh logSteps steps claim

/-! ## The specifications -/

/-- **The final check, normalized**. -/
theorem final_checkFN (T : States) (P : ℕ) (s : E2) (w c L : List E2) (value : E2)
    (t : List E2) (hL : L.length = 11) (hw : w.length = 1600)
    (ht : t.getD 0 0 = TkF T P s c 0 L ∧ t.getD 1 0 = TkF T P s c 1 L ∧
      t.getD 2 0 = TkF T P s c 2 L)
    (hc : dotF ((eqKernelF L).take keccakBits) w *
      (sumF (instWeightsF s) * t.getD 0 0 +
        (sumF (instWeightsF s) + t.getD 1 0) * t.getD 2 0) = value) :
    value = 1 * phiF T P s w c L :=
  final_checkF T P s w c L 1 value t hL hw ht (by rw [one_mul]; exact hc)

variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

open Classical in
/-- The tail of a normalized layer at `E2`. -/
noncomputable def tailSpecE2N (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (Tq : β → States) (P : ℕ) (claim : KClaim E2) (hshape : ClaimShapeF P claim) (s : E2)
    (point : List E2) (hpoint : point.length = P + 1) (res2 : List E2 × E2)
    (hres2 : res2.1.length = 11) (hβ : ((1 : ℕ) : ℝ≥0∞) * errG gC2 2 + T ≤ εS) :
    Spec (layerTailE2N claim s point res2)
      (Doomed C (fun q ↦ res2.2 = 1 * phiF (Tq q) P s claim.weights point res2.1 ∧ R q))
      (fun c h ↦ ClaimShapeF P c ∧ Doomed C (fun q ↦ ClaimTrueF (Tq q) P c ∧ R q) h) εS 0 T :=
  (e2ReadsSpec (T := 0) hst _ zero_le 2).bind' fun t ↦
    (Spec.require (Pre := fun h ↦ t.length = 2 + 1 ∧ Doomed C (fun q ↦ res2.2 =
        1 * phiF (Tq q) P s claim.weights point res2.1 ∧ R q) h)
      (Post := fun _ h ↦ Doomed C (fun q ↦ (t.getD 0 0 = TkF (Tq q) P s point 0 res2.1 ∧
        t.getD 1 0 = TkF (Tq q) P s point 1 res2.1 ∧
        t.getD 2 0 = TkF (Tq q) P s point 2 res2.1) ∧ R q) h)
      fun _ hpre hc ↦ Doomed.mono hpre.2 fun q ⟨ht, hR⟩ ↦
        ⟨final_checkFN (Tq q) P s claim.weights point res2.1 res2.2 t hres2
          hshape.2.2 ht hc, hR⟩).bind' fun _ ↦
      (doomE2SampleSpec (εmax := εS) (T := T) hst hcard _
        (fun b q ↦ t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0) =
          TkF (Tq q) P s point 0 res2.1 + b * (TkF (Tq q) P s point 1 res2.1 +
            b * TkF (Tq q) P s point 2 res2.1) ∧ R q) (errG gC2 2)
        (fun q hq ↦ by
          by_cases hR : R q
          · exact (avgE_mono fun b ↦ indE_mono fun hb ↦ ⟨hb.1, hb.2.1⟩).trans
              (quad_escapeG (by norm_num) fun h ↦ hq ⟨h, hR⟩)
          · exact (avgE_mono fun b ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans
              ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)) hβ).bind' fun b ↦
        (Spec.ret (Post := fun c h ↦ ClaimShapeF P c ∧
            Doomed C (fun q ↦ ClaimTrueF (Tq q) P c ∧ R q) h)
          (⟨t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0), instWeightsF s, point,
            linearTransposeF (batchWF res2.1 b)⟩ : KClaim E2)).mono
          (fun h hd ↦ ⟨⟨instWeightsF_length s, hpoint, linearTransposeF_length _⟩,
            Doomed.mono hd fun q ⟨htrue, hR⟩ ↦
              ⟨htrue.trans (batch_eqF (Tq q) P s point res2.1 hres2 b).symm, hR⟩⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

open Classical in
/-- **One normalized layer of the GKR at `E2`**: from doom of "the claim holds of the states after the
round" to doom of "the next claim holds of the states before it". Lead `0`; groups `(46, 6)`, `(3, 2)` per
round, `(2, 2)` for `β` with the follower's `T`. -/
noncomputable def layerSpecE2N {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (Tq : β → States) (step P : ℕ) (claim : KClaim E2) (hshape : ClaimShapeF P claim)
    (hβ : ((1 : ℕ) : ℝ≥0∞) * errG gC2 2 + T ≤ εS) :
    Spec (verifyKeccakLayerE2N sh (sh.logSteps P) step claim)
      (Doomed C (fun q ↦ ClaimTrueF (afterRoundS sh (Tq q) step) P claim ∧ R q))
      (fun c h ↦ ClaimShapeF P c ∧ Doomed C (fun q ↦ ClaimTrueF (Tq q) P c ∧ R q) h) εS 0 T :=
  (e2ReadsSpec (T := 0) hst _ zero_le 46).bind' fun product ↦
  (Spec.require
    (Pre := fun h ↦ product.length = 46 + 1 ∧
      Doomed C (fun q ↦ ClaimTrueF (afterRoundS sh (Tq q) step) P claim ∧ R q) h)
    (Post := fun _ h ↦ product.length = 47 ∧ Doomed C (fun q ↦ (∀ c < 47, product.getD c 0 =
      (GpolyF (Tq q) P claim.point claim.weights).coeff c) ∧ R q) h)
    fun _ hpre hc ↦ ⟨hpre.1, Doomed.mono hpre.2 fun q ⟨hG, hR⟩ ↦
      ⟨product_checkF hsh (Tq q) step P claim hshape product hG hc, hR⟩⟩).bind' fun _ ↦
  if hlen : product.length = 47 then
    ((sepSpec (T' := 0) hst hcard _).mono (fun _ h ↦ h.2) (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl).bind' fun _ ↦
    (doomE2SampleSpec (εmax := εS) (T := 0) hst hcard _
      (fun s q ↦ polyEvalF product s = (GpolyF (Tq q) P claim.point claim.weights).eval s ∧ R q)
      (errG gC46 46) (fun q hq ↦ by
        by_cases hR : R q
        · exact (avgE_mono fun s ↦ indE_mono fun hs ↦ ⟨hs.1, hs.2.1⟩).trans
            (s_escapeG (by norm_num) hlen (natDegree_GpolyF _ _ _ _) fun h ↦ hq ⟨h, hR⟩)
        · exact (avgE_mono fun s ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans
            ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)) errG_c46).bind'
      fun s ↦
    ((packGNSpec (T := 0) hst hcard R
      (EqFamilyF.mono (FPF_eqFamily P s claim.weights Tq claim.point hshape.2.1) (by norm_num : 2 ≤ 3))
      (by norm_num) (g := gC3) (by norm_num) errG_c3 claim.point [] (polyEvalF product s) rfl).mono
      (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨by
        rw [hv, FPF_nil], hR⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun res ↦
    if hres : res.2.length = P + 1 then
      ((sumcheckGSpec (T := 0) hst hcard R
        (FXF_plainFamily P s claim.weights Tq res.2 1) (count := 4) (by norm_num)
        (by norm_num) (g := gC3) (by norm_num) errG_c3 11 [] res.1 (by simp)).mono
        (fun _ (hd : res.2.length = claim.point.length ∧ Doomed C _ _) ↦ Doomed.mono hd.2
          fun q ⟨hv, hR⟩ ↦ ⟨by
            rw [hv, FXF_nil, List.nil_append, FPF_full _ _ _ _ _ _ hshape.2.1 hres, one_mul], hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun res2 ↦
      if hres2 : res2.1.length = 11 then
        (tailSpecE2N hst hcard R Tq P claim hshape s res.2 hres res2 hres2 hβ).mono
          (fun _ (hd : res2.1.length = 11 ∧ Doomed C _ _) ↦ Doomed.mono hd.2 fun q ⟨hv, hR⟩ ↦
            ⟨by rw [hv, List.nil_append, FXF_full _ _ _ _ _ _ _ hres2], hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ h ↦ hres2 h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h ↦ hres (h.1.trans hshape.2.1)) (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl
  else Spec.dead.mono (fun _ h ↦ hlen h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

open Classical in
/-- **The normalized layers at a shape at `E2`, from depth `d`** (the twin of `layersSpecE2`): lead `0`;
each layer's groups `(46, 6)`, `(3, 2)`, `(2, 2)` at one candidate, the last one's follower lead `T`. -/
noncomputable def layersSpecE2N {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop) (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ)
    (hβ : errG gC2 2 + T ≤ εS) :
    (n d : ℕ) → d + n + 1 = sh.depth → (claim : KClaim E2) → ClaimShapeF P claim →
      Spec (keccakLayersE2N sh (sh.logSteps P) (List.range' d (n + 1)) claim)
        (Doomed C (fun q ↦ ClaimTrueF (statesOfS sh P (Iq q) d) P claim ∧ R q))
        (fun c h ↦ ClaimShapeF P c ∧
          Doomed C (fun q ↦ ClaimTrueF (statesOfS sh P (Iq q) sh.depth) P c ∧ R q) h) εS 0 T
  | 0, d, hd, claim, hs =>
    ((layerSpecE2N (T := T) hsh hst hcard R (fun q ↦ statesOfS sh P (Iq q) (d + 1)) d P claim hs
      (by rw [Nat.cast_one, one_mul]; exact hβ)).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_roundSF hsh P (Iq q) (by omega) claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
    (Spec.ret (Post := fun c h ↦ ClaimShapeF P c ∧
        Doomed C (fun q ↦ ClaimTrueF (statesOfS sh P (Iq q) sh.depth) P c ∧ R q) h) c).mono
      (fun _ h' ↦ by rw [show d + 1 = sh.depth by omega] at h'; exact h') (fun _ _ h' ↦ h')
      le_rfl le_rfl le_rfl
  | n + 1, d, hd, claim, hs =>
    ((layerSpecE2N (T := 0) hsh hst hcard R (fun q ↦ statesOfS sh P (Iq q) (d + 1)) d P claim hs
      errG_c2).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_roundSF hsh P (Iq q) (by omega) claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
    if hc : ClaimShapeF P c then
      (layersSpecE2N hsh hst hcard R Iq P hβ n (d + 1) (by omega) c hc).mono
        (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h' ↦ hc h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

end Lvm6.KPack
