-- New for lvm6 K1: the v6 Keccak layer (K0's normalized layer without the separator, `FORMAT6.md` §6.2 row 8)
-- in the doom calculus: `layerSpec6`, `layersSpec6` (the proofs of K0's `layerSpecE2N`/`layersSpecE2N`
-- with the separator's step removed).
import Lvm6KProg

/-!
# The v6 layers

`layer6Sh sh` is `layer6` at a GKR shape (`layer6 = layer6Sh Shape.v1`, `layer6_eq`). `layerSpec6`,
`layersSpec6`: K0's statements for the program without `e2Sep` (groups `(46, 6)`, `(3, 2)` per round,
`(2, 2)` for `β`; lead `0`).
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (States Shape afterRoundS statesOfS)
open Lvm.E2V Lvm6.KPack
open Lvm.ASM (εS)
open scoped ENNReal

/-- `layer6` at the GKR shape `sh`. -/
def layer6Sh (sh : Shape) (logSteps step : ℕ) (claim : KClaim E2) : VerifierProgram (KClaim E2) :=
  e2Reads productBits >>= fun product ↦
  VerifierProgram.require (projectedF claim product + iotaSF sh logSteps step claim *
    sumF claim.mu = claim.value) >>= fun _ ↦
  e2Sample gC46 >>= fun s ↦
  packRoundsN gC3 claim.point (polyEvalF product s) >>= fun vp ↦
  sumcheckE2 gC3 vp.1 4 (List.replicate keccakLocalBits none) >>= fun lv ↦
  layerTailE2N claim s vp.2 lv

/-- The layers at `sh`. -/
def layers6Sh (sh : Shape) (logSteps : ℕ) : List ℕ → KClaim E2 → VerifierProgram (KClaim E2)
  | [], claim => pure claim
  | step :: steps, claim => layer6Sh sh logSteps step claim >>= fun c ↦ layers6Sh sh logSteps steps c

theorem layers6_eq (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KClaim E2),
    layers6 logSteps steps claim = layers6Sh Shape.v1 logSteps steps claim
  | [], _ => rfl
  | step :: steps, claim => by
    rw [layers6, layers6Sh]
    exact congrArg _ (funext fun c ↦ layers6_eq logSteps steps c)

variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

open Classical in
/-- **One normalized layer of the GKR at `E2`**: from doom of "the claim holds of the states after the
round" to doom of "the next claim holds of the states before it". Lead `0`; groups `(46, 6)`, `(3, 2)` per
round, `(2, 2)` for `β` with the follower's `T`. -/
noncomputable def layerSpec6 {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (Tq : β → States) (step P : ℕ) (claim : KClaim E2) (hshape : ClaimShapeF P claim)
    (hβ : ((1 : ℕ) : ℝ≥0∞) * errG gC2 2 + T ≤ εS) :
    Spec (layer6Sh sh (sh.logSteps P) step claim)
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
    ((doomE2SampleSpec (εmax := εS) (T := 0) hst hcard _
      (fun s q ↦ polyEvalF product s = (GpolyF (Tq q) P claim.point claim.weights).eval s ∧ R q)
      (errG gC46 46) (fun q hq ↦ by
        by_cases hR : R q
        · exact (avgE_mono fun s ↦ indE_mono fun hs ↦ ⟨hs.1, hs.2.1⟩).trans
            (s_escapeG (by norm_num) hlen (natDegree_GpolyF _ _ _ _) fun h ↦ hq ⟨h, hR⟩)
        · exact (avgE_mono fun s ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans
            ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)) errG_c46).mono
      (fun _ h ↦ h.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind'
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
noncomputable def layersSpec6 {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop) (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ)
    (hβ : errG gC2 2 + T ≤ εS) :
    (n d : ℕ) → d + n + 1 = sh.depth → (claim : KClaim E2) → ClaimShapeF P claim →
      Spec (layers6Sh sh (sh.logSteps P) (List.range' d (n + 1)) claim)
        (Doomed C (fun q ↦ ClaimTrueF (statesOfS sh P (Iq q) d) P claim ∧ R q))
        (fun c h ↦ ClaimShapeF P c ∧
          Doomed C (fun q ↦ ClaimTrueF (statesOfS sh P (Iq q) sh.depth) P c ∧ R q) h) εS 0 T
  | 0, d, hd, claim, hs =>
    ((layerSpec6 (T := T) hsh hst hcard R (fun q ↦ statesOfS sh P (Iq q) (d + 1)) d P claim hs
      (by rw [Nat.cast_one, one_mul]; exact hβ)).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_roundSF hsh P (Iq q) (by omega) claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
    (Spec.ret (Post := fun c h ↦ ClaimShapeF P c ∧
        Doomed C (fun q ↦ ClaimTrueF (statesOfS sh P (Iq q) sh.depth) P c ∧ R q) h) c).mono
      (fun _ h' ↦ by rw [show d + 1 = sh.depth by omega] at h'; exact h') (fun _ _ h' ↦ h')
      le_rfl le_rfl le_rfl
  | n + 1, d, hd, claim, hs =>
    ((layerSpec6 (T := 0) hsh hst hcard R (fun q ↦ statesOfS sh P (Iq q) (d + 1)) d P claim hs
      errG_c2).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_roundSF hsh P (Iq q) (by omega) claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
    if hc : ClaimShapeF P c then
      (layersSpec6 hsh hst hcard R Iq P hβ n (d + 1) (by omega) c hc).mono
        (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h' ↦ hc h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

end Lvm6.K
