-- New for lvm2 S1 (E2-F, E2F-V): the tape's `24 × 1` Keccak GKR at `E2` in the doom calculus (the twins of
-- `LvmKeccakLayer.layerSpec`/`LvmKeccakCandidate.layerSpecS`, `LvmKeccakGkr.layersSpecS`/`tapeGkrSpec`) with
-- ground challenges (`doomE2Sample`, `sumcheckGSpec`, `packGSpec`) at one candidate and `εS`.
import LvmE2VGkrLayer
import LvmE2VZero
import LvmCertSNoGen

/-!
# The tape's GKR at `E2`

* the groups at `εS` (S2GF's `(c, g)`): `errG_c1`, `errG_c2`, `errG_c3`, `errG_c46`;
* `product_checkF`, `s_escapeG`, `quad_escapeG`, `final_checkF`: a layer's checks and escapes;
* **`layerSpecE2`**: one layer, from doom of the claim after the round to doom of the next claim;
* **`layersSpecE2`**: the 24 layers; **`tapeGkrSpecE2W`**: the lanes' zero test and the layers.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (States stAt Lb sbit Shape layerRCS afterRoundS statesOfS
  statesOfS_round segStateS laneWord tapeStates)
open Lvm.ASM (εS)
open Finset Polynomial
open scoped ENNReal

/-! ## The groups at `εS` (S2GF's grinding) -/

/-- One candidate, a ground group of numerator `c` at `g` bits, within `εS`. -/
theorem errG_le_εS {c g : ℕ} (h : grpEps 1 c g ≤ epsS) : ((1 : ℕ) : ℝ≥0∞) * errG g c + 0 ≤ εS := by
  rw [add_zero, errG_grpEpsE, grpEpsE_eq, εS, epsS_eq]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h)

theorem errG_c1 : ((1 : ℕ) : ℝ≥0∞) * errG gC1 1 + 0 ≤ εS := errG_le_εS table_min.2.1.1
theorem errG_c2 : ((1 : ℕ) : ℝ≥0∞) * errG gC2 2 + 0 ≤ εS := errG_le_εS table_min.2.1.2.1
theorem errG_c3 : ((1 : ℕ) : ℝ≥0∞) * errG gC3 3 + 0 ≤ εS := errG_le_εS table_min.2.1.2.2.1
theorem errG_c46 : ((1 : ℕ) : ℝ≥0∞) * errG gC46 46 + 0 ≤ εS := errG_le_εS table_min.2.1.2.2.2

/-! ## Claims -/

theorem sumF_mu {mu : List E2} (h : mu.length = 16) : sumF mu = ∑ i ∈ range 16, mu.getD i 0 := by
  rw [sumF_eq_sum, list_sum_getDF, h]

/-- **The product check** at a shape. -/
theorem product_checkF {sh : Shape} (hsh : sh.Ok) (T : States) (step P : ℕ) (claim : KClaim E2)
    (hshape : ClaimShapeF P claim) (product : List E2)
    (hG : ∀ c < 47, product.getD c 0 = (GpolyF T P claim.point claim.weights).coeff c)
    (hc : projectedF claim product + iotaSF sh (sh.logSteps P) step claim * sumF claim.mu =
      claim.value) :
    ClaimTrueF (afterRoundS sh T step) P claim := by
  rw [ClaimTrueF, claimSumF_roundS sh T step P _ _ _ hshape.2.1, ← hc, projectedF,
    projected_eqF claim.mu product hshape.1 _ hG, iota_eqSF hsh step P claim hshape.2.1,
    sumF_mu hshape.1]

/-- **The evaluation point's escape** at `E2`. -/
theorem s_escapeG {g : ℕ} (hg : g ≤ 64) {product : List E2} (hlen : product.length = 47)
    {G : E2[X]} (hG : G.natDegree ≤ 46) (h : ¬ ∀ c < 47, product.getD c 0 = G.coeff c) :
    avgE (fun c ↦ indE (powOK g c ∧ polyEvalF product (e2OfE c) = G.eval (e2OfE c))) ≤
      errG g 46 := by
  have hne : listPolyF product ≠ G := by
    intro he
    refine h fun c hc ↦ ?_
    rw [← he, listPolyF, finsetSum_coeff, Finset.sum_eq_single c]
    · simp
    · intro b _ hb; simp [coeff_C_mul, coeff_X_pow, Ne.symm hb]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  refine (avgE_mono fun s ↦ indE_mono fun hs ↦ ⟨hs.1, ?_⟩).trans
    (sampleG_escape hg hne ((natDegree_listPolyF product).trans (by omega)) hG)
  rw [eval_listPolyF]; exact hs.2

/-- **β's escape** at `E2`: distinct triples give distinct quadratics. -/
theorem quad_escapeG {g : ℕ} (hg : g ≤ 64) {t0 t1 t2 a0 a1 a2 : E2}
    (h : ¬ (t0 = a0 ∧ t1 = a1 ∧ t2 = a2)) :
    avgE (fun c ↦ indE (powOK g c ∧ t0 + e2OfE c * (t1 + e2OfE c * t2) =
      a0 + e2OfE c * (a1 + e2OfE c * a2))) ≤ errG g 2 := by
  let p : E2[X] := C t0 + C t1 * X + C t2 * X ^ 2
  let q : E2[X] := C a0 + C a1 * X + C a2 * X ^ 2
  have hdeg : ∀ x y z : E2, (C x + C y * X + C z * X ^ 2 : E2[X]).natDegree ≤ 2 := fun x y z ↦
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      ((natDegree_C _).trans_le (by norm_num)) ((natDegree_C_mul_le _ _).trans (by simp)))
      ((natDegree_C_mul_le _ _).trans (by simp))
  have hne : p ≠ q := by
    intro he
    refine h ⟨?_, ?_, ?_⟩
    · have := congrArg (coeff · 0) he; simpa [p, q] using this
    · have := congrArg (coeff · 1) he; simpa [p, q, coeff_X] using this
    · have := congrArg (coeff · 2) he; simpa [p, q, coeff_X] using this
  refine (avgE_mono fun b ↦ indE_mono fun hb ↦ ⟨hb.1, ?_⟩).trans
    (sampleG_escape hg hne (hdeg _ _ _) (hdeg _ _ _))
  simp only [p, q, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  linear_combination hb.2

/-- **The final check**. -/
theorem final_checkF (T : States) (P : ℕ) (s : E2) (w c L : List E2) (scale value : E2)
    (t : List E2) (hL : L.length = 11) (hw : w.length = 1600)
    (ht : t.getD 0 0 = TkF T P s c 0 L ∧ t.getD 1 0 = TkF T P s c 1 L ∧
      t.getD 2 0 = TkF T P s c 2 L)
    (hc : scale * dotF ((eqKernelF L).take keccakBits) w *
      (sumF (instWeightsF s) * t.getD 0 0 +
        (sumF (instWeightsF s) + t.getD 1 0) * t.getD 2 0) = value) :
    value = scale * phiF T P s w c L := by
  rw [← hc, dot_weightsF w L hL hw, kappa_eqF, ht.1, ht.2.1, ht.2.2, phiF]
  ring

/-! ## The layer as a program with projections -/

/-- A layer's tail: `t`, the final check, `β`, the next claim. -/
def layerTailE2 (claim : KClaim E2) (s : E2) (vsp : E2 × E2 × List E2) (lv : List E2 × E2) :
    VerifierProgram (KClaim E2) :=
  e2Reads 3 >>= fun t ↦
  VerifierProgram.require (vsp.2.1 * dotF ((eqKernelF lv.1).take keccakBits) claim.weights *
    (sumF (instWeightsF s) * t.getD 0 0 + (sumF (instWeightsF s) + t.getD 1 0) * t.getD 2 0) =
      lv.2) >>= fun _ ↦
  e2Sample gC2 >>= fun beta ↦
  pure ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), instWeightsF s, vsp.2.2,
    linearTransposeF (batchWF lv.1 beta)⟩

/-- A layer at a shape, with projections. -/
def layerProgE2 (sh : Shape) (logSteps step : ℕ) (claim : KClaim E2) : VerifierProgram (KClaim E2) :=
  e2Reads productBits >>= fun product ↦
  VerifierProgram.require (projectedF claim product + iotaSF sh logSteps step claim *
    sumF claim.mu = claim.value) >>= fun _ ↦
  e2Sep >>= fun _ ↦
  e2Sample gC46 >>= fun s ↦
  packRoundsE2 gC3 claim.point (polyEvalF product s) 1 >>= fun vsp ↦
  sumcheckE2 gC3 vsp.1 4 (List.replicate keccakLocalBits none) >>= fun lv ↦
  layerTailE2 claim s vsp lv

theorem verifyKeccakLayerE2_eq (sh : Shape) (logSteps step : ℕ) (claim : KClaim E2) :
    verifyKeccakLayerE2 sh logSteps step claim = layerProgE2 sh logSteps step claim := rfl

/-! ## The specifications -/

variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

/-- The separator keeps doom. -/
noncomputable def sepSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (A : β → Prop) {T' : ℝ≥0∞} :
    Spec e2Sep (Doomed C A) (fun _ h ↦ Doomed C A h) εS T' T' :=
  ((LeanVM.Protocol.EndToEnd.Front.doomSample (εmax := εS) (T := T') hst hcard A (fun _ ↦ A) 0
      fun q hq ↦ (avgE_le_of_le fun c ↦ (indE_of_not hq).le)).mono (fun _ h ↦ h)
      (fun _ _ h ↦ h) le_rfl (le_of_eq (by simp)) le_rfl).bind' fun _ ↦
    Spec.ret (Post := fun _ h ↦ Doomed C A h) ()

open Classical in
/-- The tail of a layer at `E2`. -/
noncomputable def tailSpecE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (Tq : β → States) (P : ℕ) (claim : KClaim E2) (hshape : ClaimShapeF P claim) (s : E2)
    (res : E2 × E2 × List E2) (hres : res.2.2.length = P + 1) (res2 : List E2 × E2)
    (hres2 : res2.1.length = 11) (hβ : ((1 : ℕ) : ℝ≥0∞) * errG gC2 2 + T ≤ εS) :
    Spec (layerTailE2 claim s res res2)
      (Doomed C (fun q ↦ res2.2 = res.2.1 * phiF (Tq q) P s claim.weights res.2.2 res2.1 ∧ R q))
      (fun c h ↦ ClaimShapeF P c ∧ Doomed C (fun q ↦ ClaimTrueF (Tq q) P c ∧ R q) h) εS 0 T :=
  (e2ReadsSpec (T := 0) hst _ zero_le 2).bind' fun t ↦
    (Spec.require (Pre := fun h ↦ t.length = 2 + 1 ∧ Doomed C (fun q ↦ res2.2 =
        res.2.1 * phiF (Tq q) P s claim.weights res.2.2 res2.1 ∧ R q) h)
      (Post := fun _ h ↦ Doomed C (fun q ↦ (t.getD 0 0 = TkF (Tq q) P s res.2.2 0 res2.1 ∧
        t.getD 1 0 = TkF (Tq q) P s res.2.2 1 res2.1 ∧
        t.getD 2 0 = TkF (Tq q) P s res.2.2 2 res2.1) ∧ R q) h)
      fun _ hpre hc ↦ Doomed.mono hpre.2 fun q ⟨ht, hR⟩ ↦
        ⟨final_checkF (Tq q) P s claim.weights res.2.2 res2.1 res.2.1 res2.2 t hres2
          hshape.2.2 ht hc, hR⟩).bind' fun _ ↦
      (doomE2SampleSpec (εmax := εS) (T := T) hst hcard _
        (fun b q ↦ t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0) =
          TkF (Tq q) P s res.2.2 0 res2.1 + b * (TkF (Tq q) P s res.2.2 1 res2.1 +
            b * TkF (Tq q) P s res.2.2 2 res2.1) ∧ R q) (errG gC2 2)
        (fun q hq ↦ by
          by_cases hR : R q
          · exact (avgE_mono fun b ↦ indE_mono fun hb ↦ ⟨hb.1, hb.2.1⟩).trans
              (quad_escapeG (by norm_num) fun h ↦ hq ⟨h, hR⟩)
          · exact (avgE_mono fun b ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans
              ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)) hβ).bind' fun b ↦
        (Spec.ret (Post := fun c h ↦ ClaimShapeF P c ∧
            Doomed C (fun q ↦ ClaimTrueF (Tq q) P c ∧ R q) h)
          (⟨t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0), instWeightsF s, res.2.2,
            linearTransposeF (batchWF res2.1 b)⟩ : KClaim E2)).mono
          (fun h hd ↦ ⟨⟨instWeightsF_length s, hres, linearTransposeF_length _⟩,
            Doomed.mono hd fun q ⟨htrue, hR⟩ ↦
              ⟨htrue.trans (batch_eqF (Tq q) P s res.2.2 res2.1 hres2 b).symm, hR⟩⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

open Classical in
/-- **One layer of the tape's GKR at `E2`**: from doom of "the claim holds of the states after the
round" to doom of "the next claim holds of the states before it". Lead `0`; groups `(46, 6)`,
`(3, 2)` per round, `(2, 2)` for `β` with the follower's `T`. -/
noncomputable def layerSpecE2 {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (Tq : β → States) (step P : ℕ) (claim : KClaim E2) (hshape : ClaimShapeF P claim)
    (hβ : ((1 : ℕ) : ℝ≥0∞) * errG gC2 2 + T ≤ εS) :
    Spec (verifyKeccakLayerE2 sh (sh.logSteps P) step claim)
      (Doomed C (fun q ↦ ClaimTrueF (afterRoundS sh (Tq q) step) P claim ∧ R q))
      (fun c h ↦ ClaimShapeF P c ∧ Doomed C (fun q ↦ ClaimTrueF (Tq q) P c ∧ R q) h) εS 0 T :=
  Spec.congr (verifyKeccakLayerE2_eq sh (sh.logSteps P) step claim).symm <|
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
    ((packGSpec (T := 0) hst hcard R (FPF_eqFamily P s claim.weights Tq claim.point hshape.2.1)
      le_rfl (g := gC3) (by norm_num) errG_c3 claim.point [] (polyEvalF product s) 1 rfl).mono
      (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨by
        rw [hv, one_mul, FPF_nil], hR⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun res ↦
    if hres : res.2.2.length = P + 1 then
      ((sumcheckGSpec (T := 0) hst hcard R
        (FXF_plainFamily P s claim.weights Tq res.2.2 res.2.1) (count := 4) (by norm_num)
        (by norm_num) (g := gC3) (by norm_num) errG_c3 11 [] res.1 (by simp)).mono
        (fun _ (hd : res.2.2.length = claim.point.length ∧ Doomed C _ _) ↦ Doomed.mono hd.2
          fun q ⟨hv, hR⟩ ↦ ⟨by
            rw [hv, FXF_nil, List.nil_append, FPF_full _ _ _ _ _ _ hshape.2.1 hres], hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun res2 ↦
      if hres2 : res2.1.length = 11 then
        (tailSpecE2 hst hcard R Tq P claim hshape s res hres res2 hres2 hβ).mono
          (fun _ (hd : res2.1.length = 11 ∧ Doomed C _ _) ↦ Doomed.mono hd.2 fun q ⟨hv, hR⟩ ↦
            ⟨by rw [hv, List.nil_append, FXF_full _ _ _ _ _ _ _ hres2], hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ h ↦ hres2 h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h ↦ hres (h.1.trans hshape.2.1)) (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl
  else Spec.dead.mono (fun _ h ↦ hlen h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

theorem claimTrue_roundSF {sh : Shape} (hsh : sh.Ok) (P : ℕ) (I : ℕ → ℕ → KeccakState) {d : ℕ}
    (hd : d < sh.depth) (c : KClaim E2) :
    ClaimTrueF (statesOfS sh P I d) P c ↔
      ClaimTrueF (afterRoundS sh (statesOfS sh P I (d + 1)) d) P c := by
  unfold ClaimTrueF
  rw [claimSumF_congr P (fun m x j hm hj ↦ statesOfS_round hsh P I hd m x j hm hj)]

open Classical in
/-- **The layers at a shape at `E2`, from depth `d`** (the twin of `layersSpecS`): lead `0`; each
layer's groups `(46, 6)`, `(3, 2)`, `(2, 2)` at one candidate, the last one's follower lead `T`. -/
noncomputable def layersSpecE2 {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop) (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ)
    (hβ : errG gC2 2 + T ≤ εS) :
    (n d : ℕ) → d + n + 1 = sh.depth → (claim : KClaim E2) → ClaimShapeF P claim →
      Spec (keccakLayersE2 sh (sh.logSteps P) (List.range' d (n + 1)) claim)
        (Doomed C (fun q ↦ ClaimTrueF (statesOfS sh P (Iq q) d) P claim ∧ R q))
        (fun c h ↦ ClaimShapeF P c ∧
          Doomed C (fun q ↦ ClaimTrueF (statesOfS sh P (Iq q) sh.depth) P c ∧ R q) h) εS 0 T
  | 0, d, hd, claim, hs =>
    ((layerSpecE2 (T := T) hsh hst hcard R (fun q ↦ statesOfS sh P (Iq q) (d + 1)) d P claim hs
      (by rw [Nat.cast_one, one_mul]; exact hβ)).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_roundSF hsh P (Iq q) (by omega) claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
    (Spec.ret (Post := fun c h ↦ ClaimShapeF P c ∧
        Doomed C (fun q ↦ ClaimTrueF (statesOfS sh P (Iq q) sh.depth) P c ∧ R q) h) c).mono
      (fun _ h' ↦ by rw [show d + 1 = sh.depth by omega] at h'; exact h') (fun _ _ h' ↦ h')
      le_rfl le_rfl le_rfl
  | n + 1, d, hd, claim, hs =>
    ((layerSpecE2 (T := 0) hsh hst hcard R (fun q ↦ statesOfS sh P (Iq q) (d + 1)) d P claim hs
      errG_c2).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_roundSF hsh P (Iq q) (by omega) claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
    if hc : ClaimShapeF P c then
      (layersSpecE2 hsh hst hcard R Iq P hβ n (d + 1) (by omega) c hc).mono
        (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h' ↦ hc h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

end Lvm.E2V
