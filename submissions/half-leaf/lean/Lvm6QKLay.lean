-- New for lvm6 (WP CB-L). One normalized Keccak GKR layer in the node circuit (FORMAT6 §6.2 row 8,
-- K0's `layer6`) as a straight-line `BM` gadget, its HAR (`LayerHarStmt layer6G`), and the 12
-- layers chained (`layers6G`, the HAR of `layers6 κ (List.range 12)`).
import Lvm6QKLayKit

/-!
# One Keccak layer (generator and HAR)

Lanes of a layer from `q` (`P18.layer κ` = `E(47) G(6) (κ−3)×R(2,2) 11×R(3,2) E(3) G(2)`): the
product at `q + 2k`; `s` at `lA q + 1`; the pack rounds from `lB q`; the position rounds from
`lC κ q`; `t₀ t₁ t₂` at `lD κ q`; `β` at `lE κ q + 1`. The next layer starts at
`layEnd (P18.layer κ) q` (`296 + 14(κ − 3)` lanes on).

* **`layBody`**: the layer on a claim whose seven iota weights `W(2^i − 1)` are `fs` and whose
  final-check weight is computed by `dotG`: the asserted product check
  `projected + ι·Σμ = value`, `instWeightsF s`, Horner, `eqRounds6`, `sc4 11`, the asserted final
  check, the next value. **`layBody_har`**.
* **`layer6G`**: dispatches on the claim's weights (`WRep`): `first rl` (lane table, `x^z`
  constants) or `lt pos β` (lane weights `laneWB`, the slice table, flip forms, the rotated-sum
  tables); an `lt` claim whose `pos` is not 11 long gets a failing assertion (`failG`).
  **`layer6G_har : LayerHarStmt layer6G`**.
* **`layers6G κ q claim gate`**: the 12 layers (steps `0 … 11`), each `layEnd (P18.layer κ)`
  lanes after the last; **`layers6G_runs`**: it re-executes `layers6 κ (List.range 12)` on
  `rep 12 (P18.layer κ)` and hands on an `lt` claim with 11 position cells.
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters (E2)
open LeanVM.Protocol.KeccakGkr (Shape)
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K Lvm6.KPack
open Lvm.Q1 (iotaPos)
open Lvm6 (Item rep rnd)

variable {c : Ctx} {M : Mem}

/-! ## Lanes and the program side -/

/-- The nonce lane of `s` (its answer one lane on). -/
abbrev lA (q : ℕ) : ℕ := layEnd [.E 47] q
/-- The first pack round. -/
abbrev lB (q : ℕ) : ℕ := layEnd [.G 6] (lA q)
/-- The first position round. -/
abbrev lC (κ q : ℕ) : ℕ := layEnd (rep (κ - 3) (rnd 2 2)) (lB q)
/-- `t₀`. -/
abbrev lD (κ q : ℕ) : ℕ := layEnd (rep 11 (rnd 3 2)) (lC κ q)
/-- The nonce lane of `β`. -/
abbrev lE (κ q : ℕ) : ℕ := layEnd [.E 3] (lD κ q)

theorem lay_layer (κ : ℕ) : P18.layer κ =
    [.E 47] ++ ([.G 6] ++ (rep (κ - 3) (rnd 2 2) ++ (rep 11 (rnd 3 2) ++ ([.E 3] ++ [.G 2])))) := by
  simp only [Lvm6.Shape.layer, List.append_assoc]
  rfl

/-- A `require` that holds reads nothing (its decision procedure taken from the program). -/
theorem runs_require' {c : Prop} {inst : Decidable c} (hc : c) :
    Runs M [] (@LeanVM.Protocol.Compile.VerifierProgram.require c inst) fun _ ↦ True :=
  fun _ evs he ↦ by
    cases he
    exact ⟨(), by simp [LeanVM.Protocol.Compile.VerifierProgram.require, hc,
      LeanVM.Protocol.Compile.VerifierProgram.after], trivial⟩

/-- **The layer's tail on the stream** (`t₀ t₁ t₂` from `r`, the final check, `β`). -/
theorem runs_layerTail (M : Mem) (cl : KClaim E2) (s : E2) (pt' lpv : List E2) (fin : E2) (r : ℕ)
    (hB : dotF ((eqKernelF lpv).take LeanVM.Protocol.Verifier.keccakBits) cl.weights *
      (sumF (instWeightsF s) * ev2 M (ld2 r) + (sumF (instWeightsF s) + ev2 M (ld2 (r + 2))) *
        ev2 M (ld2 (r + 4))) = fin) :
    Runs M (layItems [.E 3] r ++ layItems [.G 2] (layEnd [.E 3] r)) (layerTailE2N cl s pt' (lpv, fin))
      (fun cl' ↦ cl' = ⟨ev2 M (ld2 r) + ev2 M (ld2 (layEnd [.E 3] r + 1)) * (ev2 M (ld2 (r + 2)) +
        ev2 M (ld2 (layEnd [.E 3] r + 1)) * ev2 M (ld2 (r + 4))), instWeightsF s, pt',
        linearTransposeF (batchWF lpv (ev2 M (ld2 (layEnd [.E 3] r + 1))))⟩) := by
  have e : scal M r 3 = [ev2 M (ld2 r), ev2 M (ld2 (r + 2)), ev2 M (ld2 (r + 4))] := by
    simp [scal, List.range_succ]
  unfold layerTailE2N
  refine runs_bind (runs_e2Reads' M 3 r) fun t ht ↦ ?_
  rw [ht, e]
  refine runs_bind' (l₁ := []) (List.nil_append _).symm (runs_require' hB) fun _ _ ↦ ?_
  refine runs_bind' (l₂ := []) (List.append_nil _).symm (runs_e2Sample' M (by norm_num) _)
    fun β hβ ↦ runs_pure ?_
  subst hβ
  rfl

/-- **`layer6` on the stream**, from the two checks and the two sumchecks' runs. -/
theorem runs_layer6 (M : Mem) (κ step q : ℕ) (cl : KClaim E2)
    (hA : projectedF cl (scal M q 47) + iotaSF Shape.v1 κ step cl * sumF cl.mu = cl.value)
    (v1 : E2) (pt' : List E2)
    (hpack : Runs M (layItems (rep (κ - 3) (rnd 2 2)) (lB q))
      (packRoundsN gC3 cl.point (polyEvalF (scal M q 47) (ev2 M (ld2 (lA q + 1)))))
      (fun res ↦ res.1 = v1 ∧ res.2 = pt'))
    (lpv : List E2) (fin : E2)
    (hsc : Runs M (layItems (rep 11 (rnd 3 2)) (lC κ q)) (sumcheckE2 gC3 v1 4 (List.replicate 11 none))
      (fun res ↦ res.1 = lpv ∧ res.2 = fin))
    (hB : dotF ((eqKernelF lpv).take LeanVM.Protocol.Verifier.keccakBits) cl.weights *
      (sumF (instWeightsF (ev2 M (ld2 (lA q + 1)))) * ev2 M (ld2 (lD κ q)) +
        (sumF (instWeightsF (ev2 M (ld2 (lA q + 1)))) + ev2 M (ld2 (lD κ q + 2))) *
          ev2 M (ld2 (lD κ q + 4))) = fin) :
    Runs M (layItems (P18.layer κ) q) (layer6 κ step cl) (fun cl' ↦ cl' =
      ⟨ev2 M (ld2 (lD κ q)) + ev2 M (ld2 (lE κ q + 1)) * (ev2 M (ld2 (lD κ q + 2)) +
        ev2 M (ld2 (lE κ q + 1)) * ev2 M (ld2 (lD κ q + 4))), instWeightsF (ev2 M (ld2 (lA q + 1))),
        pt', linearTransposeF (batchWF lpv (ev2 M (ld2 (lE κ q + 1))))⟩) := by
  rw [lay_layer]
  simp only [layItems_append]
  unfold layer6
  refine runs_bind (runs_e2Reads' M 47 q) fun product hprod ↦ ?_
  subst hprod
  refine runs_bind' (l₁ := []) (List.nil_append _).symm (runs_require' hA) fun _ _ ↦ ?_
  refine runs_bind (runs_e2Sample' M (by norm_num) _) fun s hs ↦ ?_
  subst hs
  refine runs_bind hpack fun vp hvp ↦ ?_
  rw [hvp.1, hvp.2]
  refine runs_bind hsc fun lv hlv ↦ ?_
  obtain rfl : lv = (lpv, fin) := Prod.ext hlv.1 hlv.2
  have hT := runs_layerTail M cl (ev2 M (ld2 (lA q + 1))) pt' lpv fin (lD κ q) hB
  exact hT

/-! ## Lengths of the round gadgets' outputs -/

theorem hs_eqRounds6_len : ∀ (q : ℕ) (value : C2) (rs : List C2),
    Hs c M (eqRounds6 q value rs) fun o ↦ o.2.length = rs.length
  | _, _, [] => hs_pure rfl
  | q, value, r :: rs => hs_bind (hs_eqRound6 q value r) fun rc _ ↦
    hs_bind (hs_eqRounds6_len (q + 14) rc.2 rs) fun res hres ↦ hs_pure (by simp [hres])

theorem hs_sc4_len : ∀ (R q : ℕ) (claim : C2), Hs c M (sc4 R q claim) fun o ↦ o.1.length = R
  | 0, _, _ => hs_pure rfl
  | R + 1, q, claim => hs_bind (hs_sc4Round q claim) fun rc _ ↦
    hs_bind (hs_sc4_len R (q + 16) rc.2) fun res hres ↦ hs_pure (by simp [hres])

/-! ## The layer's body -/

/-- **The layer on a claim** whose iota weights are `fs` and whose final-check weight is `dotG`. -/
def layBody (κ step q : ℕ) (claim : ClaimC) (gate : Cell) (z one : C2) (fs : List C2)
    (dotG : List C2 → BM C2) : BM ClaimC :=
  let prodC := (List.range 47).map fun k ↦ ld2 (q + 2 * k)
  let s := ld2 (lA q + 1)
  let t0 := ld2 (lD κ q)
  let t1 := ld2 (lD κ q + 2)
  let t2 := ld2 (lD κ q + 4)
  let β := ld2 (lE κ q + 1)
  let r := claim.point.getD (κ - 4) z
  projG z claim.mu prodC >>= fun proj ↦
  iotaG z step 0 fs >>= fun i0 ↦ iotaG z step 1 fs >>= fun i1 ↦
  g2One r >>= fun r1 ↦ g2Mul r1 i0 z >>= fun u ↦ g2Mul r i1 u >>= fun iota ↦
  g2Sum z claim.mu >>= fun sm ↦ g2Mul iota sm proj >>= fun e1 ↦ g2Add e1 claim.value >>= fun e1' ↦
  g2Assert e1' gate >>= fun _ ↦
  instG z one s >>= fun mu' ↦ g2Sum z mu' >>= fun kap ↦
  hornerG z s prodC >>= fun v0 ↦
  eqRounds6 (lB q) v0 claim.point >>= fun vp ↦
  sc4 11 (lC κ q) vp.1 >>= fun lc ↦
  dotG lc.1 >>= fun dot ↦
  g2Mul kap t0 z >>= fun kt0 ↦ g2Add kap t1 >>= fun k1 ↦ g2Mul k1 t2 kt0 >>= fun m ↦
  g2Mul dot m lc.2 >>= fun e2 ↦ g2Assert e2 gate >>= fun _ ↦
  g2Mul β t2 t1 >>= fun tt ↦ g2Mul β tt t0 >>= fun v' ↦
  pure ⟨v', mu', vp.2, .lt lc.1 β⟩

/-- An `lt` claim with 11 position cells. -/
abbrev LtS (w : WRep) : Prop := ∃ pos β, w = .lt pos β ∧ pos.length = 11

/-- **The body re-executes `layer6`**, both checks included. -/
theorem layBody_har (κ : ℕ) (hκ : 5 ≤ κ) (step : ℕ) (hstep : step < 12) (q : ℕ) (claim : ClaimC)
    (gate : Cell) (hg : gate.val M = 1) (hpt : claim.point.length = κ - 3) (cl : KClaim E2)
    (hrep : ClaimRep M claim cl) {z one : C2} (hz : z.val M = 0) (hone : one.val M = 1) (fs : List C2)
    (hfs : fs.map (ev2 M) = (List.range 7).map fun i ↦ cl.weights.getD (iotaPos i) 0)
    (dotG : List C2 → BM C2)
    (hdot : ∀ lp : List C2, lp.length = 11 → Hs c M (dotG lp) fun d ↦
      ev2 M d = dotF ((eqKernelF (lp.map (ev2 M))).take LeanVM.Protocol.Verifier.keccakBits) cl.weights) :
    HsA c M (layBody κ step q claim gate z one fs dotG) fun o ↦
      Runs M (layItems (P18.layer κ) q) (layer6 κ step cl)
        (fun cl' ↦ ClaimRep M o cl' ∧ o.point.length = κ - 3 ∧ LtS o.w) := by
  obtain ⟨hv, hmu, hpt', -⟩ := hrep
  have hz' := ev2_zero hz
  have hprod : ((List.range 47).map fun k ↦ ld2 (q + 2 * k)).map (ev2 M) = scal M q 47 := by
    rw [List.map_map]
    rfl
  unfold layBody
  refine hsA_bind (hsA_of_hs (hs_projG hz claim.mu _ cl hmu _ hprod)) fun proj hproj ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_iotaG hz step 0 hstep (by norm_num) fs cl.weights hfs)) fun i0 hi0 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_iotaG hz step 1 hstep (by norm_num) fs cl.weights hfs)) fun i1 hi1 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs2_one _)) fun r1 hr1 ↦ hsA_bind (hsA_of_hs (hs2_mul _ _ _)) fun u hu ↦
    hsA_bind (hsA_of_hs (hs2_mul _ _ _)) fun iota hiota ↦ hsA_bind (hsA_of_hs (hs2_sum _ _)) fun sm hsm ↦
    hsA_bind (hsA_of_hs (hs2_mul _ _ _)) fun e1 he1 ↦ hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun e1' he1' ↦
    hsA_bind (hsA_g2Assert e1' gate hg) fun _ hE1 ↦ ?_
  have hA : projectedF cl (scal M q 47) + iotaSF Shape.v1 κ step cl * sumF cl.mu = cl.value := by
    have h0 : e1.val M = claim.value.val M := by
      rw [he1'] at hE1
      linear_combination hE1 - claim.value.val M * CharTwo.two_eq_zero (R := FE2)
    have h1 : ev2 M e1 = ev2 M claim.value := by simp only [ev2, h0]
    rw [iotaSF_two κ step cl hκ (by rw [← hpt', List.length_map, hpt]), ← hproj, ← hi0, ← hi1,
      ← ev2_getDz hpt' hz' (κ - 4), ← hv, sumF_eq_sum, ← hmu, ← h1, he1, hiota, hu, hr1, hsm, hz']
    ring
  refine hsA_bind (hsA_of_hs (hs_instG hz hone _)) fun mu' hmu' ↦
    hsA_bind (hsA_of_hs (hs2_sum _ _)) fun kap hkap ↦ hsA_bind (hsA_of_hs (hs_hornerG hz _ _)) fun v0 hv0 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_and (eqRounds6_runs (c := c) gC3 (by norm_num) (lB q) v0 claim.point)
    (hs_eqRounds6_len _ _ _))) fun vp ⟨hvp, hvpl⟩ ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_and (sc4_runs (c := c) gC3 (by norm_num) 11 (lC κ q) vp.1)
    (hs_sc4_len _ _ _))) fun lc ⟨hlc, hlcl⟩ ↦ ?_
  refine hsA_bind (hsA_of_hs (hdot lc.1 hlcl)) fun dot hdt ↦ ?_
  refine hsA_bind (hsA_of_hs (hs2_mul _ _ _)) fun kt0 hkt0 ↦ hsA_bind (hsA_of_hs (hs2_add _ _)) fun k1 hk1 ↦
    hsA_bind (hsA_of_hs (hs2_mul _ _ _)) fun m hm ↦ hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun e2 he2 ↦
    hsA_bind (hsA_g2Assert e2 gate hg) fun _ hE2 ↦ hsA_bind (hsA_of_hs (hs2_mul _ _ _)) fun tt htt ↦
    hsA_bind (hsA_of_hs (hs2_mul _ _ _)) fun v' hv' ↦ hsA_pure ?_
  have hB : dotF ((eqKernelF (lc.1.map (ev2 M))).take LeanVM.Protocol.Verifier.keccakBits) cl.weights *
      (sumF (instWeightsF (ev2 M (ld2 (lA q + 1)))) * ev2 M (ld2 (lD κ q)) +
        (sumF (instWeightsF (ev2 M (ld2 (lA q + 1)))) + ev2 M (ld2 (lD κ q + 2))) *
          ev2 M (ld2 (lD κ q + 4))) = ev2 M lc.2 := by
    have h0 : dot.val M * m.val M = lc.2.val M := by
      rw [he2] at hE2
      linear_combination hE2 - lc.2.val M * CharTwo.two_eq_zero (R := FE2)
    have h1 : ev2 M dot * ev2 M m = ev2 M lc.2 := by simp only [ev2, ← FE2.fe2_mul_eq, h0]
    rw [← h1, hdt, hm, hk1, hkt0, hkap, hz', hmu', sumF_eq_sum]
    ring
  rw [hpt, hpt', hv0, hprod] at hvp
  refine runs_mono (runs_layer6 M κ step q cl hA _ _ hvp _ _ hlc hB) fun cl' hcl' ↦ ?_
  subst hcl'
  refine ⟨⟨?_, hmu', rfl, rfl⟩, by show vp.2.length = κ - 3; rw [hvpl, hpt], lc.1, _, rfl, hlcl⟩
  show ev2 M v' = ev2 M (ld2 (lD κ q)) + ev2 M (ld2 (lE κ q + 1)) *
    (ev2 M (ld2 (lD κ q + 2)) + ev2 M (ld2 (lE κ q + 1)) * ev2 M (ld2 (lD κ q + 4)))
  rw [hv', htt]
  ring

/-! ## The layer gadget -/

/-- The layer on the two kinds of carried weights. -/
def layW (κ step q : ℕ) (claim : ClaimC) (gate : Cell) (z one : C2) : WRep → BM ClaimC
  | .first rl =>
    g2EqTab z [one] rl >>= fun B ↦ firstIotaG z B >>= fun fs ↦
      layBody κ step q claim gate z one fs (firstDotG z one B)
  | .lt pos β =>
    if pos.length = 11 then
      g2EqTab z [one] (pos.drop 6) >>= fun eL ↦ laneWG z β eL >>= fun B ↦
      g2EqTab z [one] (pos.take 6) >>= fun A ↦ ltIotaG z B A >>= fun fs ↦
        layBody κ step q claim gate z one fs (ltDotG z one B (pos.take 6))
    else failG claim one gate

/-- **The layer gadget** (`G κ step q claim gate` of `LayerHarStmt`). -/
def layer6G (κ step q : ℕ) (claim : ClaimC) (gate : Cell) : BM ClaimC :=
  g2Zero (ld2 q) >>= fun z ↦ g2One z >>= fun one ↦ layW κ step q claim gate z one claim.w

/-- **The layer gadget re-executes `layer6`** and hands on an `lt` claim with 11 position cells. -/
theorem layer6G_har' (κ : ℕ) (hκ : 5 ≤ κ) (step : ℕ) (hstep : step < 12) (q : ℕ) (claim : ClaimC)
    (gate : Cell) (hg : gate.val M = 1) (hpt : claim.point.length = κ - 3) (cl : KClaim E2)
    (hrep : ClaimRep M claim cl) :
    HsA c M (layer6G κ step q claim gate) fun o ↦
      Runs M (layItems (P18.layer κ) q) (layer6 κ step cl)
        (fun cl' ↦ ClaimRep M o cl' ∧ o.point.length = κ - 3 ∧ LtS o.w) := by
  unfold layer6G
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ hsA_bind (hsA_of_hs (hs_g2One z)) fun one hone ↦ ?_
  rw [hz, add_zero] at hone
  have hw := hrep.2.2.2
  cases hcw : claim.w with
  | first rl =>
    simp only [hcw, wOf] at hw
    simp only [layW]
    refine hsA_bind (hsA_of_hs (hs_tab hz hone rl)) fun B hB ↦
      hsA_bind (hsA_of_hs (hs_firstIotaG hz B _ hB)) fun fs hfs ↦ ?_
    refine layBody_har κ hκ step hstep q claim gate hg hpt cl hrep hz hone fs ?_ _ fun lp hlp ↦
      hs_mono (hs_firstDotG hz hone B _ hB lp hlp) fun d hd ↦ ?_
    · rw [hfs, ← hw, firstW_eq]
    · rw [hd, ← hw, firstW_eq]
  | lt pos β =>
    simp only [hcw, wOf] at hw
    simp only [layW]
    split_ifs with hl
    · have hW : cl.weights = linearTransposeF (Lvm.Q1.prodWG (Lvm.Q1.eqAtG ((pos.map (ev2 M)).take 6))
          (laneWB (pos.map (ev2 M)) (ev2 M β))) := by
        rw [← hw, batchW_eq (p := pos.map (ev2 M)) (by simp [hl])]
      refine hsA_bind (hsA_of_hs (hs_tab hz hone _)) fun eL heL ↦
        hsA_bind (hsA_of_hs (hs_laneWG hz β pos eL heL)) fun B hB ↦
        hsA_bind (hsA_of_hs (hs_tab hz hone _)) fun A hA ↦
        hsA_bind (hsA_of_hs (hs_ltIotaG hz B _ hB A _ hA)) fun fs hfs ↦ ?_
      refine layBody_har κ hκ step hstep q claim gate hg hpt cl hrep hz hone fs ?_ _ fun lp hlp ↦
        hs_mono (hs_ltDotG hz hone B _ hB (pos.take 6) (by simp [hl]) lp hlp) fun d hd ↦ ?_
      · rw [hfs, hW, List.map_take]
      · rw [hd, hW, List.map_take]
    · exact hsA_failG hone hg

/-- **CB-L: the frozen one-layer statement holds of `layer6G`.** -/
theorem layer6G_har : LayerHarStmt layer6G :=
  fun κ hκ step hstep q claim gate _ _ hg hpt cl hrep ↦
    hsA_mono (layer6G_har' κ hκ step hstep q claim gate hg hpt cl hrep) fun _ h ↦
      runs_mono h fun _ ⟨h1, h2, pos, β, h3, _⟩ ↦ ⟨h1, h2, pos, β, h3⟩

/-! ## The 12 layers -/

/-- The layers `steps`, each `layEnd (P18.layer κ)` lanes after the last. -/
def laysG (κ : ℕ) : List ℕ → ℕ → ClaimC → Cell → BM ClaimC
  | [], _, claim, _ => pure claim
  | step :: steps, q, claim, gate =>
    layer6G κ step q claim gate >>= fun o ↦ laysG κ steps (layEnd (P18.layer κ) q) o gate

/-- **The 12 layers** of a batch (steps `0 … 11`), lanes from `q`. -/
def layers6G (κ q : ℕ) (claim : ClaimC) (gate : Cell) : BM ClaimC := laysG κ (List.range 12) q claim gate

theorem laysG_runs (κ : ℕ) (hκ : 5 ≤ κ) : ∀ (steps : List ℕ) (q : ℕ) (claim : ClaimC) (gate : Cell),
    (∀ s ∈ steps, s < 12) → gate.val M = 1 → claim.point.length = κ - 3 →
      ∀ cl : KClaim E2, ClaimRep M claim cl →
        HsA c M (laysG κ steps q claim gate) fun o ↦
          Runs M (layItems (rep steps.length (P18.layer κ)) q) (layers6 κ steps cl)
            (fun cl' ↦ ClaimRep M o cl' ∧ o.point.length = κ - 3 ∧ (LtS claim.w ∨ steps ≠ [] → LtS o.w))
  | [], _, _, _, _, _, hpt, _, hrep =>
    hsA_pure (runs_pure ⟨hrep, hpt, fun h ↦ h.elim id fun h' ↦ absurd rfl h'⟩)
  | step :: steps, q, claim, gate, hs, hg, hpt, cl, hrep => by
    simp only [laysG]
    refine hsA_bind (layer6G_har' κ hκ step (hs step (by simp)) q claim gate hg hpt cl hrep) fun o ho ↦ ?_
    have hrest : HsA c M (laysG κ steps (layEnd (P18.layer κ) q) o gate) fun o2 ↦
        ∀ cl', (ClaimRep M o cl' ∧ o.point.length = κ - 3 ∧ LtS o.w) →
          Runs M (layItems (rep steps.length (P18.layer κ)) (layEnd (P18.layer κ) q)) (layers6 κ steps cl')
            (fun cl'' ↦ ClaimRep M o2 cl'' ∧ o2.point.length = κ - 3 ∧
              (LtS claim.w ∨ step :: steps ≠ [] → LtS o2.w)) := by
      intro p hh ha cl' ⟨h1, h2, h3⟩
      exact runs_mono (laysG_runs κ hκ steps _ o gate (fun s hs' ↦ hs s (List.mem_cons_of_mem _ hs')) hg h2
        cl' h1 p hh ha) fun _ ⟨r1, r2, r3⟩ ↦ ⟨r1, r2, fun _ ↦ r3 (Or.inl h3)⟩
    refine hsA_mono hrest fun o2 h2 ↦ ?_
    rw [List.length_cons, rep_succ, layItems_append]
    simp only [layers6]
    exact runs_bind ho fun cl' hcl' ↦ h2 cl' hcl'

/-- **The 12 layers re-execute `layers6 κ (List.range 12)`** and hand on an `lt` claim. -/
theorem layers6G_runs (κ : ℕ) (hκ : 5 ≤ κ) (q : ℕ) (claim : ClaimC) (gate : Cell) (hg : gate.val M = 1)
    (hpt : claim.point.length = κ - 3) (cl : KClaim E2) (hrep : ClaimRep M claim cl) :
    HsA c M (layers6G κ q claim gate) fun o ↦
      Runs M (layItems (rep 12 (P18.layer κ)) q) (layers6 κ (List.range 12) cl)
        (fun cl' ↦ ClaimRep M o cl' ∧ o.point.length = κ - 3 ∧ LtS o.w) :=
  hsA_mono (laysG_runs κ hκ (List.range 12) q claim gate (fun _ hs ↦ List.mem_range.mp hs) hg hpt cl hrep)
    fun _ h ↦ runs_mono h fun _ ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3 (Or.inr (by simp))⟩

end Lvm6.QK
