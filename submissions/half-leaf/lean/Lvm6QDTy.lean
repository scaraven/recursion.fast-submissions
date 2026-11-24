-- New for lvm6 (WP CD). The typed family's first gadgets with their HARs: the child's zerocheck
-- (`zero6`, CD-1) and A23 with the `accIn` tie (`qacc6`, CD-4), on CB's `Runs` calculus and round
-- gadgets (`Lvm6QKRun`, `Lvm6QKRound`) and season 1's `E2` kit (`LvmE2QWKit`).
import Lvm6QDStmt
import Lvm6QKRound

/-!
# The zerocheck and A23 in the node circuit (generator and HAR)

Lanes from the lane `a` where the phase's items start (`layItems`, FORMAT6 §4):

* **`zero6 a gate`** (§6.4a rows 1–3): `τ_i` at the answer lanes `a + 1 + 10 i`; the 20
  equality-mode rounds from `a + 200` (`eqRounds6`, CB: `c₀ = claim + τ·(c₁ + c₂)`, from claim
  `0`); `A, B, C` at `a + 480`, `+ 2`, `+ 4`; the assertion `final = A·B + C`.
  **`zero6_har : ZeroHarStmt zero6`**.
* **`qacc6 … a gate`** (§6.4a rows 10–12): `κ` at `a + 1`, `a + 11`; `h` at `a + 20 + 2j`; `t` at
  `a + 109`. Assertions (gated): `h₀ = y_in`; `Σ h_j = Σ_o eq(κ, o)·v_o` (`h(0)`, `h(1)`); the
  child's `accOut` — the line from `accIn.pt` to `κ ‖ r_x ‖ r_y` at `t`, and `h(t)` (Horner) — equal
  to the node's own `accIn` cells (the tie). `Φ_Q` is not in the circuit: the program's third check
  is the promise. **`qacc6_har : AccHarStmt qacc6`**.
-/

set_option autoImplicit false

namespace Lvm6.QD

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm.Typed
open Lvm6 (Item rep rnd)
open Lvm6.QK
open Lvm6.Ty (zeroProgE accProgE lineE hEvalE yOwnE PhiQE phiVarsE selBitsE gTau gZero gKappa gT)
open Lvm6.KPack (packRoundsN sumcheckE2_eq_packRoundsN)

variable {c : Ctx} {M : Mem}

/-! ## Helpers -/

theorem fe2_eq_of_add {x y : FE2} (h : x + y = 0) : x = y := by
  have := congrArg (· + y) h
  simpa [add_assoc, fe2_add_self] using this

theorem ev2_eq_of_add {x y : C2} (h : x.val M + y.val M = 0) : ev2 M x = ev2 M y := by
  simp only [ev2, fe2_eq_of_add h]

theorem ev2_of_zero {z : C2} (h : z.val M = 0) : ev2 M z = 0 := by simp [ev2, h]

theorem map_ev2 (l : List C2) : l.map (ev2 M) = (l.map (C2.val M)).map FE2.toE2 := by
  rw [List.map_map]; rfl

theorem toE2_sum : ∀ l : List FE2, FE2.toE2 l.sum = (l.map FE2.toE2).sum
  | [] => by simp
  | x :: l => by simp [toE2_sum l]

/-- Gated equalities of two lists of `E2` values. -/
def assertEq2s (gate : Cell) : List C2 → List C2 → BM Unit
  | x :: xs, y :: ys => g2Add x y >>= fun d ↦ g2Assert d gate >>= fun _ ↦ assertEq2s gate xs ys
  | _, _ => pure ()

theorem hsA_assertEq2s {gate : Cell} (hg : gate.val M = 1) : ∀ (xs ys : List C2), xs.length = ys.length →
    HsA c M (assertEq2s gate xs ys) (fun _ ↦ xs.map (C2.val M) = ys.map (C2.val M))
  | [], [], _ => hsA_pure rfl
  | x :: xs, y :: ys, h => hsA_bind (hsA_of_hs (hs_g2Add x y)) fun d hd ↦
      hsA_bind (hsA_g2Assert d gate hg) fun _ h0 ↦
        hsA_mono (hsA_assertEq2s hg xs ys (by simpa using h)) fun _ hr ↦ by
          rw [List.map_cons, List.map_cons, hr, fe2_eq_of_add (hd.symm.trans h0)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ## Layouts -/

theorem layEnd_repG (g : ℕ) : ∀ (n a : ℕ), layEnd (rep n [.G g]) a = a + 10 * n
  | 0, a => rfl
  | n + 1, a => by
    rw [rep_succ, layEnd_append, layEnd_repG g n]
    simp only [layEnd]; omega

theorem layEnd_repR2 (g : ℕ) : ∀ (n q : ℕ), layEnd (rep n (rnd 2 g)) q = q + 14 * n
  | 0, q => rfl
  | n + 1, q => by
    rw [rep_succ, layEnd_append, layEnd_repR2 g n]
    simp only [rnd, layEnd]; omega

/-! ## The zerocheck (CD-1) -/

/-- `τ`'s cells: the answers of the 20 ground draws. -/
def tauC (a : ℕ) : List C2 := (List.range xVars).map fun i ↦ ld2 (a + 1 + 10 * i)

/-- The lane of `A` (after `τ` and the rounds). -/
def zAbc (a : ℕ) : ℕ := a + 10 * xVars + 14 * xVars

/-- **The zerocheck gadget**: the rounds from claim `0`, then `final = A·B + C` (gated). -/
def zero6 (a : ℕ) (gate : Cell) : BM ZeroOutC :=
  g2Zero (ld2 a) >>= fun z ↦ eqRounds6 (a + 10 * xVars) z (tauC a) >>= fun rf ↦
    g2Mul (ld2 (zAbc a)) (ld2 (zAbc a + 2)) (ld2 (zAbc a + 4)) >>= fun ab ↦ g2Add rf.1 ab >>= fun d ↦
      g2Assert d gate >>= fun _ ↦ pure ⟨rf.2, [ld2 (zAbc a), ld2 (zAbc a + 2), ld2 (zAbc a + 4)]⟩

theorem gdraws_tauC (a : ℕ) : gdraws M a xVars = (tauC a).map (ev2 M) := by
  rw [tauC, List.map_map]; rfl

/-- **CD-1**: `zero6` re-executes the zerocheck. -/
theorem zero6_har : ZeroHarStmt zero6 := by
  intro a gate c M hg
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ ?_
  refine hsA_bind (hsA_of_hs (eqRounds6_runs gZero (by norm_num) _ z (tauC a))) fun rf hrf ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun ab hab ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun d hd ↦ ?_
  refine hsA_bind (hsA_g2Assert d gate hg) fun _ h0 ↦ hsA_pure ?_
  show Runs M (layItems zeroItems a) zeroProgE _
  have hlen : (tauC a).length = xVars := by simp [tauC]
  rw [ev2_of_zero hz, hlen] at hrf
  have hfin : ev2 M rf.1 = ev2 M (ld2 (zAbc a)) * ev2 M (ld2 (zAbc a + 2)) + ev2 M (ld2 (zAbc a + 4)) := by
    rw [ev2_eq_of_add (hd.symm.trans h0), ev2_mul hab]
  have hlay : layItems zeroItems a = layItems (rep xVars [.G gTau]) a ++
      (layItems (rep xVars (rnd 2 gZero)) (a + 10 * xVars) ++ layItems [.E 3] (zAbc a)) := by
    rw [zeroItems, layItems_append, layItems_append, layEnd_append, layEnd_repG, layEnd_repR2,
      List.append_assoc]; rfl
  unfold zeroProgE
  refine runs_bind' hlay (runs_e2Samples M (by norm_num) xVars a) fun τ hτ ↦ ?_
  subst hτ
  rw [sumcheckE2_eq_packRoundsN, bind_assoc, gdraws_tauC]
  refine runs_bind' rfl hrf fun res hres ↦ ?_
  simp only [pure_bind]
  refine runs_bind' (l₂ := []) rfl (runs_e2Reads M 3 (zAbc a)) fun v hv ↦ ?_
  subst hv
  refine runs_bind' (l₁ := []) (l₂ := []) rfl (runs_require ?_) fun _ _ ↦ runs_pure ?_
  · show res.1 = _
    rw [hres.1, hfin]; rfl
  · refine ⟨hres.2, ?_⟩
    simp [scal, List.range_succ]

/-! ## A23 and the tie (CD-4) -/

/-- `κ`'s cells. -/
def kapC (a : ℕ) : List C2 := [ld2 (a + 1), ld2 (a + 11)]

/-- `h`'s cells (44 scalars). -/
def hC (a : ℕ) : List C2 := (List.range (phiVarsE + 1)).map fun j ↦ ld2 (a + 20 + 2 * j)

/-- `t`'s cell. -/
def tC (a : ℕ) : C2 := ld2 (a + 20 + 2 * (phiVarsE + 1) + 1)

/-- Horner from the last coefficient: `c₀ + t·(c₁ + t·(…))`. -/
def horner6 (z t : C2) : List C2 → BM C2
  | [] => pure z
  | x :: xs => horner6 z t xs >>= fun acc ↦ g2Mul t acc x

/-- `Σ_o eq(κ, o)·v_o` (the `eq` table from `[1]`). -/
def yOwn6 (z o : C2) (κ vs : List C2) : BM C2 := g2EqTab z [o] κ >>= fun tab ↦ g2Dot z (tab.zip vs)

/-- The line from `x` to `b` at `t`, coordinate by coordinate: `x_i + t·(x_i + b_i)`. -/
def line6 (z t : C2) (x b : List C2) : BM (List C2) :=
  mapB (fun i ↦ g2Add (x.getD i z) (b.getD i z) >>= fun d ↦ g2Mul t d (x.getD i z)) (List.range x.length)

/-- **A23 with the tie**: `h₀ = y_in`, `Σ h = y_own(κ)`, the child's `accOut` = the node's
`accIn` cells (`own`, `ownY`); all gated. -/
def qacc6 (_Q : Program) (_lay : Lay) (ain : List C2) (yIn : C2) (rxy vs own : List C2) (ownY : C2)
    (a : ℕ) (gate : Cell) : BM Unit :=
  g2Zero (ld2 a) >>= fun z ↦ g2Const 1 (ld2 a) >>= fun o ↦
    assertEq2s gate [(hC a).getD 0 z] [yIn] >>= fun _ ↦
      g2Sum z (hC a) >>= fun s ↦ yOwn6 z o (kapC a) vs >>= fun y ↦ assertEq2s gate [s] [y] >>= fun _ ↦
        line6 z (tC a) ain (kapC a ++ rxy) >>= fun pts ↦ assertEq2s gate pts own >>= fun _ ↦
          horner6 z (tC a) (hC a) >>= fun hv ↦ assertEq2s gate [hv] [ownY]

theorem hs_horner6 {z t : C2} (hz : z.val M = 0) : ∀ xs : List C2,
    Hs c M (horner6 z t xs) (fun r ↦ ev2 M r = hEvalE (xs.map (ev2 M)) (ev2 M t))
  | [] => hs_pure (by simp [hEvalE, ev2_of_zero hz])
  | x :: xs => hs_bind (hs_horner6 hz xs) fun acc hacc ↦ hs_mono (hs_g2Mul t acc x) fun r hr ↦ by
      rw [ev2_mul hr, hacc, List.map_cons]
      simp only [hEvalE, List.foldr_cons]
      ring

theorem hEvalE_zero (x : E2) (xs : List E2) : hEvalE (x :: xs) 0 = x := by
  simp [hEvalE]

theorem hEvalE_one : ∀ xs : List E2, hEvalE xs 1 = xs.sum
  | [] => rfl
  | x :: xs => by
    have := hEvalE_one xs
    simp only [hEvalE, List.foldr_cons, one_mul, List.sum_cons] at this ⊢
    rw [this]

theorem hs_line6 {z t : C2} (x b : List C2) :
    Hs c M (line6 z t x b) (fun pts ↦ pts.map (C2.val M) = (List.range x.length).map fun i ↦
      t.val M * ((x.getD i z).val M + (b.getD i z).val M) + (x.getD i z).val M) :=
  hs_mapB _ _ (fun i ↦ hs_bind (hs_g2Add _ _) fun d hd ↦ hs_mono (hs_g2Mul _ _ _) fun r hr ↦ by
    rw [hr, hd]) _

theorem lineE_map (z t : C2) (x b : List C2) (hb : x.length = b.length) :
    lineE (x.map (ev2 M)) (b.map (ev2 M)) (ev2 M t) = (List.range x.length).map fun i ↦
      ev2 M (x.getD i z) + ev2 M t * (ev2 M (x.getD i z) + ev2 M (b.getD i z)) := by
  apply List.ext_getElem
  · simp [lineE, hb]
  · intro i h1 h2
    simp only [lineE, List.getElem_zipWith, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h2), List.getD_eq_getElem _ _ (by simp at h2; omega)]

theorem kapC_vals (a : ℕ) : gdraws M a 2 = (kapC a).map (ev2 M) := rfl

theorem hC_vals (a : ℕ) : scal M (a + 20) (phiVarsE + 1) = (hC a).map (ev2 M) := by
  rw [hC, List.map_map]; rfl

theorem yOwn_vals {z o : C2} (hz : z.val M = 0) (ho : o.val M = 1) (κ0 κ1 v0 v1 v2 v3 : C2) :
    Hs c M (yOwn6 z o [κ0, κ1] [v0, v1, v2, v3]) (fun y ↦
      ev2 M y = yOwnE ([v0, v1, v2, v3].map (ev2 M)) ([κ0, κ1].map (ev2 M))) :=
  hs_bind (hs_g2EqTab hz [o] [κ0, κ1]) fun tab htab ↦ hs_mono (hs_g2Dot z _) fun y hy ↦ by
    obtain ⟨e0, e1, e2, e3, rfl⟩ : ∃ e0 e1 e2 e3, tab = [e0, e1, e2, e3] := by
      have hl := congrArg List.length htab
      simp only [List.map_cons, List.map_nil, List.foldl, eqStep2, List.length_map, List.length_append,
        List.length_cons, List.length_nil] at hl
      match tab, hl with
      | [e0, e1, e2, e3], _ => exact ⟨e0, e1, e2, e3, rfl⟩
    simp only [List.map_cons, List.map_nil, List.foldl, eqStep2, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.cons.injEq, and_true] at htab
    obtain ⟨h0, h1, h2, h3⟩ := htab
    simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, hz, add_zero, zero_add] at hy
    simp only [yOwnE, dotF, eqKernelF, List.map_cons, List.map_nil, List.foldl, List.cons_append,
      List.nil_append, List.zipWith_cons_cons, List.zipWith_nil_right, ev2, hy, h0, h1, h2, h3, ho,
      FE2.toE2_add, FE2.fe2_mul_eq, FE2.toE2_one]
    ring

/-- **CD-4**: `qacc6` re-executes A23 under the promise and ties the child's `accOut` to the
node's `accIn`. -/
theorem qacc6_har : AccHarStmt qacc6 := by
  intro Q lay ain yIn rxy vs own ownY hain hrxy hvs hown a gate c M hg
  obtain ⟨v0, v1, v2, v3, rfl⟩ : ∃ v0 v1 v2 v3, vs = [v0, v1, v2, v3] := by
    match vs, hvs with
    | [v0, v1, v2, v3], _ => exact ⟨v0, v1, v2, v3, rfl⟩
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Const 1 _)) fun o ho ↦ ?_
  refine hsA_bind (hsA_assertEq2s hg _ _ rfl) fun _ hA1 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Sum _ _)) fun s hs ↦ ?_
  refine hsA_bind (hsA_of_hs (yOwn_vals hz ho _ _ v0 v1 v2 v3)) fun y hy ↦ ?_
  refine hsA_bind (hsA_assertEq2s hg _ _ rfl) fun _ hA2 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_line6 (z := z) (t := tC a) ain (kapC a ++ rxy))) fun pts hpts ↦ ?_
  have hplen : pts.length = own.length := by
    have := congrArg List.length hpts
    simp only [List.length_map, List.length_range] at this
    rw [this, hain, hown]
  refine hsA_bind (hsA_assertEq2s hg _ _ hplen) fun _ hA3 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_horner6 hz (hC a))) fun hv hhv ↦ ?_
  refine hsA_mono (hsA_assertEq2s hg _ _ rfl) fun _ hA4 ↦ ?_
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hA1 hA2 hA4
  -- the tie
  have hbl : ain.length = (kapC a ++ rxy).length := by
    simp [kapC, hain, hrxy, phiVarsE, selBitsE]; omega
  have hline : lineE (ain.map (ev2 M)) ((kapC a ++ rxy).map (ev2 M)) (ev2 M (tC a)) = own.map (ev2 M) := by
    rw [lineE_map z (tC a) ain _ hbl, map_ev2 own, ← hA3, hpts, List.map_map]
    refine List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply, ev2, FE2.toE2_add, FE2.fe2_mul_eq]
    ring
  have hhe : hEvalE ((hC a).map (ev2 M)) (ev2 M (tC a)) = ev2 M ownY := by
    rw [← hhv]; simp only [ev2, hA4]
  have htie : accOut6 (ain.map (ev2 M), ev2 M yIn) (gdraws M a 2) (rxy.map (ev2 M))
      (scal M (a + 20) (phiVarsE + 1)) (ev2 M (ld2 (a + 20 + 2 * (phiVarsE + 1) + 1))) =
        (own.map (ev2 M), ev2 M ownY) := by
    rw [accOut6, kapC_vals, hC_vals, ← List.map_append]
    exact Prod.ext hline hhe
  refine ⟨htie, fun hP hpw evs he ↦ ?_⟩
  -- the run
  have h0 : hEvalE ((hC a).map (ev2 M)) 0 = ev2 M yIn := by
    rw [show (hC a) = ld2 (a + 20 + 2 * 0) :: (List.range phiVarsE).map (fun j ↦ ld2 (a + 20 + 2 * (j + 1)))
      from by rw [hC, List.range_succ_eq_map]; simp [List.map_map, Function.comp_def]]
    rw [List.map_cons, hEvalE_zero]
    have : (hC a).getD 0 z = ld2 (a + 20 + 2 * 0) := by simp [hC]
    rw [← this]; simp only [ev2, hA1]
  have h1 : hEvalE ((hC a).map (ev2 M)) 1 = yOwnE ([v0, v1, v2, v3].map (ev2 M)) ((kapC a).map (ev2 M)) := by
    rw [hEvalE_one, show (kapC a).map (ev2 M) = [ld2 (a + 1), ld2 (a + 11)].map (ev2 M) from rfl, ← hy,
      map_ev2, ← toE2_sum]
    simp only [ev2, ← hA2, hs, hz, zero_add]
  have hl : layItems accItems a = layItems (rep 2 [.G gKappa]) a ++
      ((List.range (phiVarsE + 1)).map (fun i ↦ LEv.e (a + 20 + 2 * i)) ++
        layItems [.G gT] (a + 20 + 2 * (phiVarsE + 1))) := by
    rw [accItems, layItems_append, layEnd_repG]; rfl
  have hR : Runs M (layItems accItems a) (accProgE Q lay (ev2 M yIn) (ain.map (ev2 M)) (rxy.map (ev2 M))
      ([v0, v1, v2, v3].map (ev2 M))) (fun _ ↦ True) := by
    unfold accProgE
    refine runs_bind' hl (runs_e2Samples M (by norm_num) 2 a) fun κ hκ ↦ ?_
    refine runs_bind' rfl (runs_e2Reads M (phiVarsE + 1) (a + 20)) fun hs' hhs ↦ ?_
    refine runs_bind' (l₁ := [_, _]) (l₂ := []) rfl (runs_e2Sample M (by norm_num) _) fun t ht ↦ ?_
    subst hκ hhs ht
    refine runs_mono (runs_require ⟨?_, ?_, ?_⟩) fun _ _ ↦ trivial
    · rw [hC_vals]; exact h0
    · rw [hC_vals, kapC_vals]; exact h1
    · have e := congrArg Prod.fst htie
      have e2 := congrArg Prod.snd htie
      simp only [accOut6] at e e2
      rw [e, e2]; exact hP
  obtain ⟨out, h1', -⟩ := hR hpw evs he
  exact h1'

end Lvm6.QD
