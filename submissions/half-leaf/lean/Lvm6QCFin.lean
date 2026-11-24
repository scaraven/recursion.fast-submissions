-- New for lvm6 (WP CC8). The final WHIR level in the node circuit (CC-8 of `Lvm6QCFinStmt`): the
-- generator `finGen` and its HAR `finHar`, with the gadgets it places itself: the claim folded by
-- the level's rounds (`foldsCG`), the row check (`chkEqsG`), the tail sumcheck (season 1's `sc2`,
-- re-executing W1's `sumP`), the final message's multilinear extension at the tail point (`mleG`)
-- and the terminal check `wC · m̃(τ) = claim`.
import Lvm6QCFinStmt
import Lvm6QCWhir
import Lvm6QKRound
import LvmE2QWKitSem
import LvmWhirCode

/-!
# The final level (generator and HAR)

Every gadget here is one generator call per instance with no instance constant in its body
(PHI-decision §3.2 item 4): a round's claim fold `foldCG`, a row check `chkEqG`, a fold step of the
message table `mleStep`; lanes enter as stream cells (`ld2`), the rest as cells.

* `roundPoly_ev2`, **`sc2_runsSum`**: `sc2 R q claim` re-executes W1's `sumP` (`R(2, g)` rounds,
  `c₁ = claim + c₂` in characteristic 2), for any `Φ`, `M` and start claim equal to the cell's.
* `foldCG`, `foldsCG`, `hs_foldsCG`: `foldClaim` per round, `foldsC` over the rounds' cells.
* `chkEqsG`, `hsA_chkEqsG`: pairwise asserted equality of two lists of cells.
* `mleL_succ`, `mleG`, `hs_mleG`: `mleL (s ∘ bitsToNat)` at `τ`, by folding the table `τ_0` first.
* `finGen`; **`finHar Fv : FinHarStmt Fv (finGen Fv.nf Fv.t)`** (CC-8).
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK
open Lvm6 (Item Level rep rnd)

variable {c : Ctx} {M : Mem}

theorem two_E2 : (2 : E2) = 0 := CharTwo.two_eq_zero

theorem ev2_of_zero {z : C2} (hz : z.val M = 0) : ev2 M z = 0 := by
  show FE2.ringEquivE2 (z.val M) = 0
  rw [hz, map_zero]

/-- A cell assertion pulls through any family of postconditions. -/
theorem hsA_pi {α : Type} {ι : Sort _} {m : BM α} {P : ι → α → Prop}
    (h : ∀ i, HsA c M m (P i)) : HsA c M m fun o ↦ ∀ i, P i o :=
  fun p hh ha i ↦ h i p hh ha

theorem ev2_getD {z : C2} (hz2 : ev2 M z = 0) : ∀ (l : List C2) (j : ℕ),
    ev2 M (l.getD j z) = (l.map (ev2 M)).getD j 0
  | [], j => by simp [hz2]
  | x :: l, j => by
    cases j with
    | zero => rfl
    | succ j => exact ev2_getD hz2 l j

theorem getD_of_map {l : List C2} {n : ℕ} {G : ℕ → FE2} (hl : l.map (C2.val M) = (List.range n).map G)
    {j : ℕ} (hj : j < n) (d : C2) : (l.getD j d).val M = G j := by
  have hlen : l.length = n := by simpa using congrArg List.length hl
  have h := List.getElem_of_eq hl (by simp only [List.length_map]; omega : j < (l.map (C2.val M)).length)
  simp only [List.getElem_map, List.getElem_range] at h
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact h

/-! ## The tail sumcheck -/

theorem roundPoly_ev2 {claim c0 c2 r x : C2}
    (hx : x.val M = scStep2 (c0.val M) (c2.val M) (r.val M) (claim.val M)) :
    Whir.roundPoly (ev2 M claim) (ev2 M c0) (ev2 M c2) (ev2 M r) = ev2 M x := by
  have e : ev2 M x = ((ev2 M claim + ev2 M c2) + ev2 M c2 * ev2 M r) * ev2 M r + ev2 M c0 := by
    simp only [ev2, hx, scStep2, FE2.toE2_add, FE2.fe2_mul_eq]
  rw [e, Whir.roundPoly]
  linear_combination (-(ev2 M c0) - ev2 M c2) * ev2 M r * two_E2

/-- **`sc2` re-executes W1's tail sumcheck** `sumP` from the claim the cell holds: the challenges
are the answers' lanes, the terminal check reads the final claim cell. -/
theorem sc2_runsSum {g : ℕ} (hg : g ≤ 64) : ∀ (R q : ℕ) (claim : C2),
    Hs c M (sc2 R q claim) fun o ↦ ∀ (Φ Mf : List E2 → E2) (τ : List E2) (cl : E2),
      RunsO M (bl (layItems (rep R (rnd 2 g)) q)) (Whir.sumP Whir.chalE2 g Φ Mf R τ cl)
        fun b ↦ cl = ev2 M claim →
          b = decide (Φ (τ ++ o.1.map (ev2 M)) * Mf (τ ++ o.1.map (ev2 M)) = ev2 M o.2)
  | 0, q, claim => hs_pure fun Φ Mf τ cl ↦ runsO_of_eq rfl (runsO_pure fun hcl ↦ by
      subst hcl
      simp)
  | R + 1, q, claim => by
    refine hs_bind (hs_scRound2 q claim) fun rc ⟨h1, h2⟩ ↦
      hs_bind (sc2_runsSum hg R (q + 14) rc.2) fun res hres ↦ hs_pure fun Φ Mf τ cl ↦ ?_
    have hl : bl (layItems (rep (R + 1) (rnd 2 g)) q) = bl (layItems [.E 1] q) ++
        (bl (layItems [.E 1] (q + 2)) ++ (bl (layItems [.G g, .D 0] (q + 4)) ++
          bl (layItems (rep R (rnd 2 g)) (q + 14)))) := by
      rw [rep_succ, lay_rnd2]
      simp [layItems, bl]
    show RunsO M _ (Whir.readF Whir.chalE2 >>= fun c₀ ↦ Whir.readF Whir.chalE2 >>= fun c₂ ↦
      Whir.chalE2.grp g 0 >>= fun v ↦ Whir.sumP Whir.chalE2 g Φ Mf R (τ ++ [v.getD 0 0])
        (Whir.roundPoly cl c₀ c₂ (v.getD 0 0))) _
    refine runsO_bind' hl (runsO_readF M q) fun c0 hc0 ↦ runsO_bind' rfl (runsO_readF M (q + 2))
      fun c2 hc2 ↦ runsO_bind' rfl (runsO_ground M hg 0 (q + 4)) fun v hv ↦ ?_
    have hr : v.getD 0 0 = ev2 M (ld2 (q + 5)) := by rw [hv]; rfl
    rw [hr]
    refine runsO_mono (hres Φ Mf (τ ++ [ev2 M (ld2 (q + 5))]) _) fun b hb hcl ↦ ?_
    rw [hb (by rw [hcl, hc0, hc2]; exact roundPoly_ev2 h2), h1]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

/-- `sc2 R q claim`'s challenges are `R` cells (with `sc2_runsSum`, for `finHar`'s `WAt` at the tail point). -/
theorem sc2_runsSumL {g : ℕ} (hg : g ≤ 64) (R q : ℕ) (claim : C2) :
    Hs c M (sc2 R q claim) fun o ↦ o.1.length = R ∧ ∀ (Φ Mf : List E2 → E2) (τ : List E2) (cl : E2),
      RunsO M (bl (layItems (rep R (rnd 2 g)) q)) (Whir.sumP Whir.chalE2 g Φ Mf R τ cl)
        fun b ↦ cl = ev2 M claim →
          b = decide (Φ (τ ++ o.1.map (ev2 M)) * Mf (τ ++ o.1.map (ev2 M)) = ev2 M o.2) :=
  fun p hp ↦ ⟨by rw [(hs_sc2 (c := c) (M := M) R q claim p hp).1]; simp [sc2Ans],
    sc2_runsSum hg R q claim p hp⟩

/-! ## The claim through the rounds -/

/-- **One round's claim fold** (`foldClaim`, characteristic 2):
`α·(α·w + σ + u₀) + β·(α·(c₁ + c₀) + c₀) + u₀`. -/
def foldCG (σ : C2) (r : RndC) : BM C2 :=
  g2Add σ r.u₀ >>= fun a1 ↦ g2Mul r.α r.w a1 >>= fun a2 ↦ g2Add r.c₁ r.c₀ >>= fun d ↦
    g2Mul r.α d r.c₀ >>= fun b1 ↦ g2Mul r.β b1 r.u₀ >>= fun b2 ↦ g2Mul r.α a2 b2

theorem hs_foldCG (σ : C2) (r : RndC) : Hs c M (foldCG σ r) fun x ↦ ∀ rr, RndRep M r rr →
    ev2 M x = Whir.foldClaim (ev2 M σ) rr.α rr.β rr.u₀ rr.w rr.c₀ rr.c₁ := by
  refine hs_bind (hs_g2Add _ _) fun a1 h1 ↦ hs_bind (hs_g2Mul _ _ _) fun a2 h2 ↦
    hs_bind (hs_g2Add _ _) fun d hd ↦ hs_bind (hs_g2Mul _ _ _) fun b1 hb1 ↦
    hs_bind (hs_g2Mul _ _ _) fun b2 hb2 ↦ hs_mono (hs_g2Mul _ _ _) fun x hx rr hr ↦ ?_
  obtain ⟨hu, hw, hc0, hc1, hα, hβ⟩ := hr
  rw [ev2_mul hx, ev2_mul hb2, ev2_mul hb1, ev2_add hd, ev2_mul h2, ev2_add h1, ← hu, ← hw, ← hc0,
    ← hc1, ← hα, ← hβ]
  simp only [Whir.foldClaim]
  linear_combination (ev2 M r.α * ev2 M r.u₀ + ev2 M r.α * ev2 M r.β * ev2 M r.c₀) * two_E2

/-- The claim folded by the rounds' cells, first round first. -/
def foldsCG : C2 → List RndC → BM C2
  | σ, [] => pure σ
  | σ, r :: rc => foldCG σ r >>= fun σ' ↦ foldsCG σ' rc

theorem hs_foldsCG : ∀ (rc : List RndC) (σ : C2), Hs c M (foldsCG σ rc) fun x ↦
    ∀ rs, RndsRep M rc rs → ev2 M x = Whir.foldsC rs.length rs (ev2 M σ)
  | [], σ => hs_pure fun rs hr ↦ by cases hr; rfl
  | r :: rc, σ => hs_bind (hs_foldCG σ r) fun σ' h' ↦ hs_mono (hs_foldsCG rc σ') fun x hx rs hr ↦ by
    cases hr with
    | cons hr1 hr2 =>
      rw [hx _ hr2, h' _ hr1]
      rfl

/-! ## The row check -/

/-- `x = y` asserted (`x + y = 0`). -/
def chkEqG (x y : C2) (gate : Cell) : BM Unit := g2Add x y >>= fun d ↦ g2Assert d gate

/-- Pairwise asserted equality. -/
def chkEqsG : List C2 → List C2 → Cell → BM Unit
  | x :: xs, y :: ys, gate => chkEqG x y gate >>= fun _ ↦ chkEqsG xs ys gate
  | _, _, _ => pure ()

theorem hsA_chkEqsG {gate : Cell} (hg : gate.val M = 1) : ∀ xs ys : List C2,
    HsA c M (chkEqsG xs ys gate) fun _ ↦ xs.length = ys.length → xs.map (ev2 M) = ys.map (ev2 M)
  | [], [] => hsA_pure fun _ ↦ rfl
  | [], _ :: _ => hsA_pure fun h ↦ absurd h (by simp)
  | _ :: _, [] => hsA_pure fun h ↦ absurd h (by simp)
  | x :: xs, y :: ys => by
    refine hsA_bind (hsA_bind (hsA_of_hs (hs_g2Add x y)) fun d hd ↦
      hsA_mono (hsA_g2Assert d gate hg) fun _ h0 ↦ (show ev2 M x = ev2 M y from ?_)) fun _ hxy ↦
      hsA_mono (hsA_chkEqsG hg xs ys) fun _ h hl ↦ ?_
    · have h3 : x.val M + y.val M = 0 := by rw [← hd]; exact h0
      simp only [ev2]
      congr 1
      linear_combination h3 - fe2_add_self (y.val M)
    · simp only [List.map_cons, hxy, h (by simpa using hl)]

/-! ## The message's multilinear extension -/

theorem mleL_zero (f : ℕ → E2) (y : List E2) :
    Whir.mleL (κ := 0) (fun u ↦ f (bitsToNat u)) y = f 0 := by
  simp [Whir.mleL, Whir.prodL, bitsToNat]

/-- **One variable of the multilinear extension**: the table folded by the first coordinate. -/
theorem mleL_succ (κ : ℕ) (f : ℕ → E2) (y : List E2) :
    Whir.mleL (κ := κ + 1) (fun u ↦ f (bitsToNat u)) y =
      Whir.mleL (κ := κ) (fun u ↦ (1 - y.headD 0) * f (2 * bitsToNat u) +
        y.headD 0 * f (2 * bitsToNat u + 1)) y.tail := by
  have hP : ∀ (b : Bool) (u : Fin κ → Bool),
      Whir.prodL (fun i X ↦ if h : i < κ + 1 then
        (if (Fin.cons b u : Fin (κ + 1) → Bool) ⟨i, h⟩ then X else 1 - X) else 1) (κ + 1) y =
      (if b then y.headD 0 else 1 - y.headD 0) *
        Whir.prodL (fun i X ↦ if h : i < κ then (if u ⟨i, h⟩ then X else 1 - X) else 1) κ y.tail := by
    intro b u
    rw [Whir.prodL]
    congr 1
    congr 1
    funext i X
    by_cases hi : i < κ
    · rw [dif_pos (by omega : i + 1 < κ + 1), dif_pos hi]
      rfl
    · rw [dif_neg (by omega : ¬(i + 1 < κ + 1)), dif_neg hi]
  unfold Whir.mleL
  rw [Whir.sum_cube_succ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  beta_reduce
  rw [hP false u, hP true u, LeanVM.Protocol.Whir.Sound.bitsToNat_cons,
    LeanVM.Protocol.Whir.Sound.bitsToNat_cons]
  simp only [Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte, zero_add]
  rw [add_comm 1 (2 * bitsToNat u)]
  ring

/-- One fold step of the table at `r`: `r·(t_{2j} + t_{2j+1}) + t_{2j}`. -/
def mleStep (z r : C2) (tab : List C2) (j : ℕ) : BM C2 :=
  g2Add (tab.getD (2 * j) z) (tab.getD (2 * j + 1) z) >>= fun d ↦ g2Mul r d (tab.getD (2 * j) z)

/-- **The multilinear extension of a table of `2^κ` cells** at `τ` (`z` a zero cell). -/
def mleG (z : C2) : ℕ → List C2 → List C2 → BM C2
  | 0, tab, _ => pure (tab.getD 0 z)
  | κ + 1, tab, τ => mapB (mleStep z (τ.headD z) tab) (List.range (2 ^ κ)) >>= fun tab' ↦
      mleG z κ tab' τ.tail

theorem hs_mleG {z : C2} (hz : z.val M = 0) : ∀ (κ : ℕ) (tab τ : List C2) (f : ℕ → E2),
    (∀ j, j < 2 ^ κ → ev2 M (tab.getD j z) = f j) →
    Hs c M (mleG z κ tab τ) fun o ↦
      ev2 M o = Whir.mleL (κ := κ) (fun u ↦ f (bitsToNat u)) (τ.map (ev2 M))
  | 0, tab, τ, f, hf => hs_pure (by rw [mleL_zero]; exact hf 0 (by norm_num))
  | κ + 1, tab, τ, f, hf => by
    have hz2 := ev2_of_zero (M := M) hz
    refine hs_bind (hs_mapB _ (fun j ↦ (τ.headD z).val M * ((tab.getD (2 * j) z).val M +
        (tab.getD (2 * j + 1) z).val M) + (tab.getD (2 * j) z).val M)
      (fun j ↦ hs_bind (hs_g2Add _ _) fun d hd ↦ hs_mono (hs_g2Mul _ _ _) fun r hr ↦ by
        rw [hr, hd]) _) fun tab' ht ↦ ?_
    refine hs_mono (hs_mleG hz κ tab' τ.tail (fun j ↦ (1 - (τ.map (ev2 M)).headD 0) * f (2 * j) +
      (τ.map (ev2 M)).headD 0 * f (2 * j + 1)) fun j hj ↦ ?_) fun o ho ↦ ?_
    · have hv := getD_of_map ht hj z
      have h0 := hf (2 * j) (by rw [pow_succ]; omega)
      have h1 := hf (2 * j + 1) (by rw [pow_succ]; omega)
      have hτ : (τ.map (ev2 M)).headD 0 = ev2 M (τ.headD z) := by cases τ <;> simp [hz2]
      have e : ev2 M (tab'.getD j z) = ev2 M (τ.headD z) * (ev2 M (tab.getD (2 * j) z) +
          ev2 M (tab.getD (2 * j + 1) z)) + ev2 M (tab.getD (2 * j) z) := by
        simp only [ev2, hv, FE2.toE2_add, FE2.fe2_mul_eq]
      rw [hτ, ← h0, ← h1, e]
      linear_combination (ev2 M (τ.headD z) * ev2 M (tab.getD (2 * j) z)) * two_E2
    · have htl : (τ.map (ev2 M)).tail = τ.tail.map (ev2 M) := by cases τ <;> rfl
      rw [ho, mleL_succ, htl]

/-! ## The final level -/

/-- **The final level's generator**: the rounds' cells, the scalars, the positions (`posG` on the
query group's answers), the row check (`fvG` against `fpG`, asserted pairwise), the claim folded by
the rounds, the tail sumcheck from it, the message's extension and the weight cell `wG` at the tail
point, and the terminal check `wC · m̃(τ) + claim = 0`. -/
def finGen {kq : ℕ} (nf t : ℕ) (posG : (Fin (kq + 1) → C2) → Cell → BM (List Cell))
    (fvG : List RndC → List Cell → List (List (Option ℕ)) → Cell → BM (List C2))
    (fpG : List C2 → List Cell → Cell → BM (List C2)) (wG : List RndC → List C2 → Cell → BM C2)
    (_g gT κ ℓ : ℕ) (lev : Level) (wdI a : ℕ) (σc : C2) (gate : Cell) : BM FinOutC :=
  let rc := roundsCells ℓ a
  let sc := (List.range nf).map fun j ↦ ld2 (a + 27 * ℓ + 2 * j)
  let ao := finOpenAt nf kq ℓ a
  posG (fun j ↦ ansAt (a + 27 * ℓ + 2 * nf) j) gate >>= fun ps ↦
  fvG rc ps (openRows lev wdI (ao - 4) t) gate >>= fun fs ↦
  fpG sc ps gate >>= fun es ↦
  chkEqsG fs es gate >>= fun _ ↦
  foldsCG σc rc >>= fun σf ↦
  sc2 κ (ao + t * openStride lev) σf >>= fun sr ↦
  g2Zero σc >>= fun z ↦
  mleG z κ sc sr.1 >>= fun mv ↦
  wG rc sr.1 gate >>= fun wv ↦
  g2Mul wv mv sr.2 >>= fun e ↦
  g2Assert e gate >>= fun _ ↦
  pure ⟨rc, sc, ps, sr.1⟩

theorem layFin_eq (nf kq t κ : ℕ) (lev : Level) (wdI g gq gT ℓ a : ℕ) :
    layFin nf kq t κ lev wdI g gq gT ℓ a = layRounds g ℓ a ++ (bl (layItems [.E nf] (a + 27 * ℓ)) ++
      (bl (layItems [.G gq, .D kq] (a + 27 * ℓ + 2 * nf)) ++
        ([.o (openRows lev wdI (finOpenAt nf kq ℓ a - 4) t)] ++
          bl (layItems (rep κ (rnd 2 gT)) (finOpenAt nf kq ℓ a + t * openStride lev))))) := by
  simp only [layFin, layItems, bl, List.map_append, List.append_assoc, List.append_nil]

/-- **CC-8 proved**: the final level's generator re-executes `finP` with the terminal check `chkE`. -/
theorem finHar {n : ℕ} (Fv : Whir.FinIface E2 n) : FinHarStmt Fv (finGen Fv.nf Fv.t) := by
  intro fv posG fvG fpG ℓ w Pre wG hpos hfv hfp hw g gq gT i κ hg hgq hgT hwκ lev wdI a σ σc gate c M hgate
  unfold finGen
  refine hsA_bind (hpos c M _ gate hgate) fun ps hps ↦ ?_
  refine hsA_bind (hsA_pi fun rs ↦ hsA_pi fun (hr : RndsRep M (roundsCells ℓ a) rs) ↦
    hfv c M _ rs hr [] ps _ gate hgate) fun fs hfs ↦ ?_
  refine hsA_bind (hfp c M _ ps gate hgate) fun es hes ↦ ?_
  refine hsA_bind (hsA_chkEqsG hgate fs es) fun _ hEq ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_foldsCG _ σc)) fun σf hσf ↦ ?_
  refine hsA_bind (hsA_of_hs (sc2_runsSumL (M := M) hgT κ _ σf)) fun sr ⟨hsrl, hsr⟩ ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Zero σc)) fun z hz ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_mleG hz κ _ sr.1
    (fun j ↦ (((List.range Fv.nf).map fun j ↦ ld2 (a + 27 * ℓ + 2 * j)).map (ev2 M)).getD j 0)
    fun j _ ↦ ?_)) fun mv hmv ↦ ?_
  · exact ev2_getD (ev2_of_zero hz) _ j
  refine hsA_bind (hsA_pi fun (hP : Pre M) ↦ hsA_pi fun rs ↦
    hsA_pi fun (hr : RndsRep M (roundsCells ℓ a) rs) ↦ hsA_pi fun (hl : rs.length = ℓ) ↦
      hw c M hP _ rs hr hl sr.1 (hsrl.trans hwκ.symm) gate hgate) fun wv hwv ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul wv mv sr.2)) fun e he ↦ ?_
  refine hsA_bind (hsA_g2Assert e gate hgate) fun _ hE ↦ hsA_pure ?_
  -- the program
  unfold Whir.finP
  refine runsO_bind' (layFin_eq _ _ _ _ _ _ _ _ _ _ _) (runsO_roundsP M hg ℓ a) fun rs hrs ↦ ?_
  refine runsO_bind' rfl (runsO_readFs M Fv.nf (a + 27 * ℓ)) fun s hs ↦ ?_
  refine runsO_bind' rfl (runsO_ground M hgq Fv.kq (a + 27 * ℓ + 2 * Fv.nf)) fun qv hqv ↦ ?_
  refine runsO_bind' rfl (runsO_query M i _ _) fun rows hrows ↦ ?_
  have hlen : rs.length = ℓ := by rw [← hrs.length_eq]; simp [roundsCells]
  have hsv : ((List.range Fv.nf).map fun j ↦ ld2 (a + 27 * ℓ + 2 * j)).map (ev2 M) = s := by
    rw [hs, List.map_map]
    rfl
  have hgv : Whir.fPos Fv qv = Fv.pos (fun j ↦ ev2 M (ansAt (a + 27 * ℓ + 2 * Fv.nf) j)) := by
    unfold Whir.fPos
    congr 1
    funext j
    show qv.getD j 0 = _
    exact ground_ans hqv (j := j) (by omega)
  have hpp : posOf M ps = List.ofFn fun k ↦ (Whir.fPos Fv qv k : ℕ) := by rw [hps, hgv]
  have hf1 := hfs rs hrs (Whir.fPos Fv qv) hpp
  have hf2 := hes (Whir.fPos Fv qv) hpp
  have hcond : ∀ k, fv rs (Whir.fPos Fv qv) rows k =
      (Fv.fpoly s Whir.lane0).eval (Fv.dom (Whir.fPos Fv qv k)) := by
    have hl1 : fs.length = es.length := by
      have a1 := congrArg List.length hf1
      have a2 := congrArg List.length hf2
      simp only [List.length_map, List.length_ofFn] at a1 a2
      omega
    have h := hEq hl1
    rw [hf1, hf2, hsv] at h
    have h' := List.ofFn_injective h
    intro k
    rw [hrows]
    exact congrFun h' k
  rw [if_pos hcond]
  unfold Whir.chkE
  refine runsO_mono (hsr _ _ [] _) fun b hb hP hσ ↦ ?_
  have hσ' : Whir.foldsC ℓ rs σ = ev2 M σf := by rw [hσf rs hrs, hlen, hσ]
  rw [hb hσ', List.nil_append, decide_eq_true_iff, ← hwv hP rs hrs hlen]
  have hm : Whir.mleL (Whir.msgOf κ s) (sr.1.map (ev2 M)) = ev2 M mv := by
    rw [hmv, ← hsv]
    rfl
  rw [hm]
  have h0 : ev2 M wv * ev2 M mv + ev2 M sr.2 = 0 := by
    rw [← ev2_mul he, ev2_of_zero hE]
  linear_combination h0 - ev2 M sr.2 * two_E2

end Lvm6.QC
