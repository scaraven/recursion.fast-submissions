-- New for lvm6 (WP CD). The child's mini-bus GKR walk in the node circuit (`mb6`, CD-5): the
-- fingerprint group, the roots, `count ≠ 0` (an inverse by squarings), six two-level steps with
-- equality-mode rounds of count 5 (`eqRounds5`), the children's products and extensions.
import Lvm6QDRelay

/-!
# The mini-bus walk (generator and HAR)

Lanes from `a` (FORMAT6 §6.4b): `α₀` at `a + 1`, `α₁ α₂ α₃ β` at `a + 10 + 9i`; the roots at
`a + 46`, `a + 48`; step `k` from `a_k = a + 50 + Σ_{j<k}(53 + 36j)`: `λ` at `a_k + 1`, `2k` rounds of
18 lanes from `a_k + 10` (`c₁ … c₄`, nonce, answer at `+ 9`), the three children's 4 values at
`q`, `q + 8`, `q + 16` (`q = a_k + 10 + 36k`), `y₀` at `q + 25`, `y₁` at `q + 34`.

* **`eqRound5`/`eqRounds5`**: `c₀ = claim + r·(c₁ + c₂ + c₃ + c₄)`, next claim the round polynomial at
  the challenge (Horner, 4 products); **`eqRounds5_runs`** (Y1's `sumcheckE2 g claim 5`).
* **`gstep6`**: `λ`, the start `v₀ + λ(v₁ + λv₂)`, the rounds, `Π children_s`, the gated check, the
  extensions at `y` (`mle2`); **`gstep6_runs`**: it re-executes `gkrStepG gy 2`.
* **`nz6`**: `x·x^(2^128 − 2) = 1` (gated), hence `x ≠ 0`.
* **`mb6_har : MbHarStmt mb6`**.
-/

set_option autoImplicit false

namespace Lvm6.QD

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm.Typed
open Lvm6 (Item rep rnd)
open Lvm6.QK
open Lvm6.K (gPoint dDraws dDraw)
open Lvm6.Mb (GkrStateG gkrStepG gkrLayersG verifyGkrGrandProductsG lvmBusProgG e2SampleN gAB gLam gRd
  gY gYl miniDepth LBusG)

variable {c : Ctx} {M : Mem}

/-! ## Ground groups with further draws -/

theorem sampleChallenges_map {β : Type} (f : List E2 → VerifierProgram β) : ∀ n,
    (VerifierProgram.sampleChallenges n >>= fun cs ↦ f (cs.map e2OfE)) = dDraws n >>= f
  | 0 => by
    show (VerifierProgram.ret [] >>= fun cs ↦ f (cs.map e2OfE)) = (pure [] >>= f)
    rfl
  | n + 1 => by
    show (VerifierProgram.sampleChallenge >>= fun x ↦ VerifierProgram.sampleChallenges n >>= fun xs ↦
      pure (x :: xs)) >>= (fun cs ↦ f (cs.map e2OfE)) = (dDraw >>= fun x ↦ dDraws n >>= fun xs ↦ pure (x :: xs)) >>= f
    simp only [bind_assoc, pure_bind, dDraw, List.map_cons]
    congr 1; funext x
    exact sampleChallenges_map (fun xs ↦ f (e2OfE x :: xs)) n

theorem e2SampleN_gPoint (g n : ℕ) : e2SampleN g (n + 1) = gPoint g n := by
  simp only [e2SampleN, gPoint, e2Sample, bind_assoc, pure_bind, List.map_cons]
  congr 1; funext _; congr 1; funext x; congr 1; funext _
  exact sampleChallenges_map (fun xs ↦ pure (e2OfE x :: xs)) n

/-! ## Equality-mode rounds of count 5 -/

theorem layEnd_repR4 (g : ℕ) : ∀ (n q : ℕ), layEnd (rep n (rnd 4 g)) q = q + 18 * n
  | 0, q => rfl
  | n + 1, q => by
    rw [rep_succ, layEnd_append, layEnd_repR4 g n]
    simp only [rnd, layEnd]; omega

theorem lay_rnd4 (g q : ℕ) (rest : List Item) :
    layItems (rnd 4 g ++ rest) q = [.e q, .e (q + 2), .e (q + 4), .e (q + 6), .k (q + 8), .d (q + 9) g] ++
      layItems rest (q + 18) := by
  simp [rnd, layItems, List.range_succ]

/-- **One equality-mode round of count 5** at lane `q`, factor `r`. -/
def eqRound5 (z : C2) (q : ℕ) (value r : C2) : BM (C2 × C2) :=
  g2Sum z [ld2 q, ld2 (q + 2), ld2 (q + 4), ld2 (q + 6)] >>= fun s ↦ g2Mul r s value >>= fun c0 ↦
    g2Mul (ld2 (q + 6)) (ld2 (q + 9)) (ld2 (q + 4)) >>= fun t3 ↦ g2Mul t3 (ld2 (q + 9)) (ld2 (q + 2)) >>= fun t2 ↦
      g2Mul t2 (ld2 (q + 9)) (ld2 q) >>= fun t1 ↦ g2Mul t1 (ld2 (q + 9)) c0 >>= fun nv ↦ pure (ld2 (q + 9), nv)

/-- The rounds over the point `rs` from lane `q` (18 lanes apart): the final claim, the challenges. -/
def eqRounds5 (z : C2) : ℕ → C2 → List C2 → BM (C2 × List C2)
  | _, value, [] => pure (value, [])
  | q, value, r :: rs => eqRound5 z q value r >>= fun rc ↦ eqRounds5 z (q + 18) rc.2 rs >>= fun res ↦
    pure (res.1, rc.1 :: res.2)

theorem hs_eqRound5 {z : C2} (hz : z.val M = 0) (q : ℕ) (value r : C2) :
    Hs c M (eqRound5 z q value r) (fun rc ↦ rc.1 = ld2 (q + 9) ∧
      ev2 M rc.2 = polyEvalF [ev2 M value + ev2 M r * (ev2 M (ld2 q) + ev2 M (ld2 (q + 2)) +
        ev2 M (ld2 (q + 4)) + ev2 M (ld2 (q + 6))), ev2 M (ld2 q), ev2 M (ld2 (q + 2)), ev2 M (ld2 (q + 4)),
          ev2 M (ld2 (q + 6))] (ev2 M (ld2 (q + 9)))) :=
  hs_bind (hs_g2Sum _ _) fun s hs ↦ hs_bind (hs_g2Mul _ _ _) fun c0 hc0 ↦
    hs_bind (hs_g2Mul _ _ _) fun t3 ht3 ↦ hs_bind (hs_g2Mul _ _ _) fun t2 ht2 ↦
      hs_bind (hs_g2Mul _ _ _) fun t1 ht1 ↦ hs_bind (hs_g2Mul _ _ _) fun nv hnv ↦ hs_pure ⟨rfl, by
        have hs' : ev2 M s = ev2 M (ld2 q) + ev2 M (ld2 (q + 2)) + ev2 M (ld2 (q + 4)) + ev2 M (ld2 (q + 6)) := by
          simp only [ev2, hs, hz, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add,
            FE2.toE2_add, add_assoc]
        rw [ev2_mul hnv, ev2_mul ht1, ev2_mul ht2, ev2_mul ht3, ev2_mul hc0, hs']
        simp only [polyEvalF, List.foldr]
        ring⟩

theorem runs_eqMsg5 (g : ℕ) (hg : g ≤ 64) (q : ℕ) (value r : E2) :
    Runs M [.e q, .e (q + 2), .e (q + 4), .e (q + 6), .k (q + 8), .d (q + 9) g]
      (roundPolyE2 5 value (some r) >>= fun msg ↦ e2Sample g >>= fun ch ↦ pure (msg, ch))
      (fun res ↦ res = ([value + r * (ev2 M (ld2 q) + ev2 M (ld2 (q + 2)) + ev2 M (ld2 (q + 4)) +
        ev2 M (ld2 (q + 6))), ev2 M (ld2 q), ev2 M (ld2 (q + 2)), ev2 M (ld2 (q + 4)), ev2 M (ld2 (q + 6))],
          ev2 M (ld2 (q + 9)))) := by
  refine runs_bind' (l₁ := [_, _, _, _]) (P := fun msg ↦ msg = [value + r * (ev2 M (ld2 q) +
    ev2 M (ld2 (q + 2)) + ev2 M (ld2 (q + 4)) + ev2 M (ld2 (q + 6))), ev2 M (ld2 q), ev2 M (ld2 (q + 2)),
      ev2 M (ld2 (q + 4)), ev2 M (ld2 (q + 6))]) rfl ?_ fun msg hmsg ↦
    runs_bind' (l₂ := []) rfl (runs_e2Sample M hg (q + 8)) fun ch hch ↦ runs_pure (by rw [hmsg, hch])
  refine runs_bind' (l₂ := []) (List.append_nil _).symm (runs_e2Reads M 4 q) fun tl htl ↦ runs_pure ?_
  simp only [htl, scal, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, sumF, List.foldl, zero_add, mul_zero, add_zero, mul_one]

/-- **`eqRounds5` re-executes the equality-mode rounds of count 5.** -/
theorem eqRounds5_runs {z : C2} (hz : z.val M = 0) (g : ℕ) (hg : g ≤ 64) : ∀ (q : ℕ) (value : C2) (rs : List C2),
    Hs c M (eqRounds5 z q value rs) fun o ↦
      Runs M (layItems (rep rs.length (rnd 4 g)) q) (sumcheckE2 g (ev2 M value) 5 ((rs.map (ev2 M)).map some))
        (fun res ↦ res.1 = o.2.map (ev2 M) ∧ res.2 = ev2 M o.1)
  | q, value, [] => hs_pure (runs_pure ⟨rfl, rfl⟩)
  | q, value, r :: rs => by
    refine hs_bind (hs_eqRound5 hz q value r) fun rc ⟨h1, h2⟩ ↦
      hs_bind (eqRounds5_runs hz g hg (q + 18) rc.2 rs) fun res hres ↦ hs_pure ?_
    rw [List.length_cons, rep_succ, lay_rnd4]
    show Runs M _ (roundPolyE2 5 (ev2 M value) (some (ev2 M r)) >>= fun msg ↦ e2Sample g >>= fun ch ↦
      sumcheckE2 g (polyEvalF msg ch) 5 ((rs.map (ev2 M)).map some) >>= fun res ↦ pure (ch :: res.1, res.2)) _
    have e : (roundPolyE2 5 (ev2 M value) (some (ev2 M r)) >>= fun msg ↦ e2Sample g >>= fun ch ↦
        sumcheckE2 g (polyEvalF msg ch) 5 ((rs.map (ev2 M)).map some) >>= fun res ↦ pure (ch :: res.1, res.2)) =
        ((roundPolyE2 5 (ev2 M value) (some (ev2 M r)) >>= fun msg ↦ e2Sample g >>= fun ch ↦ pure (msg, ch)) >>=
          fun mc ↦ sumcheckE2 g (polyEvalF mc.1 mc.2) 5 ((rs.map (ev2 M)).map some) >>= fun res ↦
            pure (mc.2 :: res.1, res.2)) := by
      simp only [bind_assoc, pure_bind]
    rw [e]
    refine runs_bind' (l₂ := layItems (rep rs.length (rnd 4 g)) (q + 18)) rfl (runs_eqMsg5 g hg q _ _)
      fun mc hmc ↦ ?_
    have hv : polyEvalF mc.1 mc.2 = ev2 M rc.2 := by rw [hmc, h2]
    rw [hv]
    refine runs_bind' (l₂ := []) (List.append_nil _).symm hres fun r' hr ↦ runs_pure ?_
    rw [hr.1, hr.2, h1, hmc]
    exact ⟨rfl, rfl⟩

/-! ## One two-level step -/

/-- `multilinearEvalF [x₀, x₁, x₂, x₃] [y₀, y₁]`. -/
def mle2 (z : C2) (x : List C2) (y0 y1 : C2) : BM C2 :=
  g2Add (x.getD 0 z) (x.getD 1 z) >>= fun s0 ↦ g2Mul y0 s0 (x.getD 0 z) >>= fun f0 ↦
    g2Add (x.getD 2 z) (x.getD 3 z) >>= fun s1 ↦ g2Mul y0 s1 (x.getD 2 z) >>= fun f1 ↦
      g2Add f0 f1 >>= fun s2 ↦ g2Mul y1 s2 f0

theorem hs_mle2 (z : C2) (x0 x1 x2 x3 y0 y1 : C2) :
    Hs c M (mle2 z [x0, x1, x2, x3] y0 y1) (fun r ↦ ev2 M r =
      multilinearEvalF ([x0, x1, x2, x3].map (ev2 M)) [ev2 M y0, ev2 M y1]) :=
  hs_bind (hs_g2Add _ _) fun s0 hs0 ↦ hs_bind (hs_g2Mul _ _ _) fun f0 hf0 ↦
    hs_bind (hs_g2Add _ _) fun s1 hs1 ↦ hs_bind (hs_g2Mul _ _ _) fun f1 hf1 ↦
      hs_bind (hs_g2Add _ _) fun s2 hs2 ↦ hs_mono (hs_g2Mul _ _ _) fun r hr ↦ by
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hs0 hf0 hs1 hf1
        rw [ev2_mul hr, ev2_add hs2, ev2_mul hf0, ev2_mul hf1, ev2_add hs0, ev2_add hs1]
        simp only [multilinearEvalF, List.map_cons, List.map_nil, List.foldl, foldPairsF, List.headD]
        ring

/-- A child value's cell: tree `s`, entry `j`. -/
def chC (q s j : ℕ) : C2 := ld2 (q + 8 * s + 2 * j)

/-- The children of tree `s`. -/
def chs (q s : ℕ) : List C2 := [chC q s 0, chC q s 1, chC q s 2, chC q s 3]

/-- **One two-level step** from lane `a`, values `vals`, point `pt`. -/
def gstep6 (z : C2) (gate : Cell) (a : ℕ) (vals pt : List C2) : BM (List C2 × List C2) :=
  g2Mul (vals.getD 2 z) (ld2 (a + 1)) (vals.getD 1 z) >>= fun u ↦
  g2Mul u (ld2 (a + 1)) (vals.getD 0 z) >>= fun cl ↦ eqRounds5 z (a + 10) cl pt >>= fun rf ↦
  g2Prod z (chC (a + 10 + 18 * pt.length) 0 0) ((chs (a + 10 + 18 * pt.length) 0).drop 1) >>= fun p0 ↦
  g2Prod z (chC (a + 10 + 18 * pt.length) 1 0) ((chs (a + 10 + 18 * pt.length) 1).drop 1) >>= fun p1 ↦
  g2Prod z (chC (a + 10 + 18 * pt.length) 2 0) ((chs (a + 10 + 18 * pt.length) 2).drop 1) >>= fun p2 ↦
  g2Mul p2 (ld2 (a + 1)) p1 >>= fun w ↦ g2Mul w (ld2 (a + 1)) p0 >>= fun rhs ↦ g2Add rf.1 rhs >>= fun d ↦
  g2Assert d gate >>= fun _ ↦
  mle2 z (chs (a + 10 + 18 * pt.length) 0) (ld2 (a + 10 + 18 * pt.length + 25))
    (ld2 (a + 10 + 18 * pt.length + 34)) >>= fun n0 ↦
  mle2 z (chs (a + 10 + 18 * pt.length) 1) (ld2 (a + 10 + 18 * pt.length + 25))
    (ld2 (a + 10 + 18 * pt.length + 34)) >>= fun n1 ↦
  mle2 z (chs (a + 10 + 18 * pt.length) 2) (ld2 (a + 10 + 18 * pt.length + 25))
    (ld2 (a + 10 + 18 * pt.length + 34)) >>= fun n2 ↦
  pure ([n0, n1, n2], [ld2 (a + 10 + 18 * pt.length + 25), ld2 (a + 10 + 18 * pt.length + 34)] ++ rf.2)

/-- A step's items with the `y` group's grind `gy` and `n` rounds. -/
def mbStepG (gy n : ℕ) : List Item :=
  [.G gLam] ++ rep n (rnd 4 gRd) ++ [.E 4, .E 4, .E 4, .G gy, .D 1]

theorem mbStep_eq (k : ℕ) : mbStep k = mbStepG (if k = 5 then gYl else gY) (2 * k) := rfl

theorem layEnd_mbStepG (gy n a : ℕ) : layEnd (mbStepG gy n) a = a + 53 + 18 * n := by
  rw [mbStepG, layEnd_append, layEnd_append, layEnd_repR4]
  simp only [layEnd]; omega

theorem prod4 (l : List C2) (z : C2) (hz : z.val M = 0) (x0 x1 x2 x3 : C2) (hl : l = [x0, x1, x2, x3]) {p : C2}
    (hp : p.val M = x0.val M * ((l.drop 1).map (C2.val M)).prod) :
    ev2 M p = prodF (l.map (ev2 M)) := by
  subst hl
  simp only [List.drop_succ_cons, List.drop_zero, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at hp
  simp only [ev2, hp, prodF, List.map_cons, List.map_nil, List.foldl, one_mul, FE2.fe2_mul_eq]
  ring

theorem hs_true {α : Type} (m : BM α) : Hs c M m (fun _ ↦ True) := fun _ _ ↦ trivial

theorem hs_eqRounds5_len (z : C2) : ∀ (q : ℕ) (value : C2) (rs : List C2),
    Hs c M (eqRounds5 z q value rs) (fun o ↦ o.2.length = rs.length)
  | _, _, [] => hs_pure rfl
  | q, value, r :: rs => hs_bind (hs_true _) fun rc _ ↦ hs_bind (hs_eqRounds5_len z (q + 18) rc.2 rs)
      fun res hres ↦ hs_pure (by simp [hres])

/-- **`gstep6` re-executes one step of the walk.** -/
theorem gstep6_runs {z : C2} (hz : z.val M = 0) {gate : Cell} (hg : gate.val M = 1) (gy : ℕ) (hgy : gy ≤ 64)
    (a : ℕ) (vals pt : List C2) (hv : vals.length = 3) :
    HsA c M (gstep6 z gate a vals pt) fun o ↦ o.1.length = 3 ∧ o.2.length = pt.length + 2 ∧
      Runs M (layItems (mbStepG gy pt.length) a) (gkrStepG gy 2 ⟨vals.map (ev2 M), pt.map (ev2 M)⟩)
        (fun s ↦ s.values = o.1.map (ev2 M) ∧ s.point = o.2.map (ev2 M)) := by
  obtain ⟨v0, v1, v2, rfl⟩ : ∃ v0 v1 v2, vals = [v0, v1, v2] := by
    match vals, hv with
    | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
  set q := a + 10 + 18 * pt.length with hq
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun u hu ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun cl hcl ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_and (eqRounds5_runs hz gRd (by norm_num) (a + 10) cl pt)
    (hs_eqRounds5_len z (a + 10) cl pt))) fun rf hrf2 ↦ ?_
  obtain ⟨hrf, hrfl⟩ := hrf2
  refine hsA_bind (hsA_of_hs (hs_g2Prod hz _ _)) fun p0 hp0 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Prod hz _ _)) fun p1 hp1 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Prod hz _ _)) fun p2 hp2 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun w hw ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun rhs hrhs ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun d hd ↦ ?_
  refine hsA_bind (hsA_g2Assert d gate hg) fun _ h0 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_mle2 z _ _ _ _ _ _)) fun n0 hn0 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_mle2 z _ _ _ _ _ _)) fun n1 hn1 ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_mle2 z _ _ _ _ _ _)) fun n2 hn2 ↦ hsA_pure ⟨rfl, by simp [hrfl], ?_⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hu hcl
  set lam := ev2 M (ld2 (a + 1))
  have hcl' : ev2 M cl = polyEvalF ([v0, v1, v2].map (ev2 M)) lam := by
    rw [ev2_mul hcl, ev2_mul hu]
    simp only [polyEvalF, List.map_cons, List.map_nil, List.foldr]; ring
  have hp0' : ev2 M p0 = prodF ((chs q 0).map (ev2 M)) := prod4 (chs q 0) z hz _ _ _ _ rfl hp0
  have hp1' : ev2 M p1 = prodF ((chs q 1).map (ev2 M)) := prod4 (chs q 1) z hz _ _ _ _ rfl hp1
  have hp2' : ev2 M p2 = prodF ((chs q 2).map (ev2 M)) := prod4 (chs q 2) z hz _ _ _ _ rfl hp2
  have hfin : ev2 M rf.1 = polyEvalF [prodF ((chs q 0).map (ev2 M)), prodF ((chs q 1).map (ev2 M)),
      prodF ((chs q 2).map (ev2 M))] lam := by
    rw [ev2_eq_of_add (hd.symm.trans h0), ev2_mul hrhs, ev2_mul hw, hp0', hp1', hp2']
    simp only [polyEvalF, List.foldr]; ring
  have hch0 : scal M q 4 = (chs q 0).map (ev2 M) := by simp [scal, chs, chC, List.range_succ]
  have hch1 : scal M (q + 8) 4 = (chs q 1).map (ev2 M) := by simp [scal, chs, chC, List.range_succ]
  have hch2 : scal M (q + 16) 4 = (chs q 2).map (ev2 M) := by simp [scal, chs, chC, List.range_succ]
  have hl : layItems (mbStepG gy pt.length) a = layItems [.G gLam] a ++
      (layItems (rep pt.length (rnd 4 gRd)) (a + 10) ++
        ((List.range 4).map (fun i ↦ LEv.e (q + 2 * i)) ++ ((List.range 4).map (fun i ↦ LEv.e (q + 8 + 2 * i)) ++
          ((List.range 4).map (fun i ↦ LEv.e (q + 16 + 2 * i)) ++ layItems [.G gy, .D 1] (q + 24))))) := by
    rw [mbStepG, layItems_append, layItems_append, layEnd_append, layEnd_repR4, List.append_assoc]; rfl
  rw [hl]
  unfold gkrStepG
  rw [show (2 : ℕ) ^ 2 + 1 = 5 from rfl, show (2 : ℕ) ^ 2 = 4 from rfl]
  refine runs_bind' rfl (l₁ := [_, _]) (runs_e2Sample M (by norm_num) a) fun lm hlm ↦ ?_
  subst hlm
  rw [show polyEvalF ([v0, v1, v2].map (ev2 M)) (ev2 M (ld2 (a + 1))) = ev2 M cl from hcl'.symm]
  refine runs_bind' rfl hrf fun res hres ↦ ?_
  refine runs_bind' rfl (runs_e2Reads M 4 q) fun c0 hc0 ↦ ?_
  refine runs_bind' rfl (runs_e2Reads M 4 (q + 8)) fun c1 hc1 ↦ ?_
  refine runs_bind' rfl (runs_e2Reads M 4 (q + 16)) fun c2 hc2 ↦ ?_
  rw [hch0] at hc0; rw [hch1] at hc1; rw [hch2] at hc2
  subst hc0 hc1 hc2
  refine runs_bind' (l₁ := []) rfl (runs_require ?_) fun _ _ ↦ ?_
  · rw [hres.2, hfin]; rfl
  refine runs_bind' (l₂ := []) (List.append_nil _).symm
    (by rw [e2SampleN_gPoint]; exact runs_gPoint M hgy 1 (q + 24)) fun y hy ↦ runs_pure ⟨?_, ?_⟩
  · rw [hy]; simp only [List.map_cons, List.map_nil]; rw [hn0, hn1, hn2]; rfl
  · rw [hy, hres.1]; rfl

/-! ## The walk -/

theorem gkrLayersG_even (m : ℕ) (s : GkrStateG) :
    gkrLayersG (2 * (m + 1)) s = gkrStepG (if m = 0 then gYl else gY) 2 s >>= fun s' ↦ gkrLayersG (2 * m) s' := by
  rw [show 2 * (m + 1) = 2 * m + 2 by ring, gkrLayersG]
  have h1 : ¬ (2 * m % 2 = 1) := by omega
  simp only [h1, if_false]
  by_cases hm : m = 0
  · subst hm; simp
  · have : 2 * m ≠ 0 := by omega
    simp [hm, this]

/-- The walk's steps (`m` of them, each from the next lane). -/
def gsteps6 (z : C2) (gate : Cell) : ℕ → ℕ → List C2 → List C2 → BM (List C2 × List C2)
  | 0, _, vals, pt => pure (vals, pt)
  | m + 1, a, vals, pt => gstep6 z gate a vals pt >>= fun s ↦ gsteps6 z gate m (a + 53 + 18 * pt.length) s.1 s.2

theorem gsteps6_runs {z : C2} (hz : z.val M = 0) {gate : Cell} (hg : gate.val M = 1) :
    ∀ (m k a : ℕ) (vals pt : List C2), k + m = 6 → pt.length = 2 * k → vals.length = 3 →
      HsA c M (gsteps6 z gate m a vals pt) fun o ↦
        Runs M (layItems ((List.range' k m).flatMap mbStep) a) (gkrLayersG (2 * m) ⟨vals.map (ev2 M), pt.map (ev2 M)⟩)
          (fun s ↦ s.values = o.1.map (ev2 M) ∧ s.point = o.2.map (ev2 M))
  | 0, k, a, vals, pt, _, _, _ => hsA_pure (runs_pure ⟨rfl, rfl⟩)
  | m + 1, k, a, vals, pt, hkm, hpt, hv => by
    have hgy : (if k = 5 then gYl else gY) = (if m = 0 then gYl else gY) := by
      by_cases hm : m = 0
      · have : k = 5 := by omega
        simp [hm, this]
      · have : k ≠ 5 := by omega
        simp [hm, this]
    refine hsA_bind (gstep6_runs hz hg (if m = 0 then gYl else gY) (by split_ifs <;> norm_num) a vals pt hv)
      fun s hs ↦ ?_
    obtain ⟨hs1, hs2, hsR⟩ := hs
    refine hsA_mono (gsteps6_runs hz hg m (k + 1) _ s.1 s.2 (by omega) (by rw [hs2, hpt]; ring) hs1)
      fun o ho ↦ ?_
    rw [List.range'_succ, List.flatMap_cons, layItems_append, mbStep_eq, hgy, ← hpt, layEnd_mbStepG,
      gkrLayersG_even]
    refine runs_bind' rfl hsR fun st hst ↦ ?_
    obtain ⟨sv, sp⟩ := st
    obtain ⟨h1, h2⟩ := hst
    simp only at h1 h2
    subst h1 h2
    exact ho

/-! ## `count ≠ 0` and the walk's gadget -/

/-- `x^(2^n) ` squarings with their running product. -/
def nzChain (z : C2) : ℕ → C2 → C2 → BM C2
  | 0, _, acc => pure acc
  | n + 1, s, acc => g2Mul s s z >>= fun s' ↦ g2Mul acc s' z >>= fun acc' ↦ nzChain z n s' acc'

/-- **`x ≠ 0`**: `x·x^(2^128 − 2) + 1 = 0`, gated (the product of 127 squarings). -/
def nz6 (z o x : C2) (gate : Cell) : BM Unit :=
  nzChain z 127 x o >>= fun p ↦ g2Mul x p o >>= fun t ↦ g2Assert t gate

theorem nz6_sound {z o x : C2} (ho : o.val M = 1) {gate : Cell} (hg : gate.val M = 1) :
    HsA c M (nz6 z o x gate) (fun _ ↦ ev2 M x ≠ 0) :=
  hsA_bind (hsA_of_hs (hs_true _)) fun p _ ↦ hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun t ht ↦
    hsA_mono (hsA_g2Assert t gate hg) fun _ h0 ↦ by
      intro hx
      have hx' : x.val M = 0 := FE2.toE2_injective (by rw [FE2.toE2_zero]; exact hx)
      rw [ht, hx', zero_mul, zero_add, ho] at h0
      exact one_ne_zero h0

/-- `α`'s cells. -/
def alC (a : ℕ) : List C2 := [ld2 (a + 1), ld2 (a + 10), ld2 (a + 19), ld2 (a + 28)]

/-- **The mini-bus walk's gadget.** -/
def mb6 (a : ℕ) (gate : Cell) : BM MbOutC :=
  g2Zero (ld2 a) >>= fun z ↦ g2Const 1 (ld2 a) >>= fun o ↦ nz6 z o (ld2 (a + 48)) gate >>= fun _ ↦
    gsteps6 z gate 6 (a + 50) [ld2 (a + 46), ld2 (a + 46), ld2 (a + 48)] [] >>= fun s ↦
      pure ⟨alC a, ld2 (a + 37), s.2, s.1⟩

/-- **CD-5**: `mb6` re-executes the mini-bus's GKR walk. -/
theorem mb6_har : MbHarStmt mb6 := by
  intro a gate c M hg
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Const 1 _)) fun o ho ↦ ?_
  refine hsA_bind (nz6_sound ho hg) fun _ hnz ↦ ?_
  refine hsA_bind (gsteps6_runs hz hg 6 0 (a + 50) _ [] rfl rfl rfl) fun s hs ↦ hsA_pure ?_
  show Runs M (layItems mbItems a) (lvmBusProgG miniDepth) _
  have hl : layItems mbItems a = layItems [.G gAB, .D 4] a ++
      ([LEv.e (a + 46)] ++ ([LEv.e (a + 48)] ++ layItems ((List.range' 0 6).flatMap mbStep) (a + 50))) := by
    rw [mbItems, layItems_append, show [Lvm6.V.Item.G gAB, .D 4, .E 2] = [.G gAB, .D 4] ++ [.E 2] from rfl,
      layItems_append, List.append_assoc, List.range_eq_range']; rfl
  rw [hl]
  unfold lvmBusProgG verifyGkrGrandProductsG
  rw [e2SampleN_gPoint]
  refine runs_bind' rfl (runs_gPoint M (by norm_num) 4 a) fun ab hab ↦ ?_
  simp only [bind_assoc]
  refine runs_bind' rfl (runs_e2Read M (a + 46)) fun sh hsh ↦ ?_
  refine runs_bind' rfl (runs_e2Read M (a + 48)) fun cnt hcnt ↦ ?_
  subst hsh hcnt
  refine runs_bind' (l₂ := []) (List.append_nil _).symm (show Runs M _ (gkrLayersG (2 * 6) _) _ from hs)
    fun st hst ↦ ?_
  simp only [pure_bind]
  refine runs_bind' (l₁ := []) (l₂ := []) rfl (runs_require hnz) fun _ _ ↦ runs_pure ?_
  exact ⟨by rw [hab]; rfl, by rw [hab]; rfl, hst.2, hst.1⟩

end Lvm6.QD
