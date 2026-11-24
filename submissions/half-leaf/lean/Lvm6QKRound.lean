-- New for lvm6 (WP CB). The sumcheck rounds of the v6 Keccak programs as `E2` gadgets, with their
-- HARs on the DSL: plain rounds of count 3 (season 1's `sc2`, the same 14-lane geometry under
-- FORMAT6 §4), plain rounds of count 4 (`sc4`, 16 lanes) and K0's normalized eq-mode pack rounds
-- (`eqRounds6`, no scale).
import Lvm6QKRun
import LvmE2QWKitSem

/-!
# Sumcheck rounds (generator and HAR)

Lanes of a round `R(n, g)` from the lane `q` of its `buf` (FORMAT6 §4): the `n` scalars at
`q, q + 2, …`, the nonce at `q + 2n`, the answer at `q + 2n + 1`; the next round's `buf` at
`q + 2n + 10`.

* **`sc2 R q claim`** (season 1, `LvmE2QWKit`): `R` plain rounds of count 3 (`c₀, c₂`), 14 lanes
  apart. **`sc2_runs`**: it re-executes `sumcheckE2 g claim 3 (replicate R none)` (FORMAT6
  `rep R (rnd 2 g)`): the challenges are the answers' lanes, the final claim is `scFold2`.
* **`sc4 R q claim`**: `R` plain rounds of count 4 (`c₀, c₂, c₃`, the layer's position rounds,
  `rnd 3 g`), 16 lanes apart; **`sc4_runs`**.
* **`eqRounds6 q value rs`**: K0's normalized pack rounds (`packRoundsN g rs value`, `rnd 2 g`
  per coordinate of `rs`): `c₀ = value + r·(c₁ + c₂)`, next value `(c₂·c + c₁)·c + c₀`, 3 products
  a round; **`eqRounds6_runs`**.

Every statement is `HsA` of `Runs` (the gadgets have no assertion: the round checks of a
sumcheck are carried in the claim, never asserted round by round).
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K Lvm6.KPack
open Lvm6 (Item rep rnd)

variable {c : Ctx} {M : Mem}

/-! ## Values through `toE2` -/

theorem ev2_mul {r a b d : C2} (h : r.val M = a.val M * b.val M + d.val M) :
    ev2 M r = ev2 M a * ev2 M b + ev2 M d := by
  simp only [ev2, h, FE2.toE2_add, FE2.fe2_mul_eq]

theorem ev2_add {r a b : C2} (h : r.val M = a.val M + b.val M) : ev2 M r = ev2 M a + ev2 M b := by
  simp only [ev2, h, FE2.toE2_add]

/-! ## Layouts of rounds -/

theorem rep_succ (n : ℕ) (l : List Item) : rep (n + 1) l = l ++ rep n l := rfl

theorem lay_rnd2 (g q : ℕ) (rest : List Item) :
    layItems (rnd 2 g ++ rest) q = [.e q, .e (q + 2), .k (q + 4), .d (q + 5) g] ++
      layItems rest (q + 14) := by
  simp [rnd, layItems, List.range_succ]

theorem lay_rnd3 (g q : ℕ) (rest : List Item) :
    layItems (rnd 3 g ++ rest) q = [.e q, .e (q + 2), .e (q + 4), .k (q + 6), .d (q + 7) g] ++
      layItems rest (q + 16) := by
  simp [rnd, layItems, List.range_succ]

/-! ## Plain rounds of count 3 -/

/-- One plain round of count 3 on the DSL: `c₀`, `c₂`, the ground draw. -/
theorem runs_plain3 (g : ℕ) (hg : g ≤ 64) (q : ℕ) (claim : E2) :
    Runs M [.e q, .e (q + 2), .k (q + 4), .d (q + 5) g]
      (roundPolyE2 3 claim none >>= fun msg ↦ e2Sample g >>= fun ch ↦ pure (msg, ch))
      (fun res ↦ res = ([ev2 M (ld2 q), claim + ev2 M (ld2 (q + 2)), ev2 M (ld2 (q + 2))],
        ev2 M (ld2 (q + 5)))) := by
  refine runs_bind' (l₁ := [_, _]) (P := fun msg ↦ msg = [ev2 M (ld2 q), claim + ev2 M (ld2 (q + 2)),
    ev2 M (ld2 (q + 2))]) rfl ?_ fun msg hmsg ↦ runs_bind' (l₂ := []) rfl
    (runs_e2Sample M hg (q + 4)) fun ch hch ↦ runs_pure (by rw [hmsg, hch])
  refine runs_bind' (l₁ := [_]) rfl (runs_e2Read M q) fun c0 hc0 ↦ runs_bind' (l₂ := []) rfl
    (runs_e2Reads M 1 (q + 2)) fun tl htl ↦ runs_pure ?_
  simp [hc0, htl, scal, sumF]

/-- **`sc2` re-executes the plain rounds of count 3.** -/
theorem sc2_runs (g : ℕ) (hg : g ≤ 64) : ∀ (R q : ℕ) (claim : C2),
    Hs c M (sc2 R q claim) fun o ↦
      Runs M (layItems (rep R (rnd 2 g)) q) (sumcheckE2 g (ev2 M claim) 3 (List.replicate R none))
        (fun res ↦ res.1 = o.1.map (ev2 M) ∧ res.2 = ev2 M o.2)
  | 0, q, claim => hs_pure (runs_pure ⟨rfl, rfl⟩)
  | R + 1, q, claim => by
    refine hs_bind (hs_scRound2 q claim) fun rc ⟨h1, h2⟩ ↦
      hs_bind (sc2_runs g hg R (q + roundLanes2) rc.2) fun res hres ↦ hs_pure ?_
    rw [rep_succ, lay_rnd2]
    show Runs M _ (roundPolyE2 3 (ev2 M claim) none >>= fun msg ↦ e2Sample g >>= fun ch ↦
      sumcheckE2 g (polyEvalF msg ch) 3 (List.replicate R none) >>= fun r ↦ pure (ch :: r.1, r.2)) _
    have e : (roundPolyE2 3 (ev2 M claim) none >>= fun msg ↦ e2Sample g >>= fun ch ↦
        sumcheckE2 g (polyEvalF msg ch) 3 (List.replicate R none) >>= fun r ↦ pure (ch :: r.1, r.2)) =
        ((roundPolyE2 3 (ev2 M claim) none >>= fun msg ↦ e2Sample g >>= fun ch ↦ pure (msg, ch)) >>=
          fun mc ↦ sumcheckE2 g (polyEvalF mc.1 mc.2) 3 (List.replicate R none) >>= fun r ↦
            pure (mc.2 :: r.1, r.2)) := by
      simp only [bind_assoc, pure_bind]
    rw [e]
    refine runs_bind' (l₂ := layItems (rep R (rnd 2 g)) (q + 14)) rfl (runs_plain3 g hg q _)
      fun mc hmc ↦ ?_
    have hv : polyEvalF mc.1 mc.2 = ev2 M rc.2 := by
      rw [hmc]
      simp only [ev2, h2, polyEvalF, List.foldr, scStep2, FE2.toE2_add, FE2.fe2_mul_eq]
      ring
    rw [hv]
    refine runs_bind' (l₂ := []) (List.append_nil _).symm hres fun r hr ↦ runs_pure ?_
    rw [hr.1, hr.2, h1, hmc]
    exact ⟨rfl, rfl⟩

/-! ## Plain rounds of count 4 (the layer's position rounds) -/

/-- **One plain round of count 4** at lane `q`: `c₀, c₂, c₃` at `q, q + 2, q + 4`, the answer at
`q + 7`; `c₁ = claim + c₂ + c₃`, the next claim `((c₃·r + c₂)·r + c₁)·r + c₀`. -/
def sc4Round (q : ℕ) (claim : C2) : BM (C2 × C2) :=
  let c0 := ld2 q
  let c2 := ld2 (q + 2)
  let c3 := ld2 (q + 4)
  let r := ld2 (q + 7)
  g2Add claim c2 >>= fun s ↦ g2Add s c3 >>= fun c1 ↦ g2Mul c3 r c2 >>= fun t ↦
    g2Mul t r c1 >>= fun t' ↦ g2Mul t' r c0 >>= fun nc ↦ pure (r, nc)

/-- **`R` plain rounds of count 4** from lane `q` (16 lanes apart). -/
def sc4 : ℕ → ℕ → C2 → BM (List C2 × C2)
  | 0, _, claim => pure ([], claim)
  | R + 1, q, claim => sc4Round q claim >>= fun rc ↦ sc4 R (q + 16) rc.2 >>= fun res ↦
    pure (rc.1 :: res.1, res.2)

theorem runs_plain4 (g : ℕ) (hg : g ≤ 64) (q : ℕ) (claim : E2) :
    Runs M [.e q, .e (q + 2), .e (q + 4), .k (q + 6), .d (q + 7) g]
      (roundPolyE2 4 claim none >>= fun msg ↦ e2Sample g >>= fun ch ↦ pure (msg, ch))
      (fun res ↦ res = ([ev2 M (ld2 q), claim + ev2 M (ld2 (q + 2)) + ev2 M (ld2 (q + 4)),
        ev2 M (ld2 (q + 2)), ev2 M (ld2 (q + 4))], ev2 M (ld2 (q + 7)))) := by
  refine runs_bind' (l₁ := [_, _, _]) (P := fun msg ↦ msg = [ev2 M (ld2 q),
    claim + ev2 M (ld2 (q + 2)) + ev2 M (ld2 (q + 4)), ev2 M (ld2 (q + 2)), ev2 M (ld2 (q + 4))])
    rfl ?_ fun msg hmsg ↦ runs_bind' (l₂ := []) rfl (runs_e2Sample M hg (q + 6)) fun ch hch ↦
      runs_pure (by rw [hmsg, hch])
  refine runs_bind' (l₁ := [_]) rfl (runs_e2Read M q) fun c0 hc0 ↦ runs_bind' (l₂ := []) rfl
    (runs_e2Reads M 2 (q + 2)) fun tl htl ↦ runs_pure ?_
  simp only [hc0, htl, scal, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, sumF, List.foldl, zero_add]
  ring_nf

theorem hs_sc4Round (q : ℕ) (claim : C2) :
    Hs c M (sc4Round q claim) (fun rc ↦ rc.1 = ld2 (q + 7) ∧
      ev2 M rc.2 = ((ev2 M (ld2 (q + 4)) * ev2 M (ld2 (q + 7)) + ev2 M (ld2 (q + 2))) *
        ev2 M (ld2 (q + 7)) + (ev2 M claim + ev2 M (ld2 (q + 2)) + ev2 M (ld2 (q + 4)))) *
          ev2 M (ld2 (q + 7)) + ev2 M (ld2 q)) :=
  hs_bind (hs_g2Add _ _) fun s hs ↦ hs_bind (hs_g2Add _ _) fun c1 hc1 ↦
    hs_bind (hs_g2Mul _ _ _) fun t ht ↦ hs_bind (hs_g2Mul _ _ _) fun t' ht' ↦
      hs_bind (hs_g2Mul _ _ _) fun nc hnc ↦ hs_pure ⟨rfl, by
        rw [ev2_mul hnc, ev2_mul ht', ev2_mul ht, ev2_add hc1, ev2_add hs]⟩

theorem lay_rnd3' (g q : ℕ) (R : ℕ) :
    layItems (rep (R + 1) (rnd 3 g)) q = [.e q, .e (q + 2), .e (q + 4), .k (q + 6), .d (q + 7) g] ++
      layItems (rep R (rnd 3 g)) (q + 16) := by
  rw [rep_succ, lay_rnd3]

/-- **`sc4` re-executes the plain rounds of count 4.** -/
theorem sc4_runs (g : ℕ) (hg : g ≤ 64) : ∀ (R q : ℕ) (claim : C2),
    Hs c M (sc4 R q claim) fun o ↦
      Runs M (layItems (rep R (rnd 3 g)) q) (sumcheckE2 g (ev2 M claim) 4 (List.replicate R none))
        (fun res ↦ res.1 = o.1.map (ev2 M) ∧ res.2 = ev2 M o.2)
  | 0, q, claim => hs_pure (runs_pure ⟨rfl, rfl⟩)
  | R + 1, q, claim => by
    refine hs_bind (hs_sc4Round q claim) fun rc ⟨h1, h2⟩ ↦
      hs_bind (sc4_runs g hg R (q + 16) rc.2) fun res hres ↦ hs_pure ?_
    rw [lay_rnd3']
    show Runs M _ (roundPolyE2 4 (ev2 M claim) none >>= fun msg ↦ e2Sample g >>= fun ch ↦
      sumcheckE2 g (polyEvalF msg ch) 4 (List.replicate R none) >>= fun r ↦ pure (ch :: r.1, r.2)) _
    have e : (roundPolyE2 4 (ev2 M claim) none >>= fun msg ↦ e2Sample g >>= fun ch ↦
        sumcheckE2 g (polyEvalF msg ch) 4 (List.replicate R none) >>= fun r ↦ pure (ch :: r.1, r.2)) =
        ((roundPolyE2 4 (ev2 M claim) none >>= fun msg ↦ e2Sample g >>= fun ch ↦ pure (msg, ch)) >>=
          fun mc ↦ sumcheckE2 g (polyEvalF mc.1 mc.2) 4 (List.replicate R none) >>= fun r ↦
            pure (mc.2 :: r.1, r.2)) := by
      simp only [bind_assoc, pure_bind]
    rw [e]
    refine runs_bind' (l₂ := layItems (rep R (rnd 3 g)) (q + 16)) rfl (runs_plain4 g hg q _)
      fun mc hmc ↦ ?_
    have hv : polyEvalF mc.1 mc.2 = ev2 M rc.2 := by
      rw [hmc, h2]
      simp only [polyEvalF, List.foldr]
      ring
    rw [hv]
    refine runs_bind' (l₂ := []) (List.append_nil _).symm hres fun r hr ↦ runs_pure ?_
    rw [hr.1, hr.2, h1, hmc]
    exact ⟨rfl, rfl⟩

/-! ## Normalized eq-mode pack rounds (K0) -/

/-- **One normalized pack round** at lane `q` with factor `r`: `c₁, c₂` at `q, q + 2`, the answer
`ch` at `q + 5`; `c₀ = value + r·(c₁ + c₂)`, the next value `(c₂·ch + c₁)·ch + c₀`. -/
def eqRound6 (q : ℕ) (value r : C2) : BM (C2 × C2) :=
  let c1 := ld2 q
  let c2 := ld2 (q + 2)
  let ch := ld2 (q + 5)
  g2Add c1 c2 >>= fun s ↦ g2Mul r s value >>= fun c0 ↦ g2Mul c2 ch c1 >>= fun t ↦
    g2Mul t ch c0 >>= fun nv ↦ pure (ch, nv)

/-- **The pack rounds over the point `rs`** from lane `q` (14 lanes apart): the final value and
the challenges. -/
def eqRounds6 : ℕ → C2 → List C2 → BM (C2 × List C2)
  | _, value, [] => pure (value, [])
  | q, value, r :: rs => eqRound6 q value r >>= fun rc ↦ eqRounds6 (q + 14) rc.2 rs >>= fun res ↦
    pure (res.1, rc.1 :: res.2)

theorem hs_eqRound6 (q : ℕ) (value r : C2) :
    Hs c M (eqRound6 q value r) (fun rc ↦ rc.1 = ld2 (q + 5) ∧
      ev2 M rc.2 = (ev2 M (ld2 (q + 2)) * ev2 M (ld2 (q + 5)) + ev2 M (ld2 q)) * ev2 M (ld2 (q + 5)) +
        (ev2 M r * (ev2 M (ld2 q) + ev2 M (ld2 (q + 2))) + ev2 M value)) :=
  hs_bind (hs_g2Add _ _) fun s hs ↦ hs_bind (hs_g2Mul _ _ _) fun c0 hc0 ↦
    hs_bind (hs_g2Mul _ _ _) fun t ht ↦ hs_bind (hs_g2Mul _ _ _) fun nv hnv ↦ hs_pure ⟨rfl, by
      rw [ev2_mul hnv, ev2_mul ht, ev2_mul hc0, ev2_add hs]⟩

theorem runs_eqMsg (g : ℕ) (hg : g ≤ 64) (q : ℕ) (value r : E2) :
    Runs M [.e q, .e (q + 2), .k (q + 4), .d (q + 5) g]
      (roundPolyE2 3 value (some r) >>= fun msg ↦ e2Sample g >>= fun ch ↦ pure (msg, ch))
      (fun res ↦ res = ([value + r * (ev2 M (ld2 q) + ev2 M (ld2 (q + 2))), ev2 M (ld2 q),
        ev2 M (ld2 (q + 2))], ev2 M (ld2 (q + 5)))) := by
  refine runs_bind' (l₁ := [_, _]) (P := fun msg ↦ msg = [value + r * (ev2 M (ld2 q) +
    ev2 M (ld2 (q + 2))), ev2 M (ld2 q), ev2 M (ld2 (q + 2))]) rfl ?_ fun msg hmsg ↦
      runs_bind' (l₂ := []) rfl (runs_e2Sample M hg (q + 4)) fun ch hch ↦
        runs_pure (by rw [hmsg, hch])
  refine runs_bind' (l₂ := []) (List.append_nil _).symm (runs_e2Reads M 2 q) fun tl htl ↦
    runs_pure ?_
  simp only [htl, scal, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, sumF, List.foldl, zero_add, mul_zero, add_zero]

/-- **`eqRounds6` re-executes K0's normalized pack rounds.** -/
theorem eqRounds6_runs (g : ℕ) (hg : g ≤ 64) : ∀ (q : ℕ) (value : C2) (rs : List C2),
    Hs c M (eqRounds6 q value rs) fun o ↦
      Runs M (layItems (rep rs.length (rnd 2 g)) q) (packRoundsN g (rs.map (ev2 M)) (ev2 M value))
        (fun res ↦ res.1 = ev2 M o.1 ∧ res.2 = o.2.map (ev2 M))
  | q, value, [] => hs_pure (runs_pure ⟨rfl, rfl⟩)
  | q, value, r :: rs => by
    refine hs_bind (hs_eqRound6 q value r) fun rc ⟨h1, h2⟩ ↦
      hs_bind (eqRounds6_runs g hg (q + 14) rc.2 rs) fun res hres ↦ hs_pure ?_
    rw [List.length_cons, rep_succ, lay_rnd2]
    show Runs M _ (roundPolyE2 3 (ev2 M value) (some (ev2 M r)) >>= fun msg ↦ e2Sample g >>= fun ch ↦
      packRoundsN g (rs.map (ev2 M)) (polyEvalF msg ch) >>= fun res ↦ pure (res.1, ch :: res.2)) _
    have e : (roundPolyE2 3 (ev2 M value) (some (ev2 M r)) >>= fun msg ↦ e2Sample g >>= fun ch ↦
        packRoundsN g (rs.map (ev2 M)) (polyEvalF msg ch) >>= fun res ↦ pure (res.1, ch :: res.2)) =
        ((roundPolyE2 3 (ev2 M value) (some (ev2 M r)) >>= fun msg ↦ e2Sample g >>= fun ch ↦
          pure (msg, ch)) >>= fun mc ↦ packRoundsN g (rs.map (ev2 M)) (polyEvalF mc.1 mc.2) >>=
            fun res ↦ pure (res.1, mc.2 :: res.2)) := by
      simp only [bind_assoc, pure_bind]
    rw [e]
    refine runs_bind' (l₂ := layItems (rep rs.length (rnd 2 g)) (q + 14)) rfl
      (runs_eqMsg g hg q _ _) fun mc hmc ↦ ?_
    have hv : polyEvalF mc.1 mc.2 = ev2 M rc.2 := by
      rw [hmc, h2]
      simp only [polyEvalF, List.foldr]
      ring
    rw [hv]
    refine runs_bind' (l₂ := []) (List.append_nil _).symm hres fun r' hr ↦ runs_pure ?_
    rw [hr.1, hr.2, h1, hmc]
    exact ⟨rfl, rfl⟩

end Lvm6.QK
