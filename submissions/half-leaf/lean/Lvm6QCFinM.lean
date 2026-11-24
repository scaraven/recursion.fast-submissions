-- New for lvm6 (WP CLG, second slice). Claim 44's gadget (FORMAT6 §6.5: the sponge link's stream
-- claim `Σ_{ℓ<17, x<7168} eq(λ, ℓ)·eq(ρ', x)·M(x, ℓ)`, `M(x, ℓ)` the stream word `17x + ℓ`): the
-- weight's extension at the point by a carry recursion over the point's 19 low coordinates.
import Lvm6QCFinC

/-!
# Claim 44 (CLG)

`F(c, X, L) = Σ_{x<X, ℓ<L} eq(ρ, x)·eq(λ, ℓ)·eq(Y, 17x + ℓ + c)` satisfies, with `Y = y :: Y'` and
`x = 2x' + a`, `ℓ = 2ℓ' + b` (`cmF_cons`):

`F(c, X, L) = Σ_{a,b ∈ {0,1}} h_ρ(a)·h_λ(b)·e(y, (a+b+c) mod 2)·F'((17a+b+c)/2, ⌊(X+1−a)/2⌋, ⌊(L+1−b)/2⌋)`

(`h_ρ(a)` the low coordinate's factor, `1` once `ρ` is exhausted), and at `Y = []` it is
`(Σ_{x<X} eq(ρ, x))·(Σ_{ℓ<L} eq(λ, ℓ))` (`cmF_nil`, CLG's `ltS`). Carries stay `≤ 17` and the bounds at
level `k` are `⌊X/2^k⌋ + {0, 1}`, so each level is a table of `18·2·2 = 72` cells (`cmTab`), each
cell four products of the next level's table (`cmEntryG`). The weight of claim 44 at `pt` is
`eq(pt_{19..25}, 33)·F(0, 7168, 17)` at `Y = pt_{<19}` (`cMW_eq`).

**Gadget** `cMG` (one instance), **`cM_ok : ClaimAt Pre (SP.cM lk) (cMG lc ρc)`**.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm6.QK

variable {c : Ctx} {M : Mem}

/-! ## The recursion -/

/-- `F(c, X, L) = Σ_{x<X, ℓ<L} eq(ρ, x)·eq(λ, ℓ)·eq(Y, 17x + ℓ + c)`. -/
noncomputable def cmF (ρ lam Y : List E2) (c X L : ℕ) : E2 :=
  ∑ x ∈ Finset.range X, ∑ l ∈ Finset.range L,
    E2V.eqAtF ρ x * E2V.eqAtF lam l * E2V.eqAtF Y (17 * x + l + c)

theorem cmF_congr (ρ lam Y : List E2) {c c' X X' L L' : ℕ} (h1 : c = c') (h2 : X = X') (h3 : L = L') :
    cmF ρ lam Y c X L = cmF ρ lam Y c' X' L' := by
  subst h1 h2 h3; rfl

/-- The low coordinate's factor at bit `a` (`1` once the point is exhausted). -/
def cmHd : List E2 → ℕ → E2
  | [], _ => 1
  | r :: _, a => if a = 1 then r else 1 + r

theorem eqAtF_two (ρ : List E2) (x a : ℕ) (ha : a < 2) :
    E2V.eqAtF ρ (2 * x + a) = cmHd ρ a * E2V.eqAtF ρ.tail x := by
  cases ρ with
  | nil => simp [cmHd, E2V.eqAtF]
  | cons r rs =>
    rw [E2V.eqAtF_succ, show (2 * x + a) / 2 = x by omega, List.tail_cons]
    simp only [cmHd]
    by_cases h : a = 1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]

/-- `⌊(X + 1 − a)/2⌋`: the bound on `x'` for `x = 2x' + a < X`. -/
def cmHalf (X a : ℕ) : ℕ := (X + 1 - a) / 2

theorem sum_par (g : ℕ → E2) (X : ℕ) :
    ∑ x ∈ Finset.range X, g x = ∑ x ∈ Finset.range (cmHalf X 0), g (2 * x + 0) +
      ∑ x ∈ Finset.range (cmHalf X 1), g (2 * x + 1) := by
  simp only [cmHalf, add_zero, Nat.sub_zero, Nat.add_sub_cancel]
  rcases Nat.even_or_odd' X with ⟨n, rfl | rfl⟩
  · rw [E2V.sum_range_two_mulW, Finset.sum_add_distrib, show (2 * n + 1) / 2 = n by omega,
      show 2 * n / 2 = n by omega]
  · rw [Finset.sum_range_succ, E2V.sum_range_two_mulW, Finset.sum_add_distrib,
      show (2 * n + 1 + 1) / 2 = n + 1 by omega, show (2 * n + 1) / 2 = n by omega,
      Finset.sum_range_succ]
    ring

theorem sum2_par (g : ℕ → ℕ → E2) (X L : ℕ) :
    ∑ x ∈ Finset.range X, ∑ l ∈ Finset.range L, g x l =
      ∑ x ∈ Finset.range (cmHalf X 0), ∑ l ∈ Finset.range (cmHalf L 0), g (2 * x + 0) (2 * l + 0) +
      ∑ x ∈ Finset.range (cmHalf X 0), ∑ l ∈ Finset.range (cmHalf L 1), g (2 * x + 0) (2 * l + 1) +
      (∑ x ∈ Finset.range (cmHalf X 1), ∑ l ∈ Finset.range (cmHalf L 0), g (2 * x + 1) (2 * l + 0) +
      ∑ x ∈ Finset.range (cmHalf X 1), ∑ l ∈ Finset.range (cmHalf L 1), g (2 * x + 1) (2 * l + 1)) := by
  rw [sum_par (fun x ↦ ∑ l ∈ Finset.range L, g x l) X]
  simp only [sum_par (g _) L, Finset.sum_add_distrib]

/-- The weight of branch `(a, b)` at carry `c`. -/
def cmW (ρ lam : List E2) (y : E2) (c a b : ℕ) : E2 :=
  cmHd ρ a * cmHd lam b * (if (a + b + c) % 2 = 1 then y else 1 + y)

theorem cmF_cons (ρ lam Y : List E2) (y : E2) (c X L : ℕ) :
    cmF ρ lam (y :: Y) c X L =
      cmW ρ lam y c 0 0 * cmF ρ.tail lam.tail Y ((17 * 0 + 0 + c) / 2) (cmHalf X 0) (cmHalf L 0) +
      cmW ρ lam y c 0 1 * cmF ρ.tail lam.tail Y ((17 * 0 + 1 + c) / 2) (cmHalf X 0) (cmHalf L 1) +
      (cmW ρ lam y c 1 0 * cmF ρ.tail lam.tail Y ((17 * 1 + 0 + c) / 2) (cmHalf X 1) (cmHalf L 0) +
      cmW ρ lam y c 1 1 * cmF ρ.tail lam.tail Y ((17 * 1 + 1 + c) / 2) (cmHalf X 1) (cmHalf L 1)) := by
  have key : ∀ a b, a < 2 → b < 2 → ∀ Xr Lr, (∑ x ∈ Finset.range Xr, ∑ l ∈ Finset.range Lr,
      E2V.eqAtF ρ (2 * x + a) * E2V.eqAtF lam (2 * l + b) *
        E2V.eqAtF (y :: Y) (17 * (2 * x + a) + (2 * l + b) + c)) =
      cmW ρ lam y c a b * cmF ρ.tail lam.tail Y ((17 * a + b + c) / 2) Xr Lr := by
    intro a b ha hb Xr Lr
    rw [cmF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [eqAtF_two ρ x a ha, eqAtF_two lam l b hb, E2V.eqAtF_succ,
      show (17 * (2 * x + a) + (2 * l + b) + c) / 2 = 17 * x + l + (17 * a + b + c) / 2 by omega]
    unfold cmW
    by_cases h : (a + b + c) % 2 = 1
    · rw [if_pos (show (17 * (2 * x + a) + (2 * l + b) + c) % 2 = 1 by omega), if_pos h]
      ring
    · rw [if_neg (show ¬ (17 * (2 * x + a) + (2 * l + b) + c) % 2 = 1 by omega), if_neg h]
      ring
  rw [cmF, sum2_par (fun x l ↦ E2V.eqAtF ρ x * E2V.eqAtF lam l * E2V.eqAtF (y :: Y) (17 * x + l + c))]
  rw [key 0 0 (by norm_num) (by norm_num), key 0 1 (by norm_num) (by norm_num),
    key 1 0 (by norm_num) (by norm_num), key 1 1 (by norm_num) (by norm_num)]

theorem cmF_nil (ρ lam : List E2) (c X L : ℕ) :
    cmF ρ lam [] c X L = ltS (fpE ρ []) X * ltS (fpE lam []) L := by
  have h0 : ∀ n, E2V.eqAtF ([] : List E2) n = 1 := fun _ ↦ rfl
  rw [cmF, ltS, ltS, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [termP_fpE, termP_fpE, h0, h0, h0]
  ring

/-! ## The level tables -/

/-- Entry `j` of a level's table: carry `j/4`, bounds `X + (j/2 mod 2)`, `L + (j mod 2)`. -/
noncomputable def cmTab (ρ lam Y : List E2) (X L j : ℕ) : E2 :=
  cmF ρ lam Y (j / 4) (X + j / 2 % 2) (L + j % 2)

/-- Where branch `(a, b)` of a state lands in the next level's table (base `X/2`, `L/2`). -/
def cmIdx (a b c X' L' X L : ℕ) : ℕ :=
  (17 * a + b + c) / 2 * 4 + (cmHalf X' a - X / 2) * 2 + (cmHalf L' b - L / 2)

theorem cmTab_cons (ρ lam Y : List E2) (y : E2) (X L i : ℕ) :
    cmTab ρ lam (y :: Y) X L i =
      cmW ρ lam y (i / 4) 0 0 * cmTab ρ.tail lam.tail Y (X / 2) (L / 2)
        (cmIdx 0 0 (i / 4) (X + i / 2 % 2) (L + i % 2) X L) +
      cmW ρ lam y (i / 4) 0 1 * cmTab ρ.tail lam.tail Y (X / 2) (L / 2)
        (cmIdx 0 1 (i / 4) (X + i / 2 % 2) (L + i % 2) X L) +
      (cmW ρ lam y (i / 4) 1 0 * cmTab ρ.tail lam.tail Y (X / 2) (L / 2)
        (cmIdx 1 0 (i / 4) (X + i / 2 % 2) (L + i % 2) X L) +
      cmW ρ lam y (i / 4) 1 1 * cmTab ρ.tail lam.tail Y (X / 2) (L / 2)
        (cmIdx 1 1 (i / 4) (X + i / 2 % 2) (L + i % 2) X L)) := by
  have e : ∀ a b, a < 2 → b < 2 → cmF ρ.tail lam.tail Y ((17 * a + b + i / 4) / 2)
      (cmHalf (X + i / 2 % 2) a) (cmHalf (L + i % 2) b) =
      cmTab ρ.tail lam.tail Y (X / 2) (L / 2) (cmIdx a b (i / 4) (X + i / 2 % 2) (L + i % 2) X L) := by
    intro a b ha hb
    unfold cmTab cmIdx
    have hx1 : cmHalf (X + i / 2 % 2) a ≤ X / 2 + 1 := by unfold cmHalf; omega
    have hx2 : X / 2 ≤ cmHalf (X + i / 2 % 2) a := by unfold cmHalf; omega
    have hl1 : cmHalf (L + i % 2) b ≤ L / 2 + 1 := by unfold cmHalf; omega
    have hl2 : L / 2 ≤ cmHalf (L + i % 2) b := by unfold cmHalf; omega
    generalize cmHalf (X + i / 2 % 2) a = hX at *
    generalize cmHalf (L + i % 2) b = hL at *
    generalize (17 * a + b + i / 4) / 2 = q
    exact cmF_congr _ _ _ (by omega) (by omega) (by omega)
  show cmF ρ lam (y :: Y) (i / 4) (X + i / 2 % 2) (L + i % 2) = _
  rw [cmF_cons, e 0 0 (by norm_num) (by norm_num), e 0 1 (by norm_num) (by norm_num),
    e 1 0 (by norm_num) (by norm_num), e 1 1 (by norm_num) (by norm_num)]

theorem cmIdx_lt {a b i X L : ℕ} (ha : a < 2) (hb : b < 2) (hi : i < 72) :
    cmIdx a b (i / 4) (X + i / 2 % 2) (L + i % 2) X L < 72 := by
  unfold cmIdx
  have hx1 : cmHalf (X + i / 2 % 2) a ≤ X / 2 + 1 := by unfold cmHalf; omega
  have hl1 : cmHalf (L + i % 2) b ≤ L / 2 + 1 := by unfold cmHalf; omega
  have hq : (17 * a + b + i / 4) / 2 ≤ 17 := by omega
  generalize cmHalf (X + i / 2 % 2) a = hX at *
  generalize cmHalf (L + i % 2) b = hL at *
  generalize (17 * a + b + i / 4) / 2 = q at *
  omega

/-! ## Gadgets -/

theorem hs_mapB_eq {f : ℕ → BM C2} {g : ℕ → E2} : ∀ (l : List ℕ),
    (∀ i ∈ l, Hs c M (f i) fun o ↦ ev2 M o = g i) →
      Hs c M (mapB f l) fun os ↦ os.map (ev2 M) = l.map g
  | [], _ => hs_pure rfl
  | i :: l, h => hs_bind (h i (List.mem_cons_self ..)) fun o ho ↦
      hs_bind (hs_mapB_eq l fun j hj ↦ h j (List.mem_cons_of_mem _ hj)) fun os hos ↦
        hs_pure (by rw [List.map_cons, List.map_cons, ho, hos])

theorem ev2_getD_tab {l : List C2} {g : ℕ → E2} {n j : ℕ} (h : l.map (ev2 M) = (List.range n).map g)
    (hj : j < n) (z : C2) : ev2 M (l.getD j z) = g j := by
  have hl : l.length = n := by simpa using congrArg List.length h
  have h2 := congrArg (fun l' ↦ l'[j]?) h
  simp only [List.getElem?_map, List.getElem?_range hj, List.getElem?_eq_getElem (hl ▸ hj),
    Option.map_some, Option.some.injEq] at h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ hj), Option.getD_some, h2]

/-- The low coordinate's two factors as cells (`(1, 1)` once the point is exhausted). -/
def cmHdC (one : C2) : List C2 → BM (C2 × C2)
  | [] => pure (one, one)
  | r :: _ => g2One r >>= fun r1 ↦ pure (r1, r)

theorem hs_cmHdC {one : C2} (hone : ev2 M one = 1) : ∀ ρc : List C2, Hs c M (cmHdC one ρc) fun p ↦
    ev2 M p.1 = cmHd (ρc.map (ev2 M)) 0 ∧ ev2 M p.2 = cmHd (ρc.map (ev2 M)) 1
  | [] => hs_pure ⟨by simp [cmHd, hone], by simp [cmHd, hone]⟩
  | r :: _ => hs_bind (hs_g2One r) fun r1 h1 ↦ hs_pure ⟨by simp [cmHd, ev2_onePlus h1], by simp [cmHd]⟩

/-- Branch `(a, b)`'s weight cell at parity `e mod 2`. -/
def cmSel (z : C2) (ws : List (C2 × C2)) (a b e : ℕ) : C2 :=
  if e % 2 = 1 then (ws.getD (2 * a + b) (z, z)).2 else (ws.getD (2 * a + b) (z, z)).1

/-- **One table entry** (one instance per entry): four products of the next level's table. -/
def cmEntryG (z : C2) (ws : List (C2 × C2)) (nxt : List C2) (X L i : ℕ) : BM C2 :=
  g2Mul (cmSel z ws 0 0 (0 + 0 + i / 4)) (nxt.getD (cmIdx 0 0 (i / 4) (X + i / 2 % 2) (L + i % 2) X L) z)
      z >>= fun t1 ↦
    g2Mul (cmSel z ws 0 1 (0 + 1 + i / 4))
      (nxt.getD (cmIdx 0 1 (i / 4) (X + i / 2 % 2) (L + i % 2) X L) z) t1 >>= fun t2 ↦
    g2Mul (cmSel z ws 1 0 (1 + 0 + i / 4))
      (nxt.getD (cmIdx 1 0 (i / 4) (X + i / 2 % 2) (L + i % 2) X L) z) t2 >>= fun t3 ↦
    g2Mul (cmSel z ws 1 1 (1 + 1 + i / 4))
      (nxt.getD (cmIdx 1 1 (i / 4) (X + i / 2 % 2) (L + i % 2) X L) z) t3

/-- **One level** (one instance per coordinate of `Y`): the eight branch weights, then 72 entries. -/
def cmLevelG (z one : C2) (ρc lc : List C2) (y : C2) (X L : ℕ) (nxt : List C2) : BM (List C2) :=
  cmHdC one ρc >>= fun hr ↦ cmHdC one lc >>= fun hl ↦ g2One y >>= fun y1 ↦
    g2Mul hr.1 hl.1 z >>= fun u00 ↦ g2Mul hr.1 hl.2 z >>= fun u01 ↦
    g2Mul hr.2 hl.1 z >>= fun u10 ↦ g2Mul hr.2 hl.2 z >>= fun u11 ↦
    g2Mul u00 y1 z >>= fun w000 ↦ g2Mul u00 y z >>= fun w001 ↦
    g2Mul u01 y1 z >>= fun w010 ↦ g2Mul u01 y z >>= fun w011 ↦
    g2Mul u10 y1 z >>= fun w100 ↦ g2Mul u10 y z >>= fun w101 ↦
    g2Mul u11 y1 z >>= fun w110 ↦ g2Mul u11 y z >>= fun w111 ↦
    mapB (cmEntryG z [(w000, w001), (w010, w011), (w100, w101), (w110, w111)] nxt X L)
      (List.range 72)

theorem hs_cmLevelG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (ρc lc : List C2) (y : C2)
    (X L : ℕ) (nxt : List C2) (Y : List E2)
    (hn : nxt.map (ev2 M) = (List.range 72).map
      (cmTab (ρc.map (ev2 M)).tail (lc.map (ev2 M)).tail Y (X / 2) (L / 2))) :
    Hs c M (cmLevelG z one ρc lc y X L nxt) fun t ↦
      t.map (ev2 M) = (List.range 72).map (cmTab (ρc.map (ev2 M)) (lc.map (ev2 M)) (ev2 M y :: Y) X L) := by
  have z0 := ev2_of_zero hz
  refine hs_bind (hs_cmHdC hone ρc) fun hr hhr ↦ hs_bind (hs_cmHdC hone lc) fun hl hhl ↦
    hs_bind (hs_g2One y) fun y1 hy1 ↦
    hs_bind (hs_g2Mul _ _ z) fun u00 h00 ↦ hs_bind (hs_g2Mul _ _ z) fun u01 h01 ↦
    hs_bind (hs_g2Mul _ _ z) fun u10 h10 ↦ hs_bind (hs_g2Mul _ _ z) fun u11 h11 ↦
    hs_bind (hs_g2Mul _ _ z) fun w000 g000 ↦ hs_bind (hs_g2Mul _ _ z) fun w001 g001 ↦
    hs_bind (hs_g2Mul _ _ z) fun w010 g010 ↦ hs_bind (hs_g2Mul _ _ z) fun w011 g011 ↦
    hs_bind (hs_g2Mul _ _ z) fun w100 g100 ↦ hs_bind (hs_g2Mul _ _ z) fun w101 g101 ↦
    hs_bind (hs_g2Mul _ _ z) fun w110 g110 ↦ hs_bind (hs_g2Mul _ _ z) fun w111 g111 ↦ ?_
  set ρ := ρc.map (ev2 M)
  set lam := lc.map (ev2 M)
  have hy : ev2 M y1 = 1 + ev2 M y := ev2_onePlus hy1
  have hsel : ∀ a b k, a < 2 → b < 2 → ev2 M (cmSel z [(w000, w001), (w010, w011), (w100, w101),
      (w110, w111)] a b (a + b + k)) = cmW ρ lam (ev2 M y) k a b := by
    intro a b k ha hb
    unfold cmSel cmW
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    all_goals
      simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add, List.getD_cons_zero,
        List.getD_cons_succ]
      split_ifs
      all_goals
        first
        | rw [ev2_mul g001, ev2_mul h00, hhr.1, hhl.1, z0]; ring
        | rw [ev2_mul g000, ev2_mul h00, hhr.1, hhl.1, hy, z0]; ring
        | rw [ev2_mul g011, ev2_mul h01, hhr.1, hhl.2, z0]; ring
        | rw [ev2_mul g010, ev2_mul h01, hhr.1, hhl.2, hy, z0]; ring
        | rw [ev2_mul g101, ev2_mul h10, hhr.2, hhl.1, z0]; ring
        | rw [ev2_mul g100, ev2_mul h10, hhr.2, hhl.1, hy, z0]; ring
        | rw [ev2_mul g111, ev2_mul h11, hhr.2, hhl.2, z0]; ring
        | rw [ev2_mul g110, ev2_mul h11, hhr.2, hhl.2, hy, z0]; ring
  refine hs_mapB_eq (List.range 72) fun i hi ↦ ?_
  have hi' : i < 72 := List.mem_range.mp hi
  refine hs_bind (hs_g2Mul _ _ z) fun t1 h1 ↦ hs_bind (hs_g2Mul _ _ t1) fun t2 h2 ↦
    hs_bind (hs_g2Mul _ _ t2) fun t3 h3 ↦ hs_mono (hs_g2Mul _ _ t3) fun t4 h4 ↦ ?_
  rw [ev2_mul h4, ev2_mul h3, ev2_mul h2, ev2_mul h1, z0,
    hsel 0 0 _ (by norm_num) (by norm_num), hsel 0 1 _ (by norm_num) (by norm_num),
    hsel 1 0 _ (by norm_num) (by norm_num), hsel 1 1 _ (by norm_num) (by norm_num),
    ev2_getD_tab hn (cmIdx_lt (by norm_num) (by norm_num) hi') z,
    ev2_getD_tab hn (cmIdx_lt (by norm_num) (by norm_num) hi') z,
    ev2_getD_tab hn (cmIdx_lt (by norm_num) (by norm_num) hi') z,
    ev2_getD_tab hn (cmIdx_lt (by norm_num) (by norm_num) hi') z, cmTab_cons]
  ring

/-- **The tables** (recursion on `Y`'s cells): at `Y = []` the four products `ltS·ltS`. -/
def cmTabG (z one : C2) : List C2 → List C2 → List C2 → ℕ → ℕ → BM (List C2)
  | ρc, lc, [], X, L => fpG z ρc [] >>= fun fr ↦ fpG z lc [] >>= fun fl ↦
      ltG z one fr X >>= fun r0 ↦ ltG z one fr (X + 1) >>= fun r1 ↦
      ltG z one fl L >>= fun l0 ↦ ltG z one fl (L + 1) >>= fun l1 ↦
      g2Mul r0.1 l0.1 z >>= fun p00 ↦ g2Mul r0.1 l1.1 z >>= fun p01 ↦
      g2Mul r1.1 l0.1 z >>= fun p10 ↦ g2Mul r1.1 l1.1 z >>= fun p11 ↦
      pure ((List.range 72).map fun j ↦
        if j / 2 % 2 = 1 then (if j % 2 = 1 then p11 else p10) else (if j % 2 = 1 then p01 else p00))
  | ρc, lc, y :: Y, X, L => cmTabG z one ρc.tail lc.tail Y (X / 2) (L / 2) >>= fun nxt ↦
      cmLevelG z one ρc lc y X L nxt

theorem hs_cmTabG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) :
    ∀ (Yc ρc lc : List C2) (X L : ℕ), Hs c M (cmTabG z one ρc lc Yc X L) fun t ↦
      t.map (ev2 M) = (List.range 72).map (cmTab (ρc.map (ev2 M)) (lc.map (ev2 M)) (Yc.map (ev2 M)) X L)
  | [], ρc, lc, X, L => by
    have z0 := ev2_of_zero hz
    refine hs_bind (hs_fpG hz ρc []) fun fr hfr ↦ hs_bind (hs_fpG hz lc []) fun fl hfl ↦
      hs_bind (hs_ltG hz hone fr X) fun r0 hr0 ↦ hs_bind (hs_ltG hz hone fr (X + 1)) fun r1 hr1 ↦
      hs_bind (hs_ltG hz hone fl L) fun l0 hl0 ↦ hs_bind (hs_ltG hz hone fl (L + 1)) fun l1 hl1 ↦
      hs_bind (hs_g2Mul _ _ z) fun p00 g00 ↦ hs_bind (hs_g2Mul _ _ z) fun p01 g01 ↦
      hs_bind (hs_g2Mul _ _ z) fun p10 g10 ↦ hs_bind (hs_g2Mul _ _ z) fun p11 g11 ↦ hs_pure ?_
    rw [List.map_map]
    refine List.map_congr_left fun j _ ↦ ?_
    simp only [Function.comp_apply, cmTab, List.map_nil, cmF_nil]
    rw [hfr] at hr0 hr1
    rw [hfl] at hl0 hl1
    simp only [List.map_nil] at hr0 hr1 hl0 hl1
    split_ifs with h1 h2 h2
    · rw [ev2_mul g11, hr1.1, hl1.1, z0, add_zero, h1, h2]
    · rw [ev2_mul g10, hr1.1, hl0.1, z0, add_zero, h1, show j % 2 = 0 by omega, add_zero]
    · rw [ev2_mul g01, hr0.1, hl1.1, z0, add_zero, show j / 2 % 2 = 0 by omega, h2, add_zero]
    · rw [ev2_mul g00, hr0.1, hl0.1, z0, add_zero, show j / 2 % 2 = 0 by omega,
        show j % 2 = 0 by omega, add_zero, add_zero]
  | y :: Y, ρc, lc, X, L =>
    hs_bind (hs_cmTabG hz hone Y ρc.tail lc.tail (X / 2) (L / 2)) fun nxt hn ↦
      hs_cmLevelG hz hone ρc lc y X L nxt _ (by rw [hn, List.map_tail, List.map_tail])

/-! ## Claim 44 -/

/-- **Claim 44's weight in closed form on any shape**: the stream words `17x + ℓ` of `C_rec`'s window
`⟨r, 2^r·s⟩` (`x < X`, `17·X ≤ 2^r`) on a stack of `2^M` words: `eq(pt_{r..M}, s)·F(0, X, 17)` at
`Y = pt_{<r}`. -/
theorem cMW_eqG (M r s X : ℕ) (hX : 17 * X ≤ 2 ^ r) (lam ρ pt : List E2) :
    ∑ i ∈ Finset.range 17 ×ˢ Finset.range X, E2V.eqAtF lam i.1 * E2V.eqAtF ρ i.2 *
      eqPt (E2V.bitsF (17 * i.2 + i.1 + 2 ^ r * s) M) pt =
    E2V.eqAtF ((pt.take M).drop r) s * cmTab ρ lam ((pt.take M).take r) X 17 0 := by
  rw [show cmTab ρ lam ((pt.take M).take r) X 17 0 =
    cmF ρ lam ((pt.take M).take r) 0 X 17 from rfl, cmF, Finset.mul_sum, Finset.sum_product,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hx' := Finset.mem_range.mp hx
  have hl' := Finset.mem_range.mp hl
  have hlt : 17 * x + l < 2 ^ r := by omega
  rw [eqPt_comm, eqPt_bitsF, show 17 * x + l + 2 ^ r * s = 2 ^ r * s + (17 * x + l) by ring,
    eqAtF_aligned (m := r) (Nat.mul_mod_right _ _) hlt, Nat.mul_div_cancel_left _ (Nat.two_pow_pos r),
    add_zero]
  ring

/-- **Claim 44's weight in closed form** (`P17`): `eq(pt_{18..24}, 33)·F(0, 7168, 17)` at `Y = pt_{<18}`. -/
theorem cMW_eq (lam ρ pt : List E2) :
    ∑ i ∈ Finset.range 17 ×ˢ Finset.range 7168, E2V.eqAtF lam i.1 * E2V.eqAtF ρ i.2 *
      eqPt (E2V.bitsF (17 * i.2 + i.1 + 2 ^ 18 * 33) 24) pt =
    E2V.eqAtF ((pt.take 24).drop 18) 33 * cmTab ρ lam ((pt.take 24).take 18) 7168 17 0 :=
  cMW_eqG 24 18 33 7168 (by norm_num) lam ρ pt

theorem cM_weight (lk : SP.LinkOut) (pt : List E2) :
    (SP.cM lk).1 pt = E2V.eqAtF ((pt.take 24).drop 18) 33 *
      cmTab lk.2.1.1 (lk.1.drop 13) ((pt.take 24).take 18) 7168 17 0 := by
  rw [← cMW_eq]
  unfold SP.cM
  dsimp only

/-- **Claim 44's gadget on any shape** (one instance): the selector bits `s` on `M − r` bits, the tables over
`r` coordinates, `X` rows, entry `0`. -/
def cMGG (M r s X : ℕ) (lc ρc : List C2) (x : List C2) (gate : Cell) : BM C2 :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦
    eqAtG z one ((x.take M).drop r) s >>= fun sv ↦
      cmTabG z one ρc lc ((x.take M).take r) X 17 >>= fun t ↦ g2Mul sv (t.getD 0 z) z

/-- **Claim 44's gadget** (one instance, `P17`): the selector bits `33`, the tables, entry `0`. -/
def cMG (lc ρc : List C2) (x : List C2) (gate : Cell) : BM C2 :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦
    eqAtG z one ((x.take 24).drop 18) 33 >>= fun s ↦
      cmTabG z one ρc lc ((x.take 24).take 18) 7168 17 >>= fun t ↦ g2Mul s (t.getD 0 z) z

theorem cMG_eq_G : cMG = cMGG 24 18 33 7168 := rfl

/-- **Claim 44 on any shape**: the weight `Σ_{ℓ<17, x<X} eq(λ, ℓ)·eq(ρ', x)·[stack word 17x + ℓ + 2^r·s]` on
`2^M` words. -/
theorem cM_okG (M r s X : ℕ) (hX : 17 * X ≤ 2 ^ r) (Pre : Mem → Prop) (lam ρ : List E2) (v : E2)
    (lc ρc : List C2) (h : ∀ M, Pre M → lc.map (ev2 M) = lam ∧ ρc.map (ev2 M) = ρ) :
    ClaimAt Pre ((fun pt ↦ ∑ i ∈ Finset.range 17 ×ˢ Finset.range X, E2V.eqAtF lam i.1 * E2V.eqAtF ρ i.2 *
      eqPt (E2V.bitsF (17 * i.2 + i.1 + 2 ^ r * s) M) pt), v) (cMGG M r s X lc ρc) := by
  intro c Mm hP x gate _
  obtain ⟨hl, hr⟩ := h Mm hP
  refine hsA_of_hs (hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2Const 1 z) fun one hone ↦
    hs_bind (hs_eqAtG hz (ev2_one' hone) _ _) fun sv hs ↦
      hs_bind (hs_cmTabG hz (ev2_one' hone) _ ρc lc X 17) fun t ht ↦
        hs_mono (hs_g2Mul sv (t.getD 0 z) z) fun o ho ↦ ?_)
  show ev2 Mm o = ∑ i ∈ Finset.range 17 ×ˢ Finset.range X, E2V.eqAtF lam i.1 * E2V.eqAtF ρ i.2 *
      eqPt (E2V.bitsF (17 * i.2 + i.1 + 2 ^ r * s) M) (x.map (ev2 Mm))
  rw [cMW_eqG M r s X hX, ev2_mul ho, ev2_of_zero hz, add_zero, hs, ev2_getD_tab ht (by norm_num) z, hl, hr]
  simp only [List.map_take, List.map_drop]

/-- **Claim 44** (`Σ_{ℓ<17, x<7168} eq(λ, ℓ)·eq(ρ', x)·[stream word 17x + ℓ]`): `λ`, `ρ'` as cells. -/
theorem cM_ok (Pre : Mem → Prop) (lk : SP.LinkOut) (lc ρc : List C2)
    (h : ∀ M, Pre M → lc.map (ev2 M) = lk.1.drop 13 ∧ ρc.map (ev2 M) = lk.2.1.1) :
    ClaimAt Pre (SP.cM lk) (cMG lc ρc) :=
  cM_okG 24 18 33 7168 (by norm_num) Pre _ _ _ lc ρc h

end Lvm6.QC
