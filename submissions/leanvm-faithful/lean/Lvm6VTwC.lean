-- New for lvm6 (WP V1c): claim 44 in closed form (WP CLG's carry recursion `cmF_cons`/`cmTab_cons`, copied from
-- `Lvm6QCFinM` (CLG b6702608) without its gadgets), its word-field table `cmTabF` (`cmTabF_spec`), the sponge phase's
-- claims as fast claims, the fast sponge phase (SPH's `spongePhase6`), and the fast commitment phase `commit6`.
import Lvm6VTwX
import Lvm6VTwO
import Lvm6SpProg

/-!
# Claim 44, the sponge phase and the commitment, in the word field

* CLG's recursion (`cmF`, `cmF_cons`, `cmTab`, `cmTab_cons`, `cmIdx_lt`); `eqPt_bitsF'`, `eqAtF_aligned'`,
  **`cMW_eq'`** (the weight of claim 44 is `eq(pt₁₉…₂₄, 33)·cmTab … 0`).
* `cmTabF` (one level: eight branch weights, 72 entries of four products), **`cmTabF_spec`**.
* `spSF` (the sponge phase's slices and claims 16–45 as `FClaim`s), **`spSF_dec`**; **`fSpongePhase6`**,
  **`tw_spongePhase6`**; `PhF` (a phase's slices and claims), `PhF.dec`.
* **`fCommit6`**, **`tw_commit6`**.
-/

set_option autoImplicit false

namespace Lvm6.V.C44

open LeanVM.Parameters Lvm Lvm6


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



end Lvm6.V.C44

namespace Lvm6.V.C44

open LeanVM.Parameters Lvm Lvm6

theorem two_E2' : (2 : E2) = 0 := CharTwo.two_eq_zero

theorem eqPt_cons' (a b : E2) (x y : List E2) : eqPt (a :: x) (b :: y) = (1 + a + b) * eqPt x y := by
  unfold eqPt
  rw [List.zipWith_cons_cons, List.prod_cons]
  linear_combination (a * b * (List.zipWith (fun r t ↦ r * t + (1 + r) * (1 + t)) x y).prod) * two_E2'

theorem eqPt_bitsF' : ∀ (y : List E2) (w n : ℕ), eqPt (E2V.bitsF w n) y = E2V.eqAtF (y.take n) w
  | _, _, 0 => by simp [E2V.bitsF, eqPt]
  | [], _, _ + 1 => by simp [E2V.bitsF, eqPt]
  | y0 :: y, w, n + 1 => by
    rw [E2V.bitsF, eqPt_cons', eqPt_bitsF' y (w / 2) n, List.take_succ_cons, E2V.eqAtF_succ]
    split_ifs
    · linear_combination (E2V.eqAtF (y.take n) (w / 2)) * two_E2'
    · ring

theorem eqAtF_aligned' (m a i : ℕ) (hi : i < 2 ^ m) (X : List E2) :
    E2V.eqAtF X (2 ^ m * a + i) = E2V.eqAtF (X.take m) i * E2V.eqAtF (X.drop m) a := by
  by_cases h : m ≤ X.length
  · have ht : (X.take m).length = m := by simp [h]
    conv_lhs => rw [← List.take_append_drop m X]
    rw [E2V.eqAtF_append, ht, E2V.eqAtF_mod (X.take m) (2 ^ m * a + i), ht,
      show (2 ^ m * a + i) % 2 ^ m = i by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi],
      show (2 ^ m * a + i) / 2 ^ m = a by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hi, Nat.zero_add]]
  · have hl : X.length ≤ m := by omega
    rw [List.take_of_length_le hl, List.drop_eq_nil_of_le hl,
      show E2V.eqAtF ([] : List E2) a = 1 from rfl, mul_one, E2V.eqAtF_mod X (2 ^ m * a + i),
      E2V.eqAtF_mod X i]
    congr 1
    obtain ⟨k, hk⟩ : 2 ^ X.length ∣ 2 ^ m := Nat.pow_dvd_pow 2 hl
    rw [hk, mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_left]

/-- **Claim 44's weight in closed form** (CLG's `cMW_eq`). -/
theorem cMW_eq' (lam ρ pt : List E2) :
    ∑ i ∈ Finset.range 17 ×ˢ Finset.range 7168, E2V.eqAtF lam i.1 * E2V.eqAtF ρ i.2 *
      eqPt (E2V.bitsF (17 * i.2 + i.1 + 2 ^ 19 * 33) 25) pt =
    E2V.eqAtF ((pt.take 25).drop 19) 33 * cmTab ρ lam ((pt.take 25).take 19) 7168 17 0 := by
  rw [show cmTab ρ lam ((pt.take 25).take 19) 7168 17 0 =
    cmF ρ lam ((pt.take 25).take 19) 0 7168 17 from rfl, cmF, Finset.mul_sum, Finset.sum_product,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hx' := Finset.mem_range.mp hx
  have hl' := Finset.mem_range.mp hl
  rw [eqPt_bitsF', show 17 * x + l + 2 ^ 19 * 33 = 2 ^ 19 * 33 + (17 * x + l) by ring,
    eqAtF_aligned' 19 33 (17 * x + l) (by norm_num; omega), add_zero]
  ring

theorem cM_weight' (lk : SP.LinkOut) (pt : List E2) :
    (SP.cM lk).1 pt = E2V.eqAtF ((pt.take 25).drop 19) 33 *
      cmTab lk.2.1.1 (lk.1.drop 13) ((pt.take 25).take 19) 7168 17 0 := by
  rw [← cMW_eq']
  unfold SP.cM
  dsimp only

theorem cmW_mod (ρ lam : List E2) (y : E2) (c a b : ℕ) : cmW ρ lam y c a b = cmW ρ lam y (c % 2) a b := by
  unfold cmW
  rw [show (a + b + c % 2) % 2 = (a + b + c) % 2 by omega]

end Lvm6.V.C44

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Finset

/-! ## Claim 44 in the word field -/

theorem ofFn_getD {n : ℕ} (f : Fin n → FE2) {i : ℕ} (h : i < n) : (Array.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- `cmHd` in the word field. -/
def cmHdF : List FE2 → ℕ → FE2
  | [], _ => 1
  | r :: _, a => if a = 1 then r else 1 + r

theorem toE2_cmHdF (ρ : List FE2) (a : ℕ) : FE2.toE2 (cmHdF ρ a) = C44.cmHd (ρ.map FE2.toE2) a := by
  cases ρ with
  | nil => exact toE2_one'
  | cons r rs =>
    simp only [cmHdF, C44.cmHd, List.map_cons]
    split_ifs
    · rfl
    · exact (toE2_add' 1 r).trans (by rw [toE2_one'])

/-- `cmW` in the word field. -/
def cmWF (ρ lam : List FE2) (y : FE2) (c a b : ℕ) : FE2 :=
  cmHdF ρ a * cmHdF lam b * (if (a + b + c) % 2 = 1 then y else 1 + y)

theorem toE2_cmWF (ρ lam : List FE2) (y : FE2) (c a b : ℕ) :
    FE2.toE2 (cmWF ρ lam y c a b) = C44.cmW (ρ.map FE2.toE2) (lam.map FE2.toE2) (FE2.toE2 y) c a b := by
  unfold cmWF C44.cmW
  rw [toE2_mul', toE2_mul', toE2_cmHdF, toE2_cmHdF]
  split_ifs
  · rfl
  · rw [toE2_add', toE2_one']

/-- The last level: `(Σ_{x<X} eq(ρ, x))·(Σ_{ℓ<L} eq(λ, ℓ))`. -/
def cmBaseF (ρ lam : List FE2) (X L : ℕ) : FE2 :=
  (∑ x ∈ range X, eqAtF ρ x) * ∑ l ∈ range L, eqAtF lam l

/-- **CLG's level tables in the word field**: per level eight branch weights, then 72 entries of four products. -/
def cmTabF (ρ lam : List FE2) : List FE2 → ℕ → ℕ → Array FE2
  | [], X, L => Array.ofFn (n := 72) fun j => cmBaseF ρ lam (X + j.1 / 2 % 2) (L + j.1 % 2)
  | y :: Y, X, L =>
    let nxt := cmTabF ρ.tail lam.tail Y (X / 2) (L / 2)
    let ws : Array FE2 := Array.ofFn (n := 8) fun k => cmWF ρ lam y (k.1 / 4) (k.1 / 2 % 2) (k.1 % 2)
    Array.ofFn (n := 72) fun i =>
      let p := i.1 / 4 % 2
      let X' := X + i.1 / 2 % 2
      let L' := L + i.1 % 2
      ws.getD (4 * p + 0) 0 * nxt.getD (C44.cmIdx 0 0 (i.1 / 4) X' L' X L) 0 +
        ws.getD (4 * p + 1) 0 * nxt.getD (C44.cmIdx 0 1 (i.1 / 4) X' L' X L) 0 +
        (ws.getD (4 * p + 2) 0 * nxt.getD (C44.cmIdx 1 0 (i.1 / 4) X' L' X L) 0 +
        ws.getD (4 * p + 3) 0 * nxt.getD (C44.cmIdx 1 1 (i.1 / 4) X' L' X L) 0)

theorem ws_getD (ρ lam : List FE2) (y : FE2) (p a b : ℕ) (hp : p < 2) (ha : a < 2) (hb : b < 2) :
    (Array.ofFn (n := 8) fun k : Fin 8 => cmWF ρ lam y (k.1 / 4) (k.1 / 2 % 2) (k.1 % 2)).getD (4 * p + (2 * a + b)) 0 =
      cmWF ρ lam y p a b := by
  rw [ofFn_getD _ (by omega)]
  dsimp only
  rw [show (4 * p + (2 * a + b)) / 4 = p by omega, show (4 * p + (2 * a + b)) / 2 % 2 = a by omega,
    show (4 * p + (2 * a + b)) % 2 = b by omega]

theorem cmTabF_spec : ∀ (Y ρ lam : List FE2) (X L i : ℕ), i < 72 →
    FE2.toE2 ((cmTabF ρ lam Y X L).getD i 0) =
      C44.cmTab (ρ.map FE2.toE2) (lam.map FE2.toE2) (Y.map FE2.toE2) X L i
  | [], ρ, lam, X, L, i, hi => by
    rw [cmTabF, ofFn_getD _ hi]
    show FE2.toE2 (cmBaseF ρ lam _ _) = C44.cmF _ _ [] (i / 4) _ _
    unfold cmBaseF C44.cmF
    rw [toE2_mul', ← coe_tE, map_sum, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_eqAtF, map_eqAtF, show E2V.eqAtF ([] : List E2) (17 * x + l + i / 4) = 1 from rfl, mul_one]
  | y :: Y, ρ, lam, X, L, i, hi => by
    simp only [cmTabF]
    rw [ofFn_getD _ hi]
    dsimp only
    rw [List.map_cons, C44.cmTab_cons]
    have hp : i / 4 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have e := fun (a b : ℕ) (ha : a < 2) (hb : b < 2) =>
      (ws_getD ρ lam y (i / 4 % 2) a b hp ha hb)
    have t := fun (a b : ℕ) (ha : a < 2) (hb : b < 2) =>
      cmTabF_spec Y ρ.tail lam.tail (X / 2) (L / 2) _ (C44.cmIdx_lt (X := X) (L := L) ha hb hi)
    rw [show (4 * (i / 4 % 2) + 0) = 4 * (i / 4 % 2) + (2 * 0 + 0) from rfl,
      show (4 * (i / 4 % 2) + 1) = 4 * (i / 4 % 2) + (2 * 0 + 1) from rfl,
      show (4 * (i / 4 % 2) + 2) = 4 * (i / 4 % 2) + (2 * 1 + 0) from rfl,
      show (4 * (i / 4 % 2) + 3) = 4 * (i / 4 % 2) + (2 * 1 + 1) from rfl,
      e 0 0 (by norm_num) (by norm_num), e 0 1 (by norm_num) (by norm_num), e 1 0 (by norm_num) (by norm_num),
      e 1 1 (by norm_num) (by norm_num)]
    simp only [toE2_add', toE2_mul', toE2_cmWF, t 0 0 (by norm_num) (by norm_num), t 0 1 (by norm_num) (by norm_num),
      t 1 0 (by norm_num) (by norm_num), t 1 1 (by norm_num) (by norm_num), List.map_tail]
    rw [← C44.cmW_mod, ← C44.cmW_mod, ← C44.cmW_mod, ← C44.cmW_mod]

/-- **Claim 44 as a fast claim** (`ρ'`, `λ`, value). -/
def cMF (ρ' lam : List FE2) (v : FE2) : FClaim :=
  ⟨fun x => eqAtF ((x.take 25).drop 19) 33 * (cmTabF ρ' lam ((x.take 25).take 19) 7168 17).getD 0 0, v⟩

/-! ## The sponge phase's claims -/

/-- A fast link output and its value. -/
abbrev LkF : Type := List FE2 × (List FE2 × FE2) × List FE2

/-- A lane-sum claim `Σ_{ℓ<n} eq(λ, ℓ)·eq(p ++ bits(base + ℓ, w), ·)`. -/
def laneSF (lam p : List FE2) (base n w : ℕ) (v : FE2) : FClaim :=
  ⟨fun x => ∑ l ∈ range n, eqAtF lam l * eqPtF (p ++ bitsF (base + l) w) x, v⟩

theorem laneSF_dec (lam p : List FE2) (base n w : ℕ) (v : FE2) :
    (laneSF lam p base n w v).dec = (fun pt => ∑ l ∈ range n, eqAtF (lam.map FE2.toE2) l *
      eqPt (p.map FE2.toE2 ++ bitsF (base + l) w) pt, FE2.toE2 v) := by
  simp only [FClaim.dec, laneSF]
  congr 1
  funext x
  rw [← coe_tE, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_eqAtF, coe_tE, toE2_eqPtF, map_toE2_ofE2, List.map_append, ← coe_tE, map_bitsF tE]

theorem cMF_dec (lk : LkF) : (cMF lk.2.1.1 (lk.1.drop 13) (lk.2.2.getD 2 0)).dec = SP.cM (lkD lk) := by
  simp only [FClaim.dec, cMF]
  refine Prod.ext (funext fun x => ?_) (toE2_getD _ _)
  dsimp only
  rw [C44.cM_weight', toE2_mul', toE2_eqAtF, cmTabF_spec _ _ _ _ _ _ (by norm_num)]
  simp only [List.map_drop, List.map_take, map_toE2_ofE2, lkD, scD]

/-- A phase's output in the word field: the slices and the claims. -/
abbrev PhF : Type := SliceF × List FClaim

/-- Its value in `E2` (WP S's `TreeOut`). -/
def PhF.dec (p : PhF) : Lvm6.TreeOut := ⟨p.1.dec, p.2.map FClaim.dec⟩

/-- The tree phase's output as a `PhF`. -/
def treePhF (t : TreeSF) : PhF := (⟨t.pt, t.s⟩, t.cols.map pcF)

theorem treePhF_dec (t : TreeSF) : PhF.dec (treePhF t) = t.dec := by
  simp only [PhF.dec, treePhF, TreeSF.dec, SliceF.dec, List.map_map, Function.comp_def, pcF_dec]

/-- **The sponge phase's output** (SPH's `spS`) in the word field. -/
def spSF (o : List FE2 × List FE2 × (HeadOutF × EndOutF)) (lk : LkF) : PhF :=
  (⟨o.2.2.2.pt ++ bitsF 35 6, o.2.2.2.s⟩,
    pcF (o.1 ++ o.2.2.1.ϱm ++ bitsF 35 6, o.2.2.1.cout) ::
      ((List.range 25).map (fun l => pcF (o.1 ++ bitsF (36 * 64 + l) 12, o.2.1.getD l 0)) ++
        [laneSF (lk.1.drop 13) lk.2.1.1 (36 * 64) 25 12 (lk.2.2.getD 0 0),
          laneSF (lk.1.drop 13) lk.2.1.1 (35 * 64) 25 12 (lk.2.2.getD 1 0),
          cMF lk.2.1.1 (lk.1.drop 13) (lk.2.2.getD 2 0),
          laneSF (lk.1.drop 13) (lk.2.1.1.take 10) (37 * 2 ^ 9) 17 15 (lk.2.2.getD 3 0)]))

theorem spSF_dec (o : List FE2 × List FE2 × (HeadOutF × EndOutF)) (lk : LkF) :
    PhF.dec (spSF o lk) = SP.spS (spD o) (lkD lk) := by
  simp only [PhF.dec, spSF, SP.spS, SliceF.dec, List.map_cons, List.map_append, List.map_map, Function.comp_def,
    List.map_nil, pcF_dec, pcDec, laneSF_dec, cMF_dec, SP.cOut, SP.cTied, SP.cY, SP.cIn, SP.cX, spD, coreD, lkD, scD,
    HeadOutF.dec, EndOutF.dec, toE2_getD, List.map_drop, List.map_take, ← coe_tE, map_bitsF tE, map_getD]
  all_goals rfl

/-- **Fast `spongePhase6 sh`** (SPH). -/
def fSpongePhase6 (sh : Lvm6.Shape) : VF PhF :=
  if SP.SpShapeOK sh then
    VF.bind (fSpCaller6 13) fun o => VF.bind (fKsLink 13 10 SP.contRows6) fun lk => VF.pure (spSF o lk)
  else fun _ _ => none

theorem tw_spongePhase6 (sh : Lvm6.Shape) (x : Lvm6.Hdr) :
    TwinF PhF.dec (SP.spongePhase6 sh x) (fSpongePhase6 sh) := by
  unfold SP.spongePhase6 fSpongePhase6 SP.spongeBody
  split
  · exact tw_bind (tw_spCaller6 13) fun o => tw_bind (tw_ksLink 13 10 SP.contRows6) fun lk =>
      tw_pure (spSF_dec o lk)
  · intro π tr
    rw [replayP_fail]
    exact Option.Rel.none

/-! ## The commitment phase -/

/-- **Fast `commit6 sh`** (§6.1). -/
def fCommit6 (sh : Lvm6.Shape) : VF FClaim :=
  VF.bind (fCommit (sh.levs.getD 0 default).ht (sh.levs.getD 0 default).wd) fun _ =>
  VF.bind (VF.bind fSample fun _ => VF.pure ()) fun _ =>
  VF.bind (fGrp (sh.lvl 0).gOod (sh.M - 1)) fun z =>
  VF.bind fReadF fun y => VF.pure (pcF (z, y))

theorem tw_commit6 (sh : Lvm6.Shape) : TwinF FClaim.dec (Lvm6.commit6 sh) (fCommit6 sh) := by
  unfold Lvm6.commit6
  refine tw_bind (tw_commit _ _) fun _ => ?_
  refine tw_bind (d := fun _ => ()) (tw_sample fun _ => tw_pure rfl) fun _ => ?_
  refine tw_bind (tw_grp _ _ : TwinF _ (grp6 _ _) _) fun z => tw_bind tw_e2Read fun y => tw_pure ?_
  exact pcF_dec (z, y)

end Lvm6.V
