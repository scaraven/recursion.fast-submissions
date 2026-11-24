-- New for lvm6 K1: row 10 of `FORMAT6.md` §6.2 (`treeEnd6`, BLUEPRINT §2.3 step 6) in the doom calculus:
-- the constants off the claim, 11 plain rounds (4 low row bits, the top row bit, 6 slot bits), 64 slices,
-- the final check with the byte-shifted weights `pw^P`, `pw^L` and the middle state's `pw^M`.
import Lvm6KHead
import Lvm6KBits

/-!
# The tree batch's input end

`κ = P + 4` row bits; row `x = i + 16·y + 2^(P+3)·t` (`i` the instance bits, `y` the middle pack
bits, `t` the top row bit: `0` on the parent rows, `1` on the leaf rows); `cb q z y` is bit `z` of
the stack's word `y`.

* the claim at depth 12 on the tree inputs `Itree`: `Gs_zero` (segment 0: the constant `C^t` plus
  the slot bits under `pw^t`, from `wsum_node`/`wsum_item`), `Gs_one` (segment 1: slots `8 … 32`
  under `pw^M`), **`claimSum_tree`** (the claim's sum is the constants' share plus `Tsum`);
* the sumcheck family `FeF` over `n = i + 16·t + 32·o` (`aE` the weights, `bE` the slices with the
  middle pack bits bound to `r_mid`): `FeF_plain`, **`FeF_nil`** (`= Tsum`),
  **`claimTrue_of_treeV'`** (`value' = FeF []` gives the claim);
* at the last point `ϱ`: **`aE_full`** (the verifier's `μ̃ · treeWt`), **`bE_full`** (slice `z` at
  the slice point), **`final_tree`** (true slices and the check give `FeF ϱ`);
* **`treeEndSpec`**: `treeEnd6 P claim` from doom of the claim at depth 12 on `Itree (P + 4) (stk q)`
  to doom of the 64 slice claims at the slice point. Lead `0`; the follower's `T` after the slices.
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (States Shape statesOfS laneWord segStateS sbit)
open Lvm.E2V Lvm6.KPack
open Lvm.ASM (εS)
open Finset
open scoped ENNReal

/-! ## The tree inputs' bits -/

/-- Bit `z` of the stack's word `y`, in `E2`. -/
def cb (q : Stack) (z y : ℕ) : E2 := bitF ((q y).toBitVec.getLsbD z)

/-- The byte shift's pull-back is `w_{64o+z+8}` in both branches (`z < 64`). -/
theorem shW_eq (w : List E2) (o : ℕ) {z : ℕ} (hz : z < 64) : shW w o z = w.getD (64 * o + z + 8) 0 := by
  unfold shW
  split_ifs with h
  · rfl
  · congr 1; omega

theorem K_lane_toBitVec (a : K) : (K.lane a).toBitVec = a.toBitVec := rfl

/-- The input-map weight of the top half `t` (`pw^P` for `t = 0`, `pw^L` for `t = 1`). -/
def pwT (w : List E2) (t o z : ℕ) : E2 := if t = 0 then pwP w o z else pwL w o z

theorem pwT_zero (w : List E2) : pwT w 0 = pwP w := by funext o z; simp [pwT]
theorem pwT_one (w : List E2) : pwT w 1 = pwL w := by funext o z; simp [pwT]

/-- The input constant of the top half `t`. -/
def cT (w : List E2) (t : ℕ) : E2 := if t = 0 then cW w cPbits else cW w cLbits

/-- The weighted input bits of row `x` on segment `m`. -/
def Gs (κ : ℕ) (q : Stack) (w : List E2) (m x : ℕ) : E2 :=
  ∑ j ∈ range 1600, w.getD j 0 * bitF (sbit (Itree κ q m x) j)

/-- A sum over the 64 slots of a function supported below `n`. -/
theorem sum_pad {n : ℕ} (hn : n ≤ 64) (f : ℕ → E2) (g : ℕ → E2) (hg : ∀ o, g o = if o < n then f o else 0) :
    ∑ o ∈ range 64, g o = ∑ o ∈ range n, f o := by
  obtain ⟨m, hm⟩ : ∃ m, 64 = n + m := ⟨64 - n, by omega⟩
  rw [hm, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := range m) fun o _ ↦ by rw [hg, ite_eq_right (by omega)], add_zero]
  exact Finset.sum_congr rfl fun o ho ↦ by rw [hg, ite_eq_left (Finset.mem_range.1 ho)]

/-- **Segment 0** (the input map): the constant `C^t` plus the slot bits under `pw^t`
(`wsum_node` on the parent rows, `wsum_item` on the leaf rows). -/
theorem Gs_zero (P : ℕ) (q : Stack) (w : List E2) (x : ℕ) :
    Gs (P + 4) q w 0 x = cT w (if x < 2 ^ (P + 3) then 0 else 1) +
      ∑ o ∈ range 64, ∑ z ∈ range 64, pwT w (if x < 2 ^ (P + 3) then 0 else 1) o z *
        cb q z (x + 2 ^ (P + 4) * o) := by
  have hI : Itree (P + 4) q 0 x = inTree (P + 4) q x := ite_eq_left rfl
  rw [Gs, hI, inTree, show P + 4 - 1 = P + 3 by omega]
  by_cases hx : x < 2 ^ (P + 3)
  · rw [ite_eq_left hx, ite_eq_left hx, cT, pwT_zero, ite_eq_left rfl]
    have e : wordsAt (P + 4) q x 4 = fun m ↦ wordsAt (P + 4) q x 0 (4 + m) := by
      funext m; simp only [wordsAt, zero_add]
    rw [e]
    refine (wsum_node w (wordsAt (P + 4) q x 0)).trans (congrArg (cW w cPbits + ·) ?_)
    refine (sum_pad (by norm_num) _ _ fun o ↦ ?_).symm
    unfold pwP
    split_ifs with ho
    · refine Finset.sum_congr rfl fun z hz ↦ ?_
      rw [shW_eq _ _ (Finset.mem_range.1 hz)]
      simp only [cb, wordsAt, zero_add]
      rfl
    · simp
  · rw [ite_eq_right hx, ite_eq_right hx, cT, pwT_one, ite_eq_right one_ne_zero]
    refine (wsum_item w (wordsAt (P + 4) q x 0)).trans (congrArg (cW w cLbits + ·) ?_)
    refine (sum_pad (by norm_num) _ _ fun o ↦ ?_).symm
    unfold pwL
    split_ifs with ho
    · refine Finset.sum_congr rfl fun z hz ↦ ?_
      rw [shW_eq _ _ (Finset.mem_range.1 hz)]
      simp only [cb, wordsAt, zero_add]
      rfl
    · simp

/-- **Segment 1** (the committed middle state): slots `8 … 32` under `pw^M`. -/
theorem Gs_one (κ : ℕ) (q : Stack) (w : List E2) (x : ℕ) :
    Gs κ q w 1 x = ∑ o ∈ range 64, ∑ z ∈ range 64, pwM w o z * cb q z (x + 2 ^ κ * o) := by
  rw [Gs, show 1600 = 25 * 64 from rfl, sum_range_mulK 25 64]
  have e : ∀ l ∈ range 25, ∑ z ∈ range 64, w.getD (64 * l + z) 0 * bitF (sbit (Itree κ q 1 x) (64 * l + z)) =
      ∑ z ∈ range 64, pwM w (8 + l) z * cb q z (x + 2 ^ κ * (8 + l)) := by
    intro l hl
    have hl' := Finset.mem_range.1 hl
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    have hz' := Finset.mem_range.1 hz
    rw [pwM, ite_eq_left (by omega), sbit, show (64 * l + z) / 64 = l by omega,
      show (64 * l + z) % 64 = z by omega, show 8 + l - 8 = l by omega]
    have hw := laneWord_Itree_one κ q x hl'
    have hl2 : Keccak.lane (Itree κ q 1 x) l = K.lane (q (x + 2 ^ κ * (8 + l))) := by
      rw [← hw, laneWord, Lvm.KG.lane_ofLane']
    rw [hl2, K_lane_toBitVec]
    rfl
  rw [Finset.sum_congr rfl e]
  rw [show 64 = 8 + (25 + 31) from rfl, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ o ∈ range 8, ∑ z ∈ range 64, pwM w o z * cb q z (x + 2 ^ κ * o) = 0 :=
    Finset.sum_eq_zero fun o ho ↦ Finset.sum_eq_zero fun z _ ↦ by
      rw [pwM, ite_eq_right (by have := Finset.mem_range.1 ho; omega), zero_mul]
  have h3 : ∑ o ∈ range 31, ∑ z ∈ range 64, pwM w (8 + (25 + o)) z * cb q z (x + 2 ^ κ * (8 + (25 + o))) = 0 :=
    Finset.sum_eq_zero fun o _ ↦ Finset.sum_eq_zero fun z _ ↦ by
      rw [pwM, ite_eq_right (by omega), zero_mul]
  rw [h1, h3, zero_add, add_zero]

/-! ## Sums -/

theorem list_sum_getD : ∀ l : List E2, l.sum = ∑ i ∈ range l.length, l.getD i 0
  | [] => by simp
  | a :: l => by
    rw [List.sum_cons, List.length_cons, Finset.sum_range_succ', list_sum_getD l]
    simp [add_comm]

/-- A point `a ++ [e] ++ s` splits the index into `x + 2^α·t + 2^(α+1)·o`. -/
theorem split3 {α : ℕ} (a : List E2) (ha : a.length = α) (e : E2) (s : List E2) (G : ℕ → E2) :
    ∑ n ∈ range (2 ^ (α + 1 + s.length)), eqAtF (a ++ [e] ++ s) n * G n =
      ∑ o ∈ range (2 ^ s.length), eqAtF s o * ∑ t ∈ range 2, eqAtF [e] t *
        ∑ x ∈ range (2 ^ α), eqAtF a x * G (x + 2 ^ α * t + 2 ^ (α + 1) * o) := by
  have h1 : (a ++ [e]).length = α + 1 := by simp [ha]
  rw [col_splitF h1]
  refine Finset.sum_congr rfl fun o _ ↦ congrArg _ ?_
  exact col_splitF (s := [e]) ha (fun x ↦ G (x + 2 ^ (α + 1) * o))

theorem sum_two (f : ℕ → E2) : ∑ t ∈ range 2, f t = f 0 + f 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]

theorem eq1_zero (r : E2) : eqAtF [r] 0 = 1 + r := by simp [eqAtF]
theorem eq1_one (r : E2) : eqAtF [r] 1 = r := by simp [eqAtF]

/-! ## The claim side -/

/-- The top-half bit of row `x` (`0` on the parent rows `x < 2^(κ−1)`, `1` on the leaf rows). -/
def tOf (P x : ℕ) : ℕ := if x < 2 ^ (P + 3) then 0 else 1

/-- The weight of slot `o`, bit `z`, on the top half `t`, the two segments folded by `r'_seg`. -/
def wtX (rs : E2) (w : List E2) (t o z : ℕ) : E2 := (1 + rs) * pwT w t o z + rs * pwM w o z

/-- Row `x`'s slot bits weighted by `wtX`. -/
def Hx (P : ℕ) (q : Stack) (rs : E2) (w : List E2) (t x : ℕ) : E2 :=
  ∑ o ∈ range 64, ∑ z ∈ range 64, wtX rs w t o z * cb q z (x + 2 ^ (P + 4) * o)

/-- The two segments folded by `r'_seg`: the constants' share plus `Hx`. -/
theorem Gs_comb (P : ℕ) (q : Stack) (rs : E2) (w : List E2) (x : ℕ) :
    (1 + rs) * Gs (P + 4) q w 0 x + rs * Gs (P + 4) q w 1 x =
      (1 + rs) * cT w (tOf P x) + Hx P q rs w (tOf P x) x := by
  rw [Gs_zero, Gs_one, Hx, tOf]
  simp only [wtX, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_assoc]
  ring

/-- The claim's sum without the constants, over `(t, y, i)` (`x = i + 16·y + 2^(P+3)·t`). -/
def Tsum (P : ℕ) (q : Stack) (rm : List E2) (rt rs : E2) (mu w : List E2) : E2 :=
  ∑ t ∈ range 2, eqAtF [rt] t * ∑ y ∈ range (2 ^ (P - 1)), eqAtF rm y *
    ∑ i ∈ range 16, mu.getD i 0 * Hx P q rs w t (i + 16 * y + 2 ^ (P + 3) * t)

theorem idx_split {P y t m : ℕ} (hy : y < 2 ^ P) (ht : t < 2) :
    (y + 2 ^ P * t + 2 ^ (P + 1) * m) / 2 ^ (P + 1) = m ∧
      (y + 2 ^ P * t + 2 ^ (P + 1) * m) % 2 ^ (P + 1) = y + 2 ^ P * t := by
  have hlt : y + 2 ^ P * t < 2 ^ (P + 1) := by
    rw [pow_succ]; interval_cases t <;> omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem tOf_idx {P i y t : ℕ} (hi : i < 16) (hy : y < 2 ^ P) (ht : t < 2) :
    tOf (P + 1) (i + 16 * y + 2 ^ (P + 1 + 3) * t) = t := by
  have e : 2 ^ (P + 1 + 3) = 16 * 2 ^ P := by rw [show P + 1 + 3 = 4 + P by ring, pow_add]; rfl
  rw [tOf, e]
  interval_cases t
  · rw [ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega)]

/-- **The claim at depth 12 on the tree inputs**: the constants' share plus `Tsum`. -/
theorem claimSum_tree {P : ℕ} (q : Stack) (rm : List E2) (hrm : rm.length = P) (rt rs : E2)
    {mu : List E2} (hmu : mu.length = 16) (w : List E2) :
    claimSumF (statesOfS Shape.v1 (P + 1) (Itree (P + 1 + 4) q) 12) (P + 1) (rm ++ [rt] ++ [rs]) mu w =
      (1 + rs) * mu.sum * ((1 + rt) * cW w cPbits + rt * cW w cLbits) +
        Tsum (P + 1) q rm rt rs mu w := by
  have hs := split3 rm hrm rt [rs] (fun z ↦ ∑ i ∈ range 16, mu.getD i 0 * ∑ j ∈ range 1600,
    w.getD j 0 * bitF (LeanVM.Protocol.KeccakGkr.stAt
      (statesOfS Shape.v1 (P + 1) (Itree (P + 1 + 4) q) 12) (P + 1) z i j))
  simp only [List.length_singleton, pow_one] at hs
  rw [claimSumF, hs, sum_two, eq1_zero, eq1_one]
  have hG : ∀ m < 2, ∀ t ∈ range 2, ∀ y ∈ range (2 ^ P), ∀ i : ℕ,
      ∑ j ∈ range 1600, w.getD j 0 * bitF (LeanVM.Protocol.KeccakGkr.stAt
        (statesOfS Shape.v1 (P + 1) (Itree (P + 1 + 4) q) 12) (P + 1)
          (y + 2 ^ P * t + 2 ^ (P + 1) * m) i j) =
        Gs (P + 1 + 4) q w m (i + 16 * y + 2 ^ (P + 1 + 3) * t) := by
    intro m hm t ht y hy i
    obtain ⟨h1, h2⟩ := idx_split (m := m) (Finset.mem_range.1 hy) (Finset.mem_range.1 ht)
    have e : i + 16 * (y + 2 ^ P * t) = i + 16 * y + 2 ^ (P + 1 + 3) * t := by
      rw [show P + 1 + 3 = 4 + P by ring, pow_add]; ring
    unfold LeanVM.Protocol.KeccakGkr.stAt
    rw [h1, h2, e]
    rfl
  have e0 : ∀ m < 2, (∑ t ∈ range 2, eqAtF [rt] t * ∑ y ∈ range (2 ^ P), eqAtF rm y *
      ∑ i ∈ range 16, mu.getD i 0 * ∑ j ∈ range 1600, w.getD j 0 *
        bitF (LeanVM.Protocol.KeccakGkr.stAt (statesOfS Shape.v1 (P + 1) (Itree (P + 1 + 4) q) 12)
          (P + 1) (y + 2 ^ P * t + 2 ^ (P + 1) * m) i j)) =
      ∑ t ∈ range 2, eqAtF [rt] t * ∑ y ∈ range (2 ^ P), eqAtF rm y *
        ∑ i ∈ range 16, mu.getD i 0 * Gs (P + 1 + 4) q w m (i + 16 * y + 2 ^ (P + 1 + 3) * t) :=
    fun m hm ↦ Finset.sum_congr rfl fun t ht ↦ congrArg _ (Finset.sum_congr rfl fun y hy ↦
      congrArg _ (Finset.sum_congr rfl fun i _ ↦ congrArg _ (hG m hm t ht y hy i)))
  rw [e0 0 (by norm_num), e0 1 (by norm_num)]
  have comb : (1 + rs) * (∑ t ∈ range 2, eqAtF [rt] t * ∑ y ∈ range (2 ^ P), eqAtF rm y *
        ∑ i ∈ range 16, mu.getD i 0 * Gs (P + 1 + 4) q w 0 (i + 16 * y + 2 ^ (P + 1 + 3) * t)) +
      rs * (∑ t ∈ range 2, eqAtF [rt] t * ∑ y ∈ range (2 ^ P), eqAtF rm y *
        ∑ i ∈ range 16, mu.getD i 0 * Gs (P + 1 + 4) q w 1 (i + 16 * y + 2 ^ (P + 1 + 3) * t)) =
      ∑ t ∈ range 2, eqAtF [rt] t * ∑ y ∈ range (2 ^ P), eqAtF rm y *
        ∑ i ∈ range 16, mu.getD i 0 * ((1 + rs) * cT w t +
          Hx (P + 1) q rs w t (i + 16 * y + 2 ^ (P + 1 + 3) * t)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht ↦ Finset.sum_congr rfl fun y hy ↦
      Finset.sum_congr rfl fun i hi ↦ ?_
    have hc := Gs_comb (P + 1) q rs w (i + 16 * y + 2 ^ (P + 1 + 3) * t)
    rw [tOf_idx (Finset.mem_range.1 hi) (Finset.mem_range.1 hy) (Finset.mem_range.1 ht)] at hc
    linear_combination (eqAtF [rt] t * (eqAtF rm y * mu.getD i 0)) * hc
  rw [comb]
  have hsplit : ∀ (c : ℕ → E2) (H : ℕ → ℕ → ℕ → E2),
      ∑ t ∈ range 2, eqAtF [rt] t * ∑ y ∈ range (2 ^ P), eqAtF rm y *
        ∑ i ∈ range 16, mu.getD i 0 * (c t + H t y i) =
      ∑ t ∈ range 2, eqAtF [rt] t * ∑ y ∈ range (2 ^ P), eqAtF rm y *
        ∑ i ∈ range 16, mu.getD i 0 * c t +
      ∑ t ∈ range 2, eqAtF [rt] t * ∑ y ∈ range (2 ^ P), eqAtF rm y *
        ∑ i ∈ range 16, mu.getD i 0 * H t y i := by
    intro c H
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hsplit (fun t ↦ (1 + rs) * cT w t)
    (fun t y i ↦ Hx (P + 1) q rs w t (i + 16 * y + 2 ^ (P + 1 + 3) * t))]
  rw [Tsum, Nat.add_sub_cancel]
  refine congrArg (· + _) ?_
  have hsy := sum_eqAtF rm
  rw [hrm] at hsy
  have hk : ∀ t ∈ range 2, eqAtF [rt] t * ∑ y ∈ range (2 ^ P), eqAtF rm y *
      ∑ i ∈ range 16, mu.getD i 0 * ((1 + rs) * cT w t) =
      eqAtF [rt] t * ((1 + rs) * cT w t * mu.sum) := by
    intro t _
    rw [← Finset.sum_mul, ← Finset.sum_mul, hsy, one_mul, list_sum_getD, hmu]
    ring
  rw [Finset.sum_congr rfl hk, sum_two, eq1_zero, eq1_one, cT, cT, ite_eq_left rfl, ite_eq_right one_ne_zero]
  ring

/-! ## The sumcheck family -/

/-- The weight of slice `z` at the sumcheck index `n = i + 16·t + 32·o`. -/
def aE (rt rs : E2) (mu w : List E2) (z n : ℕ) : E2 :=
  mu.getD (n % 16) 0 * eqAtF [rt] (n / 16 % 2) * wtX rs w (n / 16 % 2) (n / 32) z

/-- Slice `z` at the sumcheck index `n`, the middle row bits bound to `rm`. -/
def bE (P : ℕ) (q : Stack) (rm : List E2) (z n : ℕ) : E2 :=
  ∑ y ∈ range (2 ^ (P - 1)), eqAtF rm y *
    cb q z (n % 16 + 16 * y + 2 ^ (P + 3) * (n / 16 % 2) + 2 ^ (P + 4) * (n / 32))

/-- **The input end's sumcheck family** over 11 variables (4 low row bits, the top row bit,
6 slot bits). -/
def FeF (P : ℕ) (q : Stack) (rm : List E2) (rt rs : E2) (mu w : List E2) (acc : List E2) : E2 :=
  cubeSumF (fun pt ↦ ∑ z ∈ range 64, (∑ n ∈ range (2 ^ 11), eqAtF pt n * aE rt rs mu w z n) *
    ∑ n ∈ range (2 ^ 11), eqAtF pt n * bE P q rm z n) 11 acc

/-- The family has degree 2 in each variable. -/
theorem FeF_plain {β : Type} (P : ℕ) (stk : β → Stack) (rm : List E2) (rt rs : E2)
    (mu w : List E2) : PlainFamilyF (fun q acc ↦ FeF P (stk q) rm rt rs mu w acc) 2 11 :=
  cube_plainFamilyF (fun q pt ↦ ∑ z ∈ range 64,
      (∑ n ∈ range (2 ^ 11), eqAtF pt n * aE rt rs mu w z n) *
        ∑ n ∈ range (2 ^ 11), eqAtF pt n * bE P (stk q) rm z n) 11
    fun _ pre post ↦ PolyLEF.sum _ fun _ _ ↦ polyLEF_mle_mul _ _ _ _ pre post

/-- The 11 sumcheck variables as `i + 16·t + 32·o`. -/
theorem sum11 (G : ℕ → E2) : ∑ u ∈ range (2 ^ 11), G u =
    ∑ o ∈ range 64, ∑ t ∈ range 2, ∑ i ∈ range 16, G (i + 16 * t + 32 * o) := by
  rw [show 2 ^ 11 = 32 * 64 from rfl, sum_range_mulW]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [show 32 = 16 * 2 from rfl, sum_range_mulW]

theorem idx11 {i t : ℕ} (o : ℕ) (hi : i < 16) (ht : t < 2) :
    (i + 16 * t + 32 * o) % 16 = i ∧ (i + 16 * t + 32 * o) / 16 % 2 = t ∧
      (i + 16 * t + 32 * o) / 32 = o := by
  refine ⟨by omega, by omega, by omega⟩

/-- Reordering five nested sums. -/
theorem perm5 (g : ℕ → ℕ → ℕ → ℕ → ℕ → E2) (A B C D E : Finset ℕ) :
    ∑ o ∈ D, ∑ t ∈ A, ∑ i ∈ C, ∑ z ∈ E, ∑ y ∈ B, g t y i o z =
      ∑ t ∈ A, ∑ y ∈ B, ∑ i ∈ C, ∑ o ∈ D, ∑ z ∈ E, g t y i o z := by
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun t _ ↦ ?_)
  have h1 : ∀ o i, ∑ z ∈ E, ∑ y ∈ B, g t y i o z = ∑ y ∈ B, ∑ z ∈ E, g t y i o z :=
    fun _ _ ↦ Finset.sum_comm
  simp only [h1]
  refine Finset.sum_comm.trans ?_
  have h2 : ∀ i, ∑ o ∈ D, ∑ y ∈ B, ∑ z ∈ E, g t y i o z = ∑ y ∈ B, ∑ o ∈ D, ∑ z ∈ E, g t y i o z :=
    fun _ ↦ Finset.sum_comm
  simp only [h2]
  exact Finset.sum_comm

/-- **Before the rounds**: the family's sum over the cube is `Tsum`. -/
theorem FeF_nil (P : ℕ) (q : Stack) (rm : List E2) (rt rs : E2) (mu w : List E2) :
    FeF P q rm rt rs mu w [] = Tsum P q rm rt rs mu w := by
  rw [FeF, cubeSumF_nil]
  have hu : ∀ u ∈ range (2 ^ 11), ∑ z ∈ range 64,
      (∑ n ∈ range (2 ^ 11), eqAtF (bitsF u 11) n * aE rt rs mu w z n) *
        ∑ n ∈ range (2 ^ 11), eqAtF (bitsF u 11) n * bE P q rm z n =
      ∑ z ∈ range 64, aE rt rs mu w z u * bE P q rm z u := fun u hu ↦
    Finset.sum_congr rfl fun z _ ↦ by
      rw [sum_eqAtF_bitsF (Finset.mem_range.1 hu), sum_eqAtF_bitsF (Finset.mem_range.1 hu)]
  rw [Finset.sum_congr rfl hu, sum11]
  have hab : ∀ o ∈ range 64, ∀ t ∈ range 2, ∀ i ∈ range 16,
      ∑ z ∈ range 64, aE rt rs mu w z (i + 16 * t + 32 * o) * bE P q rm z (i + 16 * t + 32 * o) =
      ∑ z ∈ range 64, ∑ y ∈ range (2 ^ (P - 1)), eqAtF [rt] t * (eqAtF rm y * (mu.getD i 0 *
        (wtX rs w t o z * cb q z (i + 16 * y + 2 ^ (P + 3) * t + 2 ^ (P + 4) * o)))) := by
    intro o _ t ht i hi
    obtain ⟨e1, e2, e3⟩ := idx11 o (Finset.mem_range.1 hi) (Finset.mem_range.1 ht)
    simp only [aE, bE, e1, e2, e3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun y _ ↦ by ring
  rw [Finset.sum_congr rfl fun o ho ↦ Finset.sum_congr rfl fun t ht ↦
    Finset.sum_congr rfl fun i hi ↦ hab o ho t ht i hi, perm5]
  simp only [Tsum, Hx, Finset.mul_sum]

/-! ## At the last point -/

/-- The last point as `(ϱ_low, ϱ_top, ϱ_slot)`. -/
theorem rho_split {ϱ : List E2} (hϱ : ϱ.length = 11) : ϱ = ϱ.take 4 ++ [ϱ.getD 4 0] ++ ϱ.drop 5 := by
  match ϱ, hϱ with
  | _ :: _ :: _ :: _ :: _ :: _, _ => rfl

theorem split_rho {ϱ : List E2} (hϱ : ϱ.length = 11) (G : ℕ → E2) :
    ∑ n ∈ range (2 ^ 11), eqAtF ϱ n * G n =
      ∑ o ∈ range 64, eqAtF (ϱ.drop 5) o * ∑ t ∈ range 2, eqAtF [ϱ.getD 4 0] t *
        ∑ x ∈ range 16, eqAtF (ϱ.take 4) x * G (x + 16 * t + 32 * o) := by
  have h4 : (ϱ.take 4).length = 4 := by simp [hϱ]
  have h6 : (ϱ.drop 5).length = 6 := by simp [hϱ]
  have hs := split3 (ϱ.take 4) h4 (ϱ.getD 4 0) (ϱ.drop 5) G
  rw [← rho_split hϱ, h6] at hs
  exact hs

/-- **The weights at the last point** are the verifier's `μ̃ · treeWt`. -/
theorem aE_full {ϱ : List E2} (hϱ : ϱ.length = 11) (rt rs : E2) (mu w : List E2) (z : ℕ) :
    ∑ n ∈ range (2 ^ 11), eqAtF ϱ n * aE rt rs mu w z n =
      MuTF mu (ϱ.take 4) * treeWt rs rt (ϱ.getD 4 0) w (ϱ.drop 5) z := by
  rw [split_rho hϱ]
  have hin : ∀ o t, t < 2 → ∑ x ∈ range 16, eqAtF (ϱ.take 4) x * aE rt rs mu w z (x + 16 * t + 32 * o) =
      eqAtF [rt] t * wtX rs w t o z * MuTF mu (ϱ.take 4) := by
    intro o t ht
    rw [MuTF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    obtain ⟨e1, e2, e3⟩ := idx11 o (Finset.mem_range.1 hx) ht
    rw [aE, e1, e2, e3]
    ring
  rw [Finset.sum_congr rfl fun o _ ↦ congrArg _ (Finset.sum_congr rfl fun t ht ↦
    congrArg _ (hin o t (Finset.mem_range.1 ht)))]
  rw [treeWt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [sum_two, eq1_zero, eq1_one, eq1_zero, eq1_one, wtX, wtX, pwT_zero, pwT_one]
  linear_combination (eqAtF (ϱ.drop 5) o * MuTF mu (ϱ.take 4) * rs * pwM w o z * ϱ.getD 4 0 * rt) *
    (CharTwo.two_eq_zero : (2 : E2) = 0)

/-- **The slices at the last point**: the family's second factor is slice `z` at the slice
point `(ϱ_low, r_mid, ϱ_top, ϱ_slot)`. -/
theorem bE_full {P : ℕ} (hP : 1 ≤ P) (q : Stack) {rm : List E2} (hrm : rm.length = P - 1)
    {ϱ : List E2} (hϱ : ϱ.length = 11) (z : ℕ) :
    ∑ n ∈ range (2 ^ 11), eqAtF ϱ n * bE P q rm z n =
      ∑ x ∈ range (2 ^ (P + 4 + 6)), eqAtF (ϱ.take 4 ++ rm ++ [ϱ.getD 4 0] ++ ϱ.drop 5) x *
        bitF ((q x).toBitVec.getLsbD z) := by
  obtain ⟨P, rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hrm
  have h4 : (ϱ.take 4).length = 4 := by simp [hϱ]
  have h6 : (ϱ.drop 5).length = 6 := by simp [hϱ]
  have h4m : (ϱ.take 4 ++ rm).length = 4 + P := by simp [hϱ, hrm]
  have hs2 := split3 (ϱ.take 4 ++ rm) h4m (ϱ.getD 4 0) (ϱ.drop 5) (cb q z)
  rw [h6, show 4 + P + 1 + 6 = P + 1 + 4 + 6 by ring] at hs2
  show _ = ∑ x ∈ range (2 ^ (P + 1 + 4 + 6)),
    eqAtF (ϱ.take 4 ++ rm ++ [ϱ.getD 4 0] ++ ϱ.drop 5) x * cb q z x
  rw [hs2, split_rho hϱ]
  refine Finset.sum_congr rfl fun o _ ↦ congrArg _ (Finset.sum_congr rfl fun t _ ↦ congrArg _ ?_)
  have hc := col_splitF (s := rm) h4 (fun x ↦ cb q z (x + 2 ^ (4 + P) * t + 2 ^ (4 + P + 1) * o))
  rw [hrm] at hc
  rw [hc]
  simp only [bE, Nat.add_sub_cancel, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x hx ↦ ?_
  obtain ⟨e1, e2, e3⟩ := idx11 o (Finset.mem_range.1 hx) (Finset.mem_range.1 ‹t ∈ range 2›)
  rw [e1, e2, e3]
  have ex : x + 16 * y + 2 ^ (P + 1 + 3) * t + 2 ^ (P + 1 + 4) * o =
      x + 2 ^ 4 * y + 2 ^ (4 + P) * t + 2 ^ (4 + P + 1) * o := by
    rw [show P + 1 + 3 = 4 + P by ring, show P + 1 + 4 = 4 + P + 1 by ring]; rfl
  rw [ex]
  ring

/-! ## The two ends of the rounds -/

theorem take_succ_getD (l : List E2) {n : ℕ} (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l.getD n 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]
  rfl

/-- The claim's point as `(r_mid, r_top, r'_seg)`. -/
theorem point_split {P : ℕ} {l : List E2} (hl : l.length = P + 1 + 1) :
    l = l.take P ++ [l.getD P 0] ++ [l.getD (P + 1) 0] := by
  have h1 : l.take (P + 1 + 1) = l := List.take_of_length_le (by omega)
  rw [take_succ_getD l (by omega), take_succ_getD l (by omega)] at h1
  exact h1.symm

/-- **The rounds' first claim**: if `value'` is the family's sum, the claim holds (`value'` and
the family's sum are the claim's value and its sum, each plus the constants' share). -/
theorem claimTrue_of_treeV' {P : ℕ} (hP : 1 ≤ P) (q : Stack) (claim : KClaim E2)
    (hshape : ClaimShapeF P claim)
    (h : treeV' P claim = FeF P q (claim.point.take (P - 1)) (claim.point.getD (P - 1) 0)
      (claim.point.getD P 0) claim.mu claim.weights []) :
    ClaimTrueF (statesOfS Shape.v1 P (Itree (P + 4) q) 12) P claim := by
  obtain ⟨P, rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
  have hm : (claim.point.take P).length = P := by simp [hshape.2.1]; omega
  have hcs := claimSum_tree q _ hm (claim.point.getD P 0) (claim.point.getD (P + 1) 0) hshape.1
    claim.weights
  rw [← point_split hshape.2.1] at hcs
  rw [FeF_nil, treeV'] at h
  simp only [Nat.add_sub_cancel] at h
  rw [ClaimTrueF, hcs, eq_sub_of_add_eq h, CharTwo.sub_eq_add, add_comm]

/-- **The final check**: with true slices at the slice point, the check gives the family at the
last point. -/
theorem final_tree {P : ℕ} (hP : 1 ≤ P) (q : Stack) (claim : KClaim E2)
    (hshape : ClaimShapeF P claim) {ϱ s : List E2} (hϱ : ϱ.length = 11) (value : E2)
    (hs : SlicesTrue6 (P + 4 + 6) q
      (ϱ.take 4 ++ claim.point.take (P - 1) ++ [ϱ.getD 4 0] ++ ϱ.drop 5) s)
    (hc : multilinearEvalF claim.mu (ϱ.take 4) * ∑ z ∈ range 64, treeWt (claim.point.getD P 0)
      (claim.point.getD (P - 1) 0) (ϱ.getD 4 0) claim.weights (ϱ.drop 5) z * s.getD z 0 = value) :
    value = FeF P q (claim.point.take (P - 1)) (claim.point.getD (P - 1) 0) (claim.point.getD P 0)
      claim.mu claim.weights ϱ := by
  have hrm : (claim.point.take (P - 1)).length = P - 1 := by simp [hshape.2.1]; omega
  rw [← hc, FeF, cubeSumF_full _ hϱ, multilinearEvalF_mu hshape.1 (by simp [hϱ]), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  rw [aE_full hϱ, bE_full hP q hrm hϱ, hs.2.2 z (Finset.mem_range.1 hz)]
  ring

/-! ## The input end in the doom calculus -/

/-- **Row 10 of the tree batch** (`treeEnd6`): from doom of the claim at depth 12 on the tree
inputs `Itree` to doom of the 64 slice claims at the slice point. Lead `0`; the 11 plain rounds
(`(2, 2)` each); the follower's `T` after the slices. -/
noncomputable def treeEndSpec {β : Type} {C : List Ev → Set β} [Finite β] (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop) (stk : β → Stack) (P : ℕ) (hP : 1 ≤ P)
    (claim : KClaim E2) (hshape : ClaimShapeF P claim) {T : ℝ≥0∞} (hT : T ≤ εS) :
    Spec (treeEnd6 P claim)
      (Doomed C (fun q ↦ ClaimTrueF (statesOfS Shape.v1 P (Itree (P + 4) (stk q)) 12) P claim ∧ R q))
      (fun en hist ↦ en.ϱ.length = 11 ∧ en.pt.length = P + 4 + 6 ∧ en.s.length = 64 ∧
        Doomed C (fun q ↦ SlicesTrue6 (P + 4 + 6) (stk q) en.pt en.s ∧ R q) hist) εS 0 T :=
  ((sumcheckGSpec (T := 0) hst hcard R
      (FeF_plain P stk (claim.point.take (P - 1)) (claim.point.getD (P - 1) 0) (claim.point.getD P 0)
        claim.mu claim.weights) (count := 3) (by norm_num) (by norm_num) (g := gC2) (by norm_num)
      errG_c2 11 [] (treeV' P claim) (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨claimTrue_of_treeV' hP (stk q) claim hshape hv, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun lv ↦
  if hy : lv.1.length = 11 then
    ((e2ReadsSpec (T := T) hst _ hT 63).mono (fun _ hd ↦ hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl
      le_rfl).bind' fun s ↦
    (Spec.require
      (Pre := fun h ↦ s.length = 63 + 1 ∧ Doomed C (fun q ↦ lv.2 = FeF P (stk q)
        (claim.point.take (P - 1)) (claim.point.getD (P - 1) 0) (claim.point.getD P 0) claim.mu
        claim.weights ([] ++ lv.1) ∧ R q) h)
      (Post := fun _ h ↦ s.length = 63 + 1 ∧ Doomed C (fun q ↦ SlicesTrue6 (P + 4 + 6) (stk q)
        (lv.1.take 4 ++ claim.point.take (P - 1) ++ [lv.1.getD 4 0] ++ lv.1.drop 5) s ∧ R q) h)
      fun _ hd hc ↦ ⟨hd.1, Doomed.mono hd.2 fun q ⟨hs, hR⟩ ↦ ⟨by
        rw [List.nil_append]; exact final_tree hP (stk q) claim hshape hy _ hs hc, hR⟩⟩).bind' fun _ ↦
    (Spec.ret (⟨lv.1, lv.1.take 4 ++ claim.point.take (P - 1) ++ [lv.1.getD 4 0] ++ lv.1.drop 5, s⟩ :
        EndOut)).mono
      (fun _ hd ↦ ⟨hy, by simp [hy, hshape.2.1]; omega, hd.1, hd.2⟩) (fun _ _ h' ↦ h') le_rfl
      le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hy hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl


end Lvm6.K
