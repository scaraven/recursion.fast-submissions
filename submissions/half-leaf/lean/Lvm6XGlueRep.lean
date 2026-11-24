-- lvm6 EXG (DP6 §2 item 2, the algebra): the start of a level's descent as novel-basis coefficients. A mid level
-- starts from W1's candidate `cand hi U` of the next level's decoded tuple `U` (`TailIface.cand` of `tailE2`): its
-- coefficients are `U`'s lanes' low parts interleaved (coefficient `L + 2^ℓ'·y` is lane `L`'s coefficient `y`), then
-- the high part `hi` (`candC`, `rep_cand`); the final level starts from `fpolyE κ ℓ s`, whose coefficients are `s`
-- (`rep_fpoly`). New.
import Lvm6XDescDec

/-!
# The level glue's algebra

* `laneOf ℓ' x`: the lane of coefficient `x` (its low `ℓ'` bits); **`candC κ ℓ' Tc hi`**: below `2^κ`, coefficient
  `x` is `Tc (laneOf ℓ' x) (x / 2^ℓ')`; then `hi`.
* **`rep_cand`**: `RepT d' Tc U` (`d' = 2^κ' − 1 + ℓ'`) ⟹ `RepT (2^κ − 1 + ℓ) (candC κ ℓ' Tc hi) (cand hi U)` for
  W1's `tailE2` (`κ = ko + 1 = ℓ' + κ'`).
* **`rep_fpoly`**: `RepT (2^κ − 1 + ℓ) (fun _ x ↦ s.getD x 0) (fpolyE κ ℓ s)`.
-/

set_option autoImplicit false

namespace Lvm6.X

open Polynomial Finset LeanVM.Parameters LeanVM.Protocol.Whir Lvm6.Whir Lvm.X

/-- The lane of coefficient `x`: its low `ℓ'` bits. -/
def laneOf (ℓ' x : ℕ) : Fin ℓ' → Bool := fun j ↦ x.testBit j

theorem bitsToNat_laneOf (ℓ' x : ℕ) : bitsToNat (laneOf ℓ' x) = x % 2 ^ ℓ' := by
  have h := bitsToNat_testBit (κ := ℓ') (j := x % 2 ^ ℓ') (Nat.mod_lt _ (Nat.two_pow_pos ℓ'))
  rw [← h]
  congr 1
  funext j
  rw [laneOf, Nat.testBit_mod_two_pow, decide_eq_true j.isLt, Bool.true_and]

/-- **The candidate's coefficients**: lane `x mod 2^ℓ'`'s coefficient `x / 2^ℓ'` below `2^κ`, then the high part. -/
def candC {ℓ' : ℕ} (κ : ℕ) (Tc : CT E2 ℓ') (hi : List E2) : CT E2 0 := fun _ x ↦
  if x < 2 ^ κ then Tc (laneOf ℓ' x) (x / 2 ^ ℓ') else hi.getD (x - 2 ^ κ) 0

/-- Reindexing a cube point along `n = n'`. -/
theorem bitsToNat_cast {n n' : ℕ} (h : n = n') (w : Fin n' → Bool) :
    bitsToNat (fun i : Fin n ↦ w (Fin.cast h i)) = bitsToNat w := by
  unfold bitsToNat
  exact Fintype.sum_equiv (finCongr h) _ _ fun i ↦ by simp

/-- **A cube point split**: `⟨w⟩ = ⟨w|_{< a}⟩ + 2^a·⟨w|_{≥ a}⟩`. -/
theorem bitsToNat_split {a b : ℕ} (w : Fin (a + b) → Bool) :
    bitsToNat w = bitsToNat (fun i : Fin a ↦ w (Fin.castAdd b i)) +
      2 ^ a * bitsToNat (fun j : Fin b ↦ w (Fin.natAdd a j)) := by
  unfold bitsToNat
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Fin.coe_natAdd, pow_add]
  ring

/-- A polynomial held as coefficients below `d + 1 = 2^κ + m` (X's `novM ptK`) as W1's `novelF` sum. -/
theorem rep_sum_novelF {m d : ℕ} {Tc : CT E2 m} {T : Tup E2 m} (hR : RepT d Tc T) (u : Fin m → Bool)
    (hd : d + 1 ≤ 2 ^ 64) :
    T u = ∑ x ∈ range (d + 1), C (Tc u x) * Lvm6.Whir.novelF x := by
  have hR' : ∀ u, T u = ∑ x : Fin (d + 1), C (Tc u x) * (Lvm.Nb.novM ptK x : E2[X]) := hR
  rw [hR' u, Fin.sum_univ_eq_sum_range (fun x : ℕ ↦ C (Tc u x) * (Lvm.Nb.novM ptK x : E2[X])) (d + 1)]
  exact Finset.sum_congr rfl fun x hx ↦ by
    rw [novM_eq_novelF (F := E2) (lt_of_lt_of_le (mem_range.1 hx) hd)]

/-- **The low part of a decoded lane** is its first `2^κ'` coefficients. -/
theorem lowMsg_rep {m κ' ℓ' : ℕ} {Tc : CT E2 m} {U : Tup E2 m} (hκ : κ' < 64) (hℓ : ℓ' ≤ 2 ^ κ')
    (hR : RepT (2 ^ κ' - 1 + ℓ') Tc U) (u : Fin m → Bool) (v : Fin κ' → Bool) :
    lowMsgF κ' (U u) v = Tc u (bitsToNat v) := by
  have h1 : 1 ≤ 2 ^ κ' := Nat.one_le_two_pow
  have h64 : 2 ^ κ' + ℓ' ≤ 2 ^ 64 := by
    have : 2 ^ κ' ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : (2 : ℕ) ^ 64 = 2 * 2 ^ 63 := by norm_num
    omega
  rw [rep_sum_novelF hR u (by omega), show 2 ^ κ' - 1 + ℓ' + 1 = 2 ^ κ' + ℓ' by omega,
    lowMsgF_sum_novelF hκ hℓ]

/-- The message polynomial of `v ↦ c ⟨v⟩` is the novel-basis sum of `c` below `2^κ`. -/
theorem msgPolyF_eq_sum (κ : ℕ) (c : ℕ → E2) :
    Lvm6.Whir.msgPolyF κ (fun v ↦ c (bitsToNat v)) = ∑ x ∈ range (2 ^ κ), C (c x) * Lvm6.Whir.novelF x := by
  show ∑ v, c (bitsToNat v) • Lvm6.Whir.novelF (bitsToNat v) = _
  rw [← Fin.sum_univ_eq_sum_range (fun x ↦ C (c x) * (Lvm6.Whir.novelF x : E2[X])),
    ← (bitsEquiv κ).sum_comp]
  exact Finset.sum_congr rfl fun v _ ↦ by rw [bitsEquiv_val, Polynomial.smul_eq_C_mul]

/-- The high part as novel-basis coefficients `2^κ … 2^κ + ℓ − 1`. -/
theorem highF_eq_sum {κ ℓ : ℕ} (hκ : κ < 64) (hℓ : ℓ ≤ 2 ^ κ) (c : ℕ → E2) :
    highF κ ℓ (List.ofFn fun s : Fin ℓ ↦ c (2 ^ κ + s)) =
      ∑ s ∈ range ℓ, C (c (2 ^ κ + s)) * Lvm6.Whir.novelF (2 ^ κ + s) := by
  rw [highF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hs' := mem_range.1 hs
  have e : (List.ofFn fun s : Fin ℓ ↦ c (2 ^ κ + s)).getD s 0 = c (2 ^ κ + s) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hs'), List.getElem_ofFn]
  rw [e, Lvm6.Whir.novelF, Lvm6.Whir.novelF, novel_two_pow_add hκ (by omega), Polynomial.map_mul, vanNF]
  ring

/-- `highF` reads only the first `ℓ` entries. -/
theorem highF_take (κ ℓ : ℕ) (hi : List E2) :
    highF κ ℓ hi = highF κ ℓ (List.ofFn fun s : Fin ℓ ↦ hi.getD s 0) := by
  unfold highF
  refine congrArg (vanNF κ * ·) (Finset.sum_congr rfl fun s hs ↦ ?_)
  have hs' := mem_range.1 hs
  rw [List.getD_eq_getElem (List.ofFn fun s : Fin ℓ ↦ hi.getD s 0) 0 (by simpa using hs'), List.getElem_ofFn]

/-- **A polynomial `P_g + Ŵ_κ·Σ hi_s X_s`** as novel-basis coefficients: `g` below `2^κ`, then `hi`. -/
theorem msg_high_rep {κ ℓ : ℕ} (hκ : κ < 64) (hℓ : ℓ ≤ 2 ^ κ) (c : ℕ → E2) (hi : List E2)
    (hc : ∀ s < ℓ, c (2 ^ κ + s) = hi.getD s 0) :
    Lvm6.Whir.msgPolyF κ (fun v ↦ c (bitsToNat v)) + highF κ ℓ hi =
      ∑ x : Fin (2 ^ κ - 1 + ℓ + 1), C (c x) * (Lvm.Nb.novM ptK x : E2[X]) := by
  have h1 : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  have h64 : 2 ^ κ + ℓ ≤ 2 ^ 64 := by
    have : 2 ^ κ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : (2 : ℕ) ^ 64 = 2 * 2 ^ 63 := by norm_num
    omega
  rw [Fin.sum_univ_eq_sum_range (fun x : ℕ ↦ C (c x) * (Lvm.Nb.novM ptK x : E2[X])) (2 ^ κ - 1 + ℓ + 1),
    show 2 ^ κ - 1 + ℓ + 1 = 2 ^ κ + ℓ by omega, Finset.sum_range_add, msgPolyF_eq_sum]
  have hhi : highF κ ℓ hi = highF κ ℓ (List.ofFn fun s : Fin ℓ ↦ c (2 ^ κ + s)) := by
    rw [highF_take]; exact congrArg (highF κ ℓ) (List.ofFn_inj.2 (funext fun s ↦ (hc s s.isLt).symm))
  rw [hhi, highF_eq_sum hκ hℓ]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Finset.sum_congr rfl fun x hx ↦ by
      rw [novM_eq_novelF (F := E2) (lt_of_lt_of_le (mem_range.1 hx) (by omega))]
  · exact Finset.sum_congr rfl fun x hx ↦ by
      rw [novM_eq_novelF (F := E2) (by have := mem_range.1 hx; omega)]

/-- **The final level's start**: the coefficients of `fpolyE κ ℓ s` are `s`. -/
theorem rep_fpoly {κ ℓ : ℕ} (hκ : κ < 64) (hℓ : ℓ ≤ 2 ^ κ) (s : List E2) :
    RepT (2 ^ κ - 1 + ℓ) (fun _ x ↦ s.getD x 0) (fpolyE κ ℓ s) := by
  intro u
  show Lvm6.Whir.msgPolyF κ (fun v ↦ s.getD (bitsToNat v) 0) + highF κ ℓ (s.drop (2 ^ κ)) = _
  exact msg_high_rep hκ hℓ (fun x ↦ s.getD x 0) _ fun j _ ↦ by simp [List.getD_eq_getElem?_getD]

/-- **A mid level's start**: `RepT` of the next level's decoded tuple `U` gives `RepT` of `cand hi U` with the
interleaved coefficients `candC`. -/
theorem rep_cand {ko ℓ h κ' ℓ' h' kq t c : ℕ} (hκ : 0 + ℓ' + κ' = ko + 1) (hko : ko + 1 < 64) (hℓ : 1 ≤ ℓ)
    (hℓ' : ℓ ≤ 64) (hh : h ≤ 64) (hh' : h' ≤ 64) (hc : 0 < c) (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c)
    (hℓκ : ℓ ≤ 2 ^ (ko + 1)) (hℓ'κ : ℓ' ≤ 2 ^ κ') {Tc : CT E2 (0 + ℓ')} {U : Tup E2 (0 + ℓ')}
    (hR : RepT (2 ^ κ' - 1 + ℓ') Tc U) (hi : List E2) :
    RepT (2 ^ (ko + 1) - 1 + ℓ) (candC (ko + 1) Tc hi)
      ((tailE2 ko ℓ h κ' ℓ' h' kq t c hκ hko hℓ hℓ' hh hh' hc hch ht).cand hi U) := by
  intro u
  show Lvm6.Whir.msgPolyF (ko + 1) (keyE κ' ℓ' ko hκ U) + highF (ko + 1) ℓ hi = _
  have hk : keyE κ' ℓ' ko hκ U = fun v ↦ candC (ko + 1) Tc hi u (bitsToNat v) := by
    funext w
    have hlt := bitsToNat_lt w
    have hsplit := bitsToNat_split (fun i : Fin (0 + ℓ' + κ') ↦ w (Fin.cast hκ i))
    rw [bitsToNat_cast hκ w] at hsplit
    have hlane : laneOf (0 + ℓ') (bitsToNat w) = fun j ↦ w (finCongr hκ (finSumFinEquiv (Sum.inl j))) := by
      funext j
      rw [laneOf, finSumFinEquiv_apply_left, finCongr_apply]
      exact testBit_bitsToNat w (Fin.cast hκ (Fin.castAdd κ' j))
    have hlow : bitsToNat w / 2 ^ (0 + ℓ') =
        bitsToNat fun j : Fin κ' ↦ w (finCongr hκ (finSumFinEquiv (Sum.inr j))) := by
      rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (bitsToNat_lt _), zero_add]
      rfl
    simp only [candC, hlt, ↓reduceIte, hlane, hlow]
    exact lowMsg_rep (by omega) hℓ'κ hR _ _
  rw [hk]
  exact msg_high_rep hko hℓκ (candC (ko + 1) Tc hi u) hi fun s hs ↦ by
    simp only [candC, show ¬ 2 ^ (ko + 1) + s < 2 ^ (ko + 1) by omega, ↓reduceIte, Nat.add_sub_cancel_left]

end Lvm6.X
