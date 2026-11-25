-- lvm6 X9 (X8a §3 item 2): the algebraic step from the builder's `GoodB` (on the machine) to X4's `goodAt d Tc W`
-- (the extractor's agreement predicate over `E2`): `encRow` is `encN` (`fwdRun_enc`), the columns and the word
-- are the `E2` coordinates (`encN_coord`, `ysF_coord`). Hence `sbSpec = agreeS (goodAt …)`. New.
import Lvm6XDescSb

/-!
# The builder's predicate is the extractor's

* **`encRow_eq`**: lane `q`'s encoding (`fwdNIR` of the zero-padded first `d + 1` column words) is
  `encN ptK (column q, first d + 1)` at every position `j < 2^ℓ`.
* **`goodB_iff_goodAt`**: with the round's word position-major at `buf` (`HoldsW`, table entry `(buf, 2·2^m)`) and
  column `2⟨u⟩ + i` holding coordinate `i` of `Tc u`, `GoodB … j ↔ goodAt d Tc W j` for `j < 2^ℓ`.
* **`sbSpec_eq_goodAt`**: hence `sbSpec … = agreeS ℓ (d + 1) (goodAt d Tc W)`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir

/-- A zero-padded message's `encN` is the short message's. -/
theorem encN_pad (f : ℕ → BF64) {k n : ℕ} (hk : k ≤ n) (hf : ∀ x, k ≤ x → f x = 0) (j : ℕ) :
    encN ptK (fun x : Fin n ↦ f x) j = encN ptK (fun x : Fin k ↦ f x) j := by
  simp only [encN]
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ f x * algebraMap BF64 BF64 ((novelX ptK x).eval (ptK j))) n,
    Fin.sum_univ_eq_sum_range (fun x ↦ f x * algebraMap BF64 BF64 ((novelX ptK x).eval (ptK j))) k,
    ← Finset.sum_range_add_sum_Ico _ hk,
    Finset.sum_eq_zero (s := Ico k n) (fun x hx ↦ by rw [hf x (Finset.mem_Ico.1 hx).1, zero_mul]), add_zero]

/-- **Lane `q`'s encoding is `encN`** of its first `d + 1` column words. -/
theorem encRow_eq (M : Mem) {N ℓ colB str d q : ℕ} (hN : ℓ ≤ N) (hN64 : N ≤ 64) (hd : d + 1 ≤ 2 ^ ℓ) {j : ℕ}
    (hj : j < 2 ^ ℓ) :
    encRow M N ℓ colB str d q j = encN ptK (fun x : Fin (d + 1) ↦ rdK M (colB + str * q + x)) j := by
  let f : ℕ → BF64 := fun x ↦ if x < d + 1 then rdK M (colB + str * q + x) else 0
  have e1 : encRow M N ℓ colB str d q j = encN ptK (fun x : Fin (2 ^ ℓ) ↦ f x) j := by
    refine fwdRun_enc ptK_xor (ptK_injOn hN64) le_rfl hN (fun x : Fin (2 ^ ℓ) ↦ f x) f (fun x ↦ ?_) hj
    by_cases h : x < 2 ^ ℓ
    · rw [dif_pos h]
    · rw [dif_neg h]; exact if_neg (by omega)
  rw [e1, encN_pad f hd (fun x hx ↦ if_neg (by omega))]
  exact congrArg (fun c : Fin (d + 1) → BF64 ↦ encN ptK c j) (funext fun x ↦ if_pos x.2)

theorem coord_ext {z w : E2} (h : ∀ i : Fin 2, basisE2.coord i z = basisE2.coord i w) : z = w :=
  basisE2.ext_elem fun i ↦ by rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply]; exact h i

/-- **The builder's agreement predicate is the extractor's** at position `j < 2^ℓ`. -/
theorem goodB_iff_goodAt {M : Mem} {N ℓ colB str d tS r m buf : ℕ} {W : Wd E2 (2 ^ ℓ) m} {Tc : CT E2 m}
    (hN : ℓ ≤ N) (hN64 : N ≤ 64) (hd : d + 1 ≤ 2 ^ ℓ)
    (hW : HoldsW M buf ℓ m W) (hb : tbBase M tS r = buf) (ho : tbOcc M tS r = 2 * 2 ^ m)
    (hC : ∀ (u : Fin m → Bool) (i : Fin 2), ∀ x < d + 1,
      rdK M (colB + str * (2 * bitsToNat u + i) + x) = basisE2.coord i (Tc u x))
    {j : ℕ} (hj : j < 2 ^ ℓ) :
    GoodB M N ℓ colB str d tS r j ↔ goodAt d Tc W j := by
  -- lane `2⟨u⟩ + i`: its encoding and its word are coordinate `i`
  have hE : ∀ (u : Fin m → Bool) (i : Fin 2), encRow M N ℓ colB str d (2 * bitsToNat u + i) j =
      basisE2.coord i (encN ptK (fun x : Fin (d + 1) ↦ Tc u x) j) := fun u i ↦ by
    rw [encRow_eq M hN hN64 hd hj, encN_coord basisE2]
    exact congrArg (fun c : Fin (d + 1) → BF64 ↦ encN ptK c j) (funext fun x ↦ hC u i x x.2)
  have hV : ∀ (u : Fin m → Bool) (i : Fin 2),
      rdK M (tbBase M tS r + (2 * bitsToNat u + i) + tbOcc M tS r * j) = basisE2.coord i (wAtN (W u) j) :=
    fun u i ↦ by
      have h2 := ysF_coord hW hb ho u ⟨j, hj⟩
      rw [show wAtN (W u) j = W u ⟨j, hj⟩ from dif_pos hj]
      fin_cases i
      · show rdK M (tbBase M tS r + (2 * bitsToNat u + 0) + tbOcc M tS r * j) = basisE2.coord 0 _
        rw [Nat.add_zero]; exact h2.1
      · show rdK M (tbBase M tS r + (2 * bitsToNat u + 1) + tbOcc M tS r * j) = basisE2.coord 1 _
        exact h2.2
  constructor
  · intro hg u
    refine coord_ext fun i ↦ ?_
    have hq : 2 * bitsToNat u + (i : ℕ) < tbOcc M tS r := by
      have := bitsToNat_lt u; have := i.2; rw [ho]; omega
    rw [← hE, ← hV]
    exact hg _ hq
  · intro hg q hq
    rw [ho] at hq
    have hq2 : q / 2 < 2 ^ m := by omega
    let u : Fin m → Bool := fun i ↦ (q / 2).testBit i
    have hu : bitsToNat u = q / 2 := bitsToNat_testBit hq2
    have eq : q = 2 * bitsToNat u + ((⟨q % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) : ℕ) := by
      simp only [hu, Fin.val_mk]; omega
    rw [eq, hE, hV, hg u]

open Classical in
/-- **The builder's list is the extractor's `S`**: `sbSpec = agreeS ℓ (d + 1) (goodAt d Tc W)`. -/
theorem sbSpec_eq_goodAt {M : Mem} {N ℓ colB str d tS r m buf : ℕ} {W : Wd E2 (2 ^ ℓ) m} {Tc : CT E2 m}
    (hN : ℓ ≤ N) (hN64 : N ≤ 64) (hd : d + 1 ≤ 2 ^ ℓ)
    (hW : HoldsW M buf ℓ m W) (hb : tbBase M tS r = buf) (ho : tbOcc M tS r = 2 * 2 ^ m)
    (hC : ∀ (u : Fin m → Bool) (i : Fin 2), ∀ x < d + 1,
      rdK M (colB + str * (2 * bitsToNat u + i) + x) = basisE2.coord i (Tc u x)) :
    sbSpec M N ℓ colB str d tS r = agreeS ℓ (d + 1) (goodAt d Tc W) :=
  sbSpec_eq_agreeS M N ℓ colB str d tS r fun _ hj ↦ goodB_iff_goodAt hN hN64 hd hW hb ho hC hj

end Lvm6.X
