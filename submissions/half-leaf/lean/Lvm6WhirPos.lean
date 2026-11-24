-- New for lvm6 (WP W1). The deployed query positions (FORMAT6 v2.2.1 §5 "Positions"): a draw's
-- value `N = c₀ + 2^64·c₁` (lanes 0–1) gives the positions `(N >> (j·ht)) mod 2^ht`,
-- `j < ⌊128/ht⌋`; a level's `t` positions are the first `t` of its draws' positions. Their count
-- `card_posE2` is `TailIface.card_pos`/`FinIface.card_pos`: all positions in `S` with probability at
-- most `(|S|/2^ht)^t`. After leanVM `Whir/Sound/Queries.lean` (`card_chunks`) @ fdb317982 and
-- season 1's `LvmWhirGroupEscape.eNatEquiv`, here for the `E2` values of several draws.
import Lvm6WhirE2

/-!
# The deployed positions (W1)

* `e2Nat y = re + 2^64·im` (the draw's lanes 0–1 as a number); `e2NatEquiv : E2 ≃ [0, 2^128)`.
* `posE2 h c d t v k`: position `k` is digit `k mod c` (base `2^h`) of draw `k / c`'s number.
* `card_digits`: among `d`-tuples of numbers below `R·B^c`, exactly `|S|^t B^(dc−t) R^d` have their
  first `t` digits (draw-major, `c` per draw) in `S`.
* **`card_posE2`**: `#{v | ∀ k, posE2 v k ∈ S} ≤ |E2|^d (|S|/2^h)^t` for `c·h ≤ 128`, `t ≤ d·c`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier Finset
open scoped ENNReal

/-! ## `E2` values as numbers -/

/-- A draw's value as a number: lane 0 plus `2^64` times lane 1. -/
def e2Nat (y : E2) : ℕ := kToNat y.re + 2 ^ 64 * kToNat y.im

/-- The two lanes of a value as `64`-bit digits. -/
def e2Digits (y : E2) : Fin 2 → Fin (2 ^ 64) := ![y.re.toBitVec.toFin, y.im.toBitVec.toFin]

theorem e2Digits_injective : Function.Injective e2Digits := by
  intro y y' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [e2Digits, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact QuadraticAlgebra.ext (BF64.toBitVec_injective (BitVec.toFin_inj.mp h0))
    (BF64.toBitVec_injective (BitVec.toFin_inj.mp h1))

/-- **The value as a number is a bijection `E2 ≃ [0, 2^128)`.** -/
noncomputable def e2NatEquiv : E2 ≃ Fin ((2 ^ 64) ^ 2) :=
  Equiv.ofBijective (fun y ↦ finFunctionFinEquiv (e2Digits y))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨finFunctionFinEquiv.injective.comp e2Digits_injective, by
        rw [card_E2, Fintype.card_fin, ← pow_mul]⟩)

theorem e2NatEquiv_val (y : E2) : (e2NatEquiv y : ℕ) = e2Nat y := by
  show (finFunctionFinEquiv (e2Digits y) : ℕ) = _
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_two]
  simp only [e2Nat, kToNat, e2Digits, Matrix.cons_val_zero, Matrix.cons_val_one,
    BitVec.val_toFin, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one]
  rw [Nat.mul_comm]

/-! ## Digits -/

/-- The digit `x / B^j mod B` of a number below `R·B^c`, as `Fin B`. -/
def digF {B : ℕ} (hB : 0 < B) (x j : ℕ) : Fin B := ⟨x / B ^ j % B, Nat.mod_lt _ hB⟩

/-- Below `c` digits, reducing mod `B^c` keeps the digit. -/
theorem div_pow_mod_of_lt {B c j : ℕ} (hB : 0 < B) (hj : j < c) (x : ℕ) :
    x % B ^ c / B ^ j % B = x / B ^ j % B := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hj
  rw [show B ^ (j + m + 1) = B ^ j * B ^ (m + 1) by rw [← pow_add]; ring_nf,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self B (by omega))]

/-- The digits of `d` numbers, draw-major: an equivalence with the digits and the high parts. -/
noncomputable def digEquiv (B c R d : ℕ) :
    (Fin d → Fin (R * B ^ c)) ≃ (Fin (d * c) → Fin B) × (Fin d → Fin R) :=
  (Equiv.piCongrRight fun _ ↦ finProdFinEquiv.symm).trans <|
    (Equiv.arrowProdEquivProdArrow _ _ _).trans <|
      (Equiv.prodComm _ _).trans <|
        Equiv.prodCongr ((Equiv.piCongrRight fun _ ↦ finFunctionFinEquiv.symm).trans <|
          (Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl _))) (Equiv.refl _)

theorem digEquiv_fst {B c R d : ℕ} (hB : 0 < B) (v : Fin d → Fin (R * B ^ c)) (k : Fin (d * c)) :
    (digEquiv B c R d v).1 k = digF hB (v (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 := by
  have hc : (finProdFinEquiv.symm k).2.val < c := (finProdFinEquiv.symm k).2.isLt
  simp only [digEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.prodComm_apply,
    Prod.swap, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk, Equiv.piCongrRight_apply,
    Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, Equiv.curry_symm_apply,
    Function.uncurry]
  ext
  simp only [finFunctionFinEquiv_symm_apply_val, digF, finProdFinEquiv_symm_apply, Fin.modNat,
    Fin.val_mk]
  exact div_pow_mod_of_lt hB hc _

open Classical in
/-- **The digit count**: `|S|^t · B^(dc − t) · R^d` tuples have their first `t` digits in `S`. -/
theorem card_digits {B c R d t : ℕ} (hB : 0 < B) (ht : t ≤ d * c) (S : Finset (Fin B)) :
    (univ.filter fun v : Fin d → Fin (R * B ^ c) ↦ ∀ k : Fin (d * c), (k : ℕ) < t →
      (digEquiv B c R d v).1 k ∈ S).card = S.card ^ t * B ^ (d * c - t) * R ^ d := by
  rw [← Finset.card_map (digEquiv B c R d).toEmbedding]
  have : (univ.filter fun v : Fin d → Fin (R * B ^ c) ↦ ∀ k : Fin (d * c), (k : ℕ) < t →
      (digEquiv B c R d v).1 k ∈ S).map (digEquiv B c R d).toEmbedding =
      Fintype.piFinset (fun k : Fin (d * c) ↦ if (k : ℕ) < t then S else univ) ×ˢ univ := by
    ext ⟨H, r⟩
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, and_true, Fintype.mem_piFinset, Equiv.apply_symm_apply]
    refine forall_congr' fun k ↦ ?_
    split_ifs with hk <;> simp [hk]
  rw [this, Finset.card_product, Fintype.card_piFinset, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]
  simp only [apply_ite Finset.card, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (univ.filter fun k : Fin (d * c) ↦ (k : ℕ) < t).card = t := by
    rw [Fin.card_filter_val_lt]; omega
  have h2 : (univ.filter fun k : Fin (d * c) ↦ ¬ (k : ℕ) < t).card = d * c - t := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (d * c))))
      (fun k : Fin (d * c) ↦ (k : ℕ) < t)
    rw [Finset.card_univ, Fintype.card_fin, h1] at this
    omega
  rw [h1, h2]

/-! ## The deployed positions -/

/-- **The positions of a level** (FORMAT6 §5): position `k` is digit `k mod c` (base `2^h`) of the
number of draw `k / c`, `c = ⌊128/h⌋` positions per draw. -/
def posE2 (h c d t : ℕ) (hc : 0 < c) (ht : t ≤ d * c) (v : Fin d → E2) (k : Fin t) :
    Fin (2 ^ h) :=
  ⟨e2Nat (v ⟨k / c, (Nat.div_lt_iff_lt_mul hc).mpr (by have := k.isLt; omega)⟩) / (2 ^ h) ^ (k % c)
    % 2 ^ h, Nat.mod_lt _ (by positivity)⟩

open Classical in
/-- **The positions' count**: all `t` positions fall in `S` for at most `|E2|^d (|S|/2^h)^t` of the
draws' values, when `c·h ≤ 128` and `t ≤ d·c`. -/
theorem card_posE2 {h c d t : ℕ} (hc : 0 < c) (hch : c * h ≤ 128) (ht : t ≤ d * c)
    (S : Finset (Fin (2 ^ h))) :
    ((univ.filter fun v : Fin d → E2 ↦ ∀ k, posE2 h c d t hc ht v k ∈ S).card : ℝ≥0∞) ≤
      (Fintype.card E2 : ℝ≥0∞) ^ d * ((S.card : ℝ≥0∞) / (2 ^ h : ℕ)) ^ t := by
  have hB : 0 < 2 ^ h := by positivity
  have hRB : (2 ^ 64) ^ 2 = 2 ^ (128 - c * h) * (2 ^ h) ^ c := by
    rw [← pow_mul, ← pow_mul, ← pow_add, Nat.mul_comm h c]
    congr 1; omega
  let eqv : E2 ≃ Fin (2 ^ (128 - c * h) * (2 ^ h) ^ c) := e2NatEquiv.trans (finCongr hRB)
  have hv : ∀ y, (eqv y : ℕ) = e2Nat y := fun y ↦ by
    rw [Equiv.trans_apply, finCongr_apply, Fin.val_cast, e2NatEquiv_val]
  -- transport to numbers
  have hmap : (univ.filter fun v : Fin d → E2 ↦ ∀ k, posE2 h c d t hc ht v k ∈ S).map
      (Equiv.piCongrRight fun _ ↦ eqv).toEmbedding ⊆
      univ.filter fun w : Fin d → Fin (2 ^ (128 - c * h) * (2 ^ h) ^ c) ↦
        ∀ k : Fin (d * c), (k : ℕ) < t → (digEquiv (2 ^ h) c (2 ^ (128 - c * h)) d w).1 k ∈ S := by
    intro w hw
    rw [Finset.mem_map_equiv, Finset.mem_filter] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro k hk
    have hkp := hw.2 ⟨k, hk⟩
    rw [digEquiv_fst hB]
    convert hkp using 1
    simp only [posE2, digF, Equiv.piCongrRight_symm_apply, finProdFinEquiv_symm_apply,
      Fin.divNat, Fin.modNat]
    congr 2
    rw [← hv, Pi.map_apply, Equiv.apply_symm_apply]
  have hcard := (Finset.card_le_card hmap).trans_eq
    (card_digits (R := 2 ^ (128 - c * h)) hB ht S)
  rw [Finset.card_map] at hcard
  have hB0 : ((2 ^ h : ℕ) : ℝ≥0∞) ≠ 0 := by simp
  have hBt : ((2 ^ h : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
  have hsplit : ((2 ^ h : ℕ) : ℝ≥0∞) ^ (c * d) =
      ((2 ^ h : ℕ) : ℝ≥0∞) ^ (d * c - t) * ((2 ^ h : ℕ) : ℝ≥0∞) ^ t := by
    rw [← pow_add, mul_comm c d, Nat.sub_add_cancel ht]
  have hinv : ((2 ^ h : ℕ) : ℝ≥0∞) ^ t * (((2 ^ h : ℕ) : ℝ≥0∞)⁻¹) ^ t = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel hB0 hBt, one_pow]
  have hE : (Fintype.card E2 : ℝ≥0∞) = ((2 ^ (128 - c * h) : ℕ) : ℝ≥0∞) * ((2 ^ h : ℕ) : ℝ≥0∞) ^ c := by
    rw [card_E2, show (2 ^ 128 : ℕ) = 2 ^ (128 - c * h) * (2 ^ h) ^ c by rw [← hRB]; norm_num]
    push_cast; ring
  calc ((univ.filter fun v : Fin d → E2 ↦ ∀ k, posE2 h c d t hc ht v k ∈ S).card : ℝ≥0∞)
      ≤ ((S.card ^ t * (2 ^ h) ^ (d * c - t) * (2 ^ (128 - c * h)) ^ d : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hcard
    _ = (S.card : ℝ≥0∞) ^ t * ((2 ^ h : ℕ) : ℝ≥0∞) ^ (d * c - t) *
          ((2 ^ (128 - c * h) : ℕ) : ℝ≥0∞) ^ d *
          (((2 ^ h : ℕ) : ℝ≥0∞) ^ t * (((2 ^ h : ℕ) : ℝ≥0∞)⁻¹) ^ t) := by
        rw [hinv, mul_one]; push_cast; ring
    _ = (((2 ^ (128 - c * h) : ℕ) : ℝ≥0∞) * ((2 ^ h : ℕ) : ℝ≥0∞) ^ c) ^ d *
          ((S.card : ℝ≥0∞) * ((2 ^ h : ℕ) : ℝ≥0∞)⁻¹) ^ t := by
        rw [mul_pow, mul_pow, ← pow_mul, hsplit]; ring
    _ = (Fintype.card E2 : ℝ≥0∞) ^ d * ((S.card : ℝ≥0∞) / ((2 ^ h : ℕ) : ℝ≥0∞)) ^ t := by
        rw [hE, div_eq_mul_inv]

end Lvm6.Whir
