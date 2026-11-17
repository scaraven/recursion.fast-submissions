-- New for lvm2 roll 7 (WP E2-S, phase G0). In-challenge grinding on an `E2` group (ARCH-7 §2.2,
-- PI-GRIND's `powOK` in lane 2) and the per-group soundness table at the frozen `max_group`.
import LvmFieldE2
import LvmWhirLevelMidSpec
import LvmFrontMech

/-!
# Grinding twins for the `E2` front

Every challenge is still one uniform `E` answer (24 bytes, three `K` lanes). An `E2` group reads
its challenge from lanes 0–1 (`e2OfE`) and accepts only if PI-GRIND's `powOK g c`
(`eToNat c < 2^(192 − g)`), which for `g ≤ 64` is "lane 2 `< 2^(64 − g)`" (`powOK_iff_lane2`).

* **`card_powOK_prod`** (the product-set lemma): for any set `P` of `E2` challenges,
  `#{c : E | powOK g c ∧ e2OfE c ∈ P} = |P| · 2^(64 − g)`: the accepted bad answers form the
  product set `P × [0, 2^(64−g))` under `E ≃ E2 × K` (`eSplit`).
* `avgE_powOK_prod`: the same as a probability, `2^-g · |P| / 2^128`.
* **`sz_escape_grind`**: the grinding twin of `sz_escape`: a nonzero `E2` polynomial of degree
  `≤ d` vanishes at an accepted challenge with probability `≤ 2^-g · d / 2^128`.

**The per-group table** (`grpEps L₀ c g = L₀ · c / 2^(128 + g)`, `L₀` the doom's candidate count,
`epsS = 7·2^-131` the frozen `max_group` of `kcertSJ`, `= Lvm.ASM.εS`):
* `table_arch7`: ARCH-7's `g = 1, 2, 3, 7` for `c = 1, 2, 3, 46` give `≤ 2^-129` at `L₀ = 1`;
* `table_min`: NOTE-FIELD's minimum `g = 1, 2, 2, 6` gives `≤ epsS` at `L₀ = 1` (not `≤ 2^-129` for
  `c = 3, 46`);
* **`table_cand_fails`**: at the certificate's current `L₀ = 98·304 = 29,792` (`candPairsJ_ncard_le`,
  `LkSJ`) none of ARCH-7's rows is `≤ epsS`;
* `table_cand_least`: there the least `g` with `≤ epsS` is `16, 17, 17, 21`.
-/

set_option autoImplicit false

namespace LeanVM.Parameters

open Finset LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open scoped ENNReal

/-! ## The `E2` challenge inside an `E` answer -/

/-- **The `E2` challenge** of an answer: lanes 0 and 1. -/
def e2OfE (c : E) : E2 := ⟨c.limb 0, c.limb 1⟩

/-- `E ≃ E2 × K`: lanes 0–1 and lane 2. -/
def eSplit : E ≃ E2 × K where
  toFun c := (e2OfE c, c.limb 2)
  invFun p := E.ofLimbs p.1.re p.1.im p.2
  left_inv c := E.ext fun i ↦ by fin_cases i <;> simp [e2OfE]
  right_inv p := by
    obtain ⟨⟨a, b⟩, c⟩ := p
    simp [e2OfE]

theorem kToNat_lt (a : K) : kToNat a < 2 ^ 64 := a.toBitVec.isLt

/-- For `g ≤ 64`, `powOK g c` is "lane 2 `< 2^(64 − g)`". -/
theorem powOK_iff_lane2 {g : ℕ} (hg : g ≤ 64) (c : E) :
    powOK g c ↔ kToNat (c.limb 2) < 2 ^ (64 - g) := by
  have hlow : kToNat (c.limb 0) + 2 ^ 64 * kToNat (c.limb 1) < 2 ^ 128 := by
    have h0 := kToNat_lt (c.limb 0)
    have h1 := kToNat_lt (c.limb 1)
    have : 2 ^ 64 * kToNat (c.limb 1) ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by (clear * - c g h1; omega))
    (clear * - c g h0 h1; omega)
  have hsplit : 2 ^ (192 - g) = 2 ^ 128 * 2 ^ (64 - g) := by
    rw [← pow_add]
    congr 1
    (clear * - g hg c; omega)
  rw [powOK, eToNat, hsplit]
  set L := kToNat (c.limb 0) + 2 ^ 64 * kToNat (c.limb 1)
  set h := kToNat (c.limb 2)
  constructor
  · intro hl
    by_contra hh
    have : 2 ^ 128 * 2 ^ (64 - g) ≤ 2 ^ 128 * h := Nat.mul_le_mul_left _ (not_lt.mp hh)
    (clear * - g c hlow hl hh; omega)
  · intro hh
    have : 2 ^ 128 * (h + 1) ≤ 2 ^ 128 * 2 ^ (64 - g) := Nat.mul_le_mul_left _ hh
    rw [Nat.mul_succ] at this
    (clear * - L h g c hlow hh; omega)

/-- `2^k` words of `K` lie below `2^k`. -/
theorem card_kToNat_lt {k : ℕ} (hk : k ≤ 64) :
    (univ.filter fun a : K ↦ kToNat a < 2 ^ k).card = 2 ^ k := by
  have h1 : (univ.filter fun a : K ↦ kToNat a < 2 ^ k).card =
      (univ.filter fun x : Fin (2 ^ 64) ↦ (x : ℕ) < 2 ^ k).card := by
    rw [← Finset.card_map BF64.equivFin.toEmbedding]
    congr 1
    ext x
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [h1, Fin.card_filter_val_lt]
  exact min_eq_right (Nat.pow_le_pow_right (by norm_num) hk)

/-- **The product-set lemma**: the accepted answers whose `E2` challenge lies in `P` are
`|P| · 2^(64 − g)`. -/
theorem card_powOK_prod {g : ℕ} (hg : g ≤ 64) (P : E2 → Prop) [DecidablePred P] :
    (univ.filter fun c : E ↦ powOK g c ∧ P (e2OfE c)).card =
      (univ.filter P).card * 2 ^ (64 - g) := by
  rw [← card_kToNat_lt (k := 64 - g) (by (clear * - g hg; omega)), ← Finset.card_product, ← Finset.card_map eSplit.toEmbedding]
  congr 1
  ext ⟨y, a⟩
  simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [powOK_iff_lane2 hg]
  simp only [eSplit, Equiv.coe_fn_symm_mk]
  have h0 : (E.ofLimbs y.re y.im a).limb 2 = a := by simp
  have h1 : e2OfE (E.ofLimbs y.re y.im a) = y := by
    simp only [e2OfE, limb_ofLimbs]
    rfl
  rw [h0, h1, and_comm]

/-- **The product-set lemma as a probability**: `2^-g · |P| / 2^128`. -/
theorem avgE_powOK_prod {g : ℕ} (hg : g ≤ 64) (P : E2 → Prop) [DecidablePred P] :
    avgE (fun c ↦ indE (powOK g c ∧ P (e2OfE c))) =
      (2 : ℝ≥0∞)⁻¹ ^ g * ((univ.filter P).card * ((2 : ℝ≥0∞) ^ 128)⁻¹) := by
  have h : (2 : ℝ≥0∞) ^ 192 = 2 ^ g * 2 ^ 128 * 2 ^ (64 - g) := by
    rw [← pow_add, ← pow_add]
    congr 1
    (clear * - g hg; omega)
  rw [← card_filter_eq_avgE, card_powOK_prod hg, card_E, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, h, ENNReal.mul_inv (by simp) (by simp), ENNReal.mul_inv (by simp) (by simp),
    ENNReal.inv_pow]
  have h2 : ((2 : ℝ≥0∞) ^ (64 - g))⁻¹ * 2 ^ (64 - g) = 1 :=
    ENNReal.inv_mul_cancel (by simp) (by simp)
  calc (2 : ℝ≥0∞)⁻¹ ^ g * (2 ^ 128)⁻¹ * (2 ^ (64 - g))⁻¹ * ((univ.filter P).card * 2 ^ (64 - g))
      = (2 : ℝ≥0∞)⁻¹ ^ g * (2 ^ 128)⁻¹ * (univ.filter P).card *
          ((2 ^ (64 - g))⁻¹ * 2 ^ (64 - g)) := by ring
    _ = _ := by rw [h2]; ring

open Polynomial in
/-- **The grinding twin of `sz_escape`**: a nonzero `E2` polynomial of degree `≤ d` vanishes at
an accepted challenge with probability at most `2^-g · d / 2^128`. This is the joint probability
(accepted and bad) over all of `E`, the quantity a group's escape charges; it is not conditional on
acceptance. -/
theorem sz_escape_grind {g : ℕ} (hg : g ≤ 64) {p : E2[X]} (hp : p ≠ 0) {d : ℕ}
    (hd : p.natDegree ≤ d) :
    avgE (fun c ↦ indE (powOK g c ∧ p.eval (e2OfE c) = 0)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ g * (d * ((2 : ℝ≥0∞) ^ 128)⁻¹) := by
  classical
  rw [avgE_powOK_prod hg (fun y ↦ p.eval y = 0)]
  gcongr
  have hsub : (univ.filter fun y : E2 ↦ p.eval y = 0) ⊆ p.roots.toFinset := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact Multiset.mem_toFinset.mpr ((mem_roots hp).mpr hy)
  exact_mod_cast ((Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)).trans
    ((card_roots' p).trans hd)

/-! ## The per-group table at the frozen `max_group` -/

/-- A group's per-query bound: `L₀` candidates, numerator `c`, `g` grinding bits, over `|E2|`. -/
def grpEps (L₀ c g : ℕ) : ℚ := L₀ * c / 2 ^ (128 + g)

/-- The frozen `max_group`: `kcertSJ`'s `εI = εS = 7·2^-131` (`LvmCertSKJ`, `LvmCertSOpen.εS`). -/
def epsS : ℚ := 7 / 2 ^ 131

/-- ARCH-7 §2.2's column (`g = 1, 2, 3, 7`): every row `≤ 2^-129` with one candidate. -/
theorem table_arch7 :
    grpEps 1 1 1 ≤ 1 / 2 ^ 129 ∧ grpEps 1 2 2 ≤ 1 / 2 ^ 129 ∧ grpEps 1 3 3 ≤ 1 / 2 ^ 129 ∧
      grpEps 1 46 7 ≤ 1 / 2 ^ 129 := by
  unfold grpEps
  norm_num

/-- With one candidate every ARCH-7 row is `≤ epsS`, and so is NOTE-FIELD's minimum
(`g = 1, 2, 2, 6`), which is not `≤ 2^-129` for `c = 3` and `c = 46`. -/
theorem table_min :
    (grpEps 1 1 1 ≤ epsS ∧ grpEps 1 2 2 ≤ epsS ∧ grpEps 1 3 3 ≤ epsS ∧ grpEps 1 46 7 ≤ epsS) ∧
    (grpEps 1 1 1 ≤ epsS ∧ grpEps 1 2 2 ≤ epsS ∧ grpEps 1 3 2 ≤ epsS ∧ grpEps 1 46 6 ≤ epsS) ∧
    (¬ grpEps 1 3 2 ≤ 1 / 2 ^ 129 ∧ ¬ grpEps 1 46 6 ≤ 1 / 2 ^ 129) := by
  unfold grpEps epsS
  norm_num

/-- **At the certificate's candidate count `L₀ = 98·304`** (the middle phases' `Doomed candPairs`,
`LkSJ`), none of ARCH-7's rows is `≤ epsS`. -/
theorem table_cand_fails :
    ¬ grpEps 29792 1 1 ≤ epsS ∧ ¬ grpEps 29792 2 2 ≤ epsS ∧ ¬ grpEps 29792 3 3 ≤ epsS ∧
      ¬ grpEps 29792 46 7 ≤ epsS := by
  unfold grpEps epsS
  norm_num

/-- At `L₀ = 98·304` the least grinding with `≤ epsS` is `g = 16, 17, 17, 21`. -/
theorem table_cand_least :
    (grpEps 29792 1 16 ≤ epsS ∧ ¬ grpEps 29792 1 15 ≤ epsS) ∧
    (grpEps 29792 2 17 ≤ epsS ∧ ¬ grpEps 29792 2 16 ≤ epsS) ∧
    (grpEps 29792 3 17 ≤ epsS ∧ ¬ grpEps 29792 3 16 ≤ epsS) ∧
    (grpEps 29792 46 21 ≤ epsS ∧ ¬ grpEps 29792 46 20 ≤ epsS) := by
  unfold grpEps epsS
  norm_num

/-- A group's bound in the certificate's units: `L₀` candidates times `sz_escape_grind`'s bound. -/
noncomputable def grpEpsE (L₀ c g : ℕ) : ℝ≥0∞ := L₀ * ((2 : ℝ≥0∞)⁻¹ ^ g * (c * ((2 : ℝ≥0∞) ^ 128)⁻¹))

theorem grpEpsE_eq (L₀ c g : ℕ) :
    grpEpsE L₀ c g = ENNReal.ofReal (grpEps L₀ c g) := by
  rw [grpEpsE, grpEps]
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, pow_add, div_eq_mul_inv,
    ENNReal.mul_inv (by simp) (by simp), ENNReal.inv_pow, ENNReal.inv_pow]
  ring

/-- `epsS` is `εS = 7·2^-131` (`LvmCertSOpen.εS`) in the certificate's units. -/
theorem epsS_eq : (7 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 131 = ENNReal.ofReal epsS := by
  rw [epsS]
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat, div_eq_mul_inv, ENNReal.inv_pow]

/-- **ARCH-7's rows at `εS`, in the certificate's units** (one candidate): every `E2` group's
`sz_escape_grind` bound is `≤ εS`. -/
theorem table_arch7_εS :
    grpEpsE 1 1 1 ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 ∧ grpEpsE 1 2 2 ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 ∧
      grpEpsE 1 3 3 ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 ∧ grpEpsE 1 46 7 ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  simp only [grpEpsE_eq, epsS_eq]
  obtain ⟨h1, h2, h3, h4⟩ := (table_min).1
  exact ⟨ENNReal.ofReal_le_ofReal (by exact_mod_cast h1), ENNReal.ofReal_le_ofReal (by exact_mod_cast h2),
    ENNReal.ofReal_le_ofReal (by exact_mod_cast h3), ENNReal.ofReal_le_ofReal (by exact_mod_cast h4)⟩

end LeanVM.Parameters
