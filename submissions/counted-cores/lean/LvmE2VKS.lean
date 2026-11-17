-- New for lvm2 S1 (E2-F, E2F-V), E2AC-DES §6 statement 7 (`ksSpecE2`, `ksLinkSpecE2`): the `KS` phase (the
-- Keccak reduction with all 25 lanes tied, `12 × 2`) and the `KS` sponge link at `E2`. Kept in its own module:
-- under the 24 h rule KS may stay at `E3` (S2GF `--no-ks`), and then this module leaves the build.
import LvmE2VSpecTape
import LvmE2VProgKS
import LvmKeccakCallerPhases
import LvmE2VZero
import LvmE2VKec

/-!
# `KS` and its link at `E2`

Programs (S2GF phases KS, KSlink; `E3` originals in parentheses):
* `verifyKeccakE2` (`verifyKeccak`): segment and lane coordinates (`c = 1`), the committed segment
  outputs, twelve layers of `Shape.v1`, the outputs' opening (slot rounds `c = 2`, the word), the
  inputs' opening (pack and slot rounds `c = 2`, 64 slices);
* `callerProgE2` (`callerProg`): `h` instance coordinates (`c = 1`), 25 scalars, `verifyKeccakE2`,
  the row switch on the slices;
* `ksLinkProgE2` (`ksLinkProg`): `hk + 5` coordinates `ρ, λ` (`c = 1`), `hk` shift rounds (`c = 2`),
  four scalars, the check.

Statements, at `L₀ = 1` and `εS`:
* **`ksSpecE2`** (7): from doom of `RegionValid`, `OutRel` (all 25 lanes) and `R` to doom of the
  row claim on the `KS` column, the committed outputs' `E2` word claims, the tied lanes' `E2` word
  claims at `r`, and `R`;
* **`ksLinkSpecE2`** (7): from doom of the sponge link and `R` to doom of the four combined claims
  at `ρ'` (`KsClaimsE2`) and `R`.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (RegionValid inState laneWord errE)
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open Lvm.KG (OutRel SpongeLink ksMsg ksSplitN)
open Lvm.ASM (εS)
open Finset
open scoped ENNReal

/-! ## The claims at `E2` -/

/-- A column claim on the `KS` column holds (`colTrue`): its multilinear extension at the point. -/
def colTrueE2 (h : ℕ) (col : ℕ → K) (c : ColClaimE2) : Prop :=
  c.column = qkeccak ∧ c.point.length = h + 6 ∧ c.value = stepMleF (h + 6) c.point col

/-- The tied lanes' word claims at `r` (`TiedTrue`). -/
def TiedTrueE2 (h nt : ℕ) (Y : ℕ → ℕ → K) (r v : List E2) : Prop :=
  ∀ l < nt, stepMleF h r (Y l) = v.getD l 0

/-- The claims the `KS` caller leaves (`CallerClaims`). -/
def CallerClaimsE2 (h nt : ℕ) (qk : ℕ → K) (Y : ℕ → ℕ → K) (co : CallerOutE2) : Prop :=
  RowColTrue (h + 6) qk co.2.2.2 ∧ (∀ c ∈ co.2.2.1.1, colTrueE2 h qk c) ∧ TiedTrueE2 h nt Y co.1 co.2.1

/-- **The four combined claims** at `ρ'` (`KsClaims`). -/
def KsClaimsE2 (hk xl : ℕ) (ks : ℕ → K) (Y M X : ℕ → ℕ → K) (lam rho' vals : List E2) : Prop :=
  vals.getD 0 0 = ∑ l ∈ range 25, eqAtF lam l * stepMleF hk rho' (fun x ↦ Y x l) ∧
  vals.getD 1 0 = ∑ l ∈ range 25, eqAtF lam l * stepMleF hk rho' (fun x ↦ ks (x + 2 ^ hk * l)) ∧
  vals.getD 2 0 = ∑ l ∈ range 17, eqAtF lam l *
    ∑ x ∈ range (ksSplitN hk xl), eqAtF rho' x * kF (M x l) ∧
  vals.getD 3 0 = ∑ l ∈ range 17, eqAtF lam l * stepMleF xl (rho'.take xl) (fun x ↦ X x l)

/-! ## The `KS` link's algebra over `F` (`LvmSpongeTableLink`) -/

section KSAlg

variable {F : Type} [Field F] [Algebra K F] [CharP F 2]

omit [Algebra K F] [CharP F 2] in
theorem prodF_eq_prod (l : List F) : prodF l = l.prod := by
  unfold prodF; rw [List.prod_eq_foldl]

omit [Algebra K F] [CharP F 2] in
theorem eqEvalF_nil : eqEvalF ([] : List F) [] = 1 := rfl

omit [Algebra K F] [CharP F 2] in
theorem eqEvalF_cons (a b : F) (x y : List F) :
    eqEvalF (a :: x) (b :: y) = (1 + a + b) * eqEvalF x y := by
  unfold eqEvalF
  rw [List.zipWith_cons_cons, ← List.prod_eq_foldl, ← List.prod_eq_foldl, List.prod_cons]

omit [Algebra K F] [CharP F 2] in
theorem eqAtF_even (r : F) (rs : List F) (w : ℕ) : eqAtF (r :: rs) (2 * w) = (1 + r) * eqAtF rs w := by
  rw [eqAtF_succ, if_neg (by omega), show 2 * w / 2 = w by omega]

omit [Algebra K F] [CharP F 2] in
theorem eqAtF_odd (r : F) (rs : List F) (w : ℕ) : eqAtF (r :: rs) (2 * w + 1) = r * eqAtF rs w := by
  rw [eqAtF_succ, if_pos (by omega), show (2 * w + 1) / 2 = w by omega]

omit [Algebra K F] in
/-- **The equality weights pair to `eqEvalF`** (`sum_eqAt_mul_eqAt`). -/
theorem sum_eqAtF_mul_eqAtF : ∀ (x y : List F), x.length = y.length →
    ∑ w ∈ range (2 ^ x.length), eqAtF x w * eqAtF y w = eqEvalF x y
  | [], [], _ => by simp [eqEvalF]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: x, b :: y, h => by
    simp only [List.length_cons, add_left_inj] at h
    rw [List.length_cons, sum_cube_succW, eqEvalF_cons, ← sum_eqAtF_mul_eqAtF x y h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [eqAtF_even, eqAtF_even, eqAtF_odd, eqAtF_odd]
    linear_combination (a * b * (eqAtF x w * eqAtF y w)) * CharTwo.two_eq_zero (R := F)

/-- The shifted continuation kernel on the cube (`scK`). -/
def scKF (rows : List ℕ) (rho : List F) (k : ℕ) : F := if k + 1 ∈ rows then eqAtF rho (k + 1) else 0

omit [Algebra K F] [CharP F 2] in
/-- **`contShiftF` is the shifted kernel's extension** (`contShiftE_eq`). -/
theorem contShiftF_eq (n : ℕ) {rows : List ℕ} (hnd : rows.Nodup)
    (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ n) (rho rho' : List F) :
    contShiftF rows rho rho' = ∑ k ∈ range (2 ^ n), eqAtF rho' k * scKF rows rho k := by
  classical
  rw [contShiftF, sumF_eq_sum, ← List.sum_toFinset _ hnd]
  simp only [scKF, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun i ↦ i - 1) (fun k ↦ k + 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have := hrows i (List.mem_toFinset.1 hi)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [show i - 1 + 1 = i by omega]; exact List.mem_toFinset.1 hi⟩
  · intro k hk
    simp only [Finset.mem_filter] at hk
    exact List.mem_toFinset.2 hk.2
  · intro i hi
    have := hrows i (List.mem_toFinset.1 hi)
    omega
  · intro k _
    simp
  · intro i hi
    have := hrows i (List.mem_toFinset.1 hi)
    simp only [show i - 1 + 1 = i by omega]
    ring

variable (hk xl : ℕ) (rows : List ℕ) (ks : ℕ → K) (Y M X : ℕ → ℕ → K) (lam : List F)

/-- The sponge link's zero-test table on `hk + 5` bits at `F` (`ksDelta`): row low, lane high. -/
def ksDeltaF (w : ℕ) : F :=
  if w / 2 ^ hk < 25 then
    kF (ks (w % 2 ^ hk + 2 ^ hk * (w / 2 ^ hk))) +
      (if w % 2 ^ hk ∈ rows then kF (Y (w % 2 ^ hk - 1) (w / 2 ^ hk)) else 0) +
      (if w / 2 ^ hk < 17 then kF (ksMsg (ksSplitN hk xl) M X (w % 2 ^ hk) (w / 2 ^ hk)) else 0)
  else 0

omit [Algebra K F] in
theorem char2_sum3F {a b c : F} (h : a + b + c = 0) : a = b + c := by
  linear_combination h - (b + c) * CharTwo.two_eq_zero (R := F)

/-- A vanishing table is the sponge link (`spongeLink_of_zero`). -/
theorem spongeLink_of_zeroF (hz : ZeroOnF (ksDeltaF (F := F) hk xl rows ks Y M X) [] (hk + 5)) :
    SpongeLink hk rows ks Y (ksMsg (ksSplitN hk xl) M X) := by
  rw [zeroOnF_nil] at hz
  intro i hi l hl
  have := hz (i + 2 ^ hk * l) (by
    have : 2 ^ (hk + 5) = 2 ^ hk * 32 := by rw [pow_add]; rfl
    nlinarith)
  simp only [ksDeltaF, Lvm.KG.idx_div hk hi, Lvm.KG.idx_mod hk hi, if_pos hl] at this
  apply (algebraMap K F).injective
  rw [map_add, apply_ite (algebraMap K F), apply_ite (algebraMap K F), map_zero]
  exact char2_sum3F this

/-- `Y_ω(k)` (`yOm`). -/
def yOmF (k : ℕ) : F := ∑ l ∈ range 25, eqAtF lam l * kF (Y k l)
/-- `in_ω(k)` (`inOm`). -/
def inOmF (k : ℕ) : F := ∑ l ∈ range 25, eqAtF lam l * kF (ks (k + 2 ^ hk * l))
/-- `Msg_ω(k)` (`msgOm`). -/
def msgOmF (k : ℕ) : F := ∑ l ∈ range 17, eqAtF lam l * kF (ksMsg (ksSplitN hk xl) M X k l)

/-- The `KS` link sumcheck's family at `F` (`Fks`). -/
def FksF (rho acc : List F) : F :=
  cubeSumF (fun pt ↦ (∑ k ∈ range (2 ^ hk), eqAtF pt k * scKF rows rho k) *
      (∑ k ∈ range (2 ^ hk), eqAtF pt k * yOmF Y lam k) +
    (∑ k ∈ range (2 ^ hk), eqAtF pt k * eqAtF rho k) *
      (∑ k ∈ range (2 ^ hk), eqAtF pt k * (inOmF hk ks lam k + msgOmF hk xl M X lam k))) hk acc

omit [CharP F 2] in
theorem FksF_plain {β : Type} (kq : β → ℕ → K) (Yq Mq Xq : β → ℕ → ℕ → K) (rho : List F) :
    PlainFamilyF (fun q acc ↦ FksF hk xl rows (kq q) (Yq q) (Mq q) (Xq q) lam rho acc) 2 hk :=
  cube_plainFamilyF _ hk fun _ pre post ↦ PolyLEF.add (polyLEF_mle_mul _ _ _ _ pre post)
    (polyLEF_mle_mul _ _ _ _ pre post)

omit [CharP F 2] in
/-- One row of the table, its lanes combined by `eq(λ, ·)` (`ksDelta_row`). -/
theorem ksDeltaF_row (hl : lam.length = 5) {x : ℕ} (hx : x < 2 ^ hk) :
    ∑ o ∈ range (2 ^ lam.length), eqAtF lam o * ksDeltaF hk xl rows ks Y M X (x + 2 ^ hk * o) =
      inOmF hk ks lam x + (if x ∈ rows then yOmF Y lam (x - 1) else 0) + msgOmF hk xl M X lam x := by
  rw [hl, show (2 : ℕ) ^ 5 = 25 + 7 from rfl, Finset.sum_range_add]
  have h7 : ∑ o ∈ range 7, eqAtF lam (25 + o) * ksDeltaF hk xl rows ks Y M X (x + 2 ^ hk * (25 + o)) =
      0 := by
    refine Finset.sum_eq_zero fun o _ ↦ ?_
    rw [ksDeltaF, Lvm.KG.idx_div hk hx, if_neg (by omega), mul_zero]
  rw [h7, add_zero]
  have e : ∀ o ∈ range 25, eqAtF lam o * ksDeltaF hk xl rows ks Y M X (x + 2 ^ hk * o) =
      eqAtF lam o * kF (ks (x + 2 ^ hk * o)) +
        ((if x ∈ rows then eqAtF lam o * kF (Y (x - 1) o) else 0) +
          (if o < 17 then eqAtF lam o * kF (ksMsg (ksSplitN hk xl) M X x o) else 0)) := by
    intro o ho
    rw [ksDeltaF, Lvm.KG.idx_div hk hx, Lvm.KG.idx_mod hk hx, if_pos (Finset.mem_range.1 ho),
      mul_add, mul_add, mul_ite, mul_ite, mul_zero, add_assoc]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hY : ∑ o ∈ range 25, (if x ∈ rows then eqAtF lam o * kF (Y (x - 1) o) else 0) =
      if x ∈ rows then yOmF Y lam (x - 1) else 0 := by
    split_ifs <;> simp [yOmF]
  have hM : ∑ o ∈ range 25, (if o < 17 then eqAtF lam o * kF (ksMsg (ksSplitN hk xl) M X x o) else 0) =
      msgOmF hk xl M X lam x := by
    rw [show 25 = 17 + 8 from rfl, Finset.sum_range_add, msgOmF,
      Finset.sum_eq_zero (s := range 8) fun o _ ↦ if_neg (by omega), add_zero]
    exact Finset.sum_congr rfl fun o ho ↦ if_pos (Finset.mem_range.1 ho)
  rw [hY, hM, inOmF, add_assoc]

/-- **The zero test at `(ρ, λ)` is the claim `0`** (`ks_zero_of_claim`). -/
theorem ks_zero_of_claimF (h0 : 0 ∉ rows) (hrows : ∀ i ∈ rows, i < 2 ^ hk) {kchal : List F}
    (hc : kchal.length = hk + 5)
    (H : (0 : F) = FksF hk xl rows ks Y M X (kchal.drop hk) (kchal.take hk) []) :
    ZeroOnF (ksDeltaF hk xl rows ks Y M X) kchal (hk + 5) := by
  have hr : (kchal.take hk).length = hk := by simp [hc]
  have hl : (kchal.drop hk).length = 5 := by simp [hc]
  set ρ := kchal.take hk with hρ
  set lm := kchal.drop hk with hlm
  rw [zeroOnF_full _ hc]
  have hsplit : kchal = ρ ++ lm := (List.take_append_drop hk kchal).symm
  have e1 : ∑ w ∈ range (2 ^ (hk + 5)), eqAtF kchal w * ksDeltaF hk xl rows ks Y M X w =
      ∑ x ∈ range (2 ^ hk), eqAtF ρ x *
        (inOmF hk ks lm x + (if x ∈ rows then yOmF Y lm (x - 1) else 0) + msgOmF hk xl M X lm x) := by
    conv_lhs => rw [hsplit]
    rw [show hk + 5 = hk + lm.length by rw [hl], col_splitF hr]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [← ksDeltaF_row hk xl rows ks Y M X lm hl (Finset.mem_range.1 hx), Finset.mul_sum]
    exact Finset.sum_congr rfl fun o _ ↦ by ring
  rw [e1]
  refine Eq.trans ?_ H.symm
  rw [FksF, cubeSumF_nil]
  have hcube : ∀ u ∈ range (2 ^ hk),
      (∑ k ∈ range (2 ^ hk), eqAtF (bitsF u hk : List F) k * scKF rows ρ k) *
        (∑ k ∈ range (2 ^ hk), eqAtF (bitsF u hk : List F) k * yOmF Y lm k) +
      (∑ k ∈ range (2 ^ hk), eqAtF (bitsF u hk : List F) k * eqAtF ρ k) *
        (∑ k ∈ range (2 ^ hk), eqAtF (bitsF u hk : List F) k * (inOmF hk ks lm k + msgOmF hk xl M X lm k)) =
      scKF rows ρ u * yOmF Y lm u + eqAtF ρ u * (inOmF hk ks lm u + msgOmF hk xl M X lm u) := by
    intro u hu
    have hu' := Finset.mem_range.1 hu
    rw [sum_eqAtF_bitsF hu', sum_eqAtF_bitsF hu', sum_eqAtF_bitsF hu', sum_eqAtF_bitsF hu']
  rw [Finset.sum_congr rfl hcube, Finset.sum_add_distrib]
  have hp := Nat.two_pow_pos hk
  obtain ⟨Mk, hMk⟩ : ∃ Mk, 2 ^ hk = Mk + 1 := ⟨2 ^ hk - 1, by omega⟩
  have hshift : ∑ u ∈ range (2 ^ hk), scKF rows ρ u * yOmF Y lm u =
      ∑ x ∈ range (2 ^ hk), eqAtF ρ x * (if x ∈ rows then yOmF Y lm (x - 1) else 0) := by
    rw [hMk, Finset.sum_range_succ, Finset.sum_range_succ']
    have hlast : Mk + 1 ∉ rows := fun hm ↦ by have := hrows _ hm; omega
    simp only [scKF, hlast, ite_false, zero_mul, add_zero, h0, mul_zero, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs <;> simp
  rw [hshift, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

omit [Algebra K F] [CharP F 2] in
/-- `eq` at the all-ones index of a point is the product of its coordinates (`eqAt_ones`). -/
theorem eqAtF_ones : ∀ pt : List F, eqAtF pt (2 ^ pt.length - 1) = pt.prod
  | [] => by simp
  | r :: rs => by
    have h1 : 1 ≤ 2 ^ rs.length := Nat.one_le_two_pow
    have hm : (2 ^ rs.length * 2 - 1) % 2 = 1 := by omega
    have hd : (2 ^ rs.length * 2 - 1) / 2 = 2 ^ rs.length - 1 := by omega
    rw [eqAtF_succ, List.length_cons, List.prod_cons, pow_succ, hm, hd, eqAtF_ones rs, if_pos rfl]

omit [Algebra K F] [CharP F 2] in
/-- **A row from the split** (`eqAt_split`). -/
theorem eqAtF_split {hk xl : ℕ} (hxl : xl ≤ hk) {pt : List F} (hpt : pt.length = hk) {j : ℕ}
    (hj : j < 2 ^ xl) : eqAtF pt (ksSplitN hk xl + j) = eqAtF (pt.take xl) j * selXF xl pt := by
  have hd : (pt.drop xl).length = hk - xl := by simp [hpt]
  have ht : (pt.take xl).length = xl := by simp [hpt]; omega
  have hp : 2 ^ hk = 2 ^ xl * 2 ^ (hk - xl) := by rw [← pow_add]; congr 1; omega
  have h1 : 1 ≤ 2 ^ (hk - xl) := Nat.one_le_two_pow
  have hw : ksSplitN hk xl + j = j + 2 ^ xl * (2 ^ (hk - xl) - 1) := by
    have e := Lvm.KG.ksSplitN_add hxl
    rw [hp] at e
    rw [Nat.mul_sub_one]
    have : 2 ^ xl ≤ 2 ^ xl * 2 ^ (hk - xl) := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  conv_lhs => rw [← List.take_append_drop xl pt]
  rw [eqAtF_append, ht, hw, eqAtF_mod (pt.take xl), ht, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hj, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hj, zero_add,
    ← hd, eqAtF_ones, selXF, prodF_eq_prod]

omit [CharP F 2] in
/-- **The messages split at `2^hk − 2^xl`** (`msgOm_mle`). -/
theorem msgOmF_mle (hxl : xl ≤ hk) {pt : List F} (hpt : pt.length = hk) :
    ∑ k ∈ range (2 ^ hk), eqAtF pt k * msgOmF hk xl M X lam k =
      ∑ x ∈ range (ksSplitN hk xl), eqAtF pt x * ∑ l ∈ range 17, eqAtF lam l * kF (M x l) +
        selXF xl pt * ∑ x ∈ range (2 ^ xl), eqAtF (pt.take xl) x *
          ∑ l ∈ range 17, eqAtF lam l * kF (X x l) := by
  rw [show range (2 ^ hk) = range (ksSplitN hk xl + 2 ^ xl) by rw [Lvm.KG.ksSplitN_add hxl],
    Finset.sum_range_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [msgOmF, ksMsg, if_pos (Finset.mem_range.1 hx)]
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.1 hj
    simp only [msgOmF, ksMsg, if_neg (show ¬ ksSplitN hk xl + j < ksSplitN hk xl by omega),
      Nat.add_sub_cancel_left, eqAtF_split hxl hpt hj']
    ring

/-- **The `KS` link sumcheck's end** at `ρ'`, in V_S's closed forms (`Fks_end`). -/
theorem FksF_end (hxl : xl ≤ hk) (hnd : rows.Nodup) (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ hk)
    {rho pt : List F} (hr : rho.length = hk) (hpt : pt.length = hk) :
    FksF hk xl rows ks Y M X lam rho pt =
      contShiftF rows rho pt * ∑ l ∈ range 25, eqAtF lam l * stepMleF hk pt (fun x ↦ Y x l) +
        eqEvalF rho pt * (∑ l ∈ range 25, eqAtF lam l * stepMleF hk pt (fun x ↦ ks (x + 2 ^ hk * l)) +
          ∑ l ∈ range 17, eqAtF lam l * ∑ x ∈ range (ksSplitN hk xl), eqAtF pt x * kF (M x l) +
          selXF xl pt * ∑ l ∈ range 17, eqAtF lam l * stepMleF xl (pt.take xl) (fun x ↦ X x l)) := by
  rw [FksF, cubeSumF_full _ hpt, ← contShiftF_eq hk hnd hrows]
  have hee : ∑ k ∈ range (2 ^ hk), eqAtF pt k * eqAtF rho k = eqEvalF rho pt := by
    rw [← sum_eqAtF_mul_eqAtF rho pt (by rw [hr, hpt]), hr]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hy : ∑ k ∈ range (2 ^ hk), eqAtF pt k * yOmF Y lam k =
      ∑ l ∈ range 25, eqAtF lam l * stepMleF hk pt (fun x ↦ Y x l) := by
    simp only [yOmF, stepMleF, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have hin : ∑ k ∈ range (2 ^ hk), eqAtF pt k * inOmF hk ks lam k =
      ∑ l ∈ range 25, eqAtF lam l * stepMleF hk pt (fun x ↦ ks (x + 2 ^ hk * l)) := by
    simp only [inOmF, stepMleF, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have hm : ∀ (n : ℕ) (a : List F) (Z : ℕ → ℕ → K), ∑ x ∈ range n, eqAtF a x *
      ∑ l ∈ range 17, eqAtF lam l * kF (Z x l) =
      ∑ l ∈ range 17, eqAtF lam l * ∑ x ∈ range n, eqAtF a x * kF (Z x l) := fun n a Z ↦ by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hee, hy, Finset.sum_congr rfl fun k _ ↦ mul_add _ _ _, Finset.sum_add_distrib, hin,
    msgOmF_mle hk xl M X lam hxl hpt, hm, hm]
  simp only [stepMleF]
  ring

end KSAlg

/-! ## Statement 7: `KS` and its link -/

variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

/-- **Statement 7 (`ksSpecE2`)**: the `KS` Keccak phase with caller claims at `E2` (`callerSpec` with
`nt` tied lanes), at `L₀ = 1`: from doom of "the region is valid, the tied lanes are the
permutation's output, and `R`" to doom of "the row claim on the column, the committed outputs'
word claims, the tied lanes' word claims at `r`, and `R`". Lead `0`; every ground group `≤ εS`; the
row switch's group with the follower's `T`. -/
theorem ksSpecE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (P nt : ℕ) (hnt : nt ≤ 25)
    (qk : β → ℕ → K) (Y : β → ℕ → ℕ → K) (R : β → Prop)
    (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Nonempty (Spec (callerProgE2 (P + 5))
      (Doomed C (fun q ↦ RegionValid (P + 5) (qk q) ∧ OutRel (P + 5) nt (qk q) (Y q) ∧ R q))
      (fun out hist ↦ out.1.length = P + 5 ∧ out.2.1.length = 25 ∧
        Doomed C (fun q ↦ CallerClaimsE2 (P + 5) nt (qk q) (Y q) out ∧ R q) hist) εS 0 T) := by
  refine ⟨(callerSpecV hst hcard P nt hnt qk Y R (by simpa using hrT)).mono (fun _ h ↦ h)
    (fun out _ ⟨h1, h2, hd⟩ ↦ ⟨h1, h2, Doomed.mono hd fun q ⟨⟨hrow, hcol, htied⟩, hR⟩ ↦
      ⟨hrow, hcol, htied, hR⟩⟩) le_rfl le_rfl le_rfl⟩

/-- **Statement 7 (`ksLinkSpecE2`)**: the `KS` sponge link at `E2` (`ksLinkSpec`), at `L₀ = 1`: from
doom of the sponge link and `R` to doom of the four combined claims at `ρ'` and `R`. Lead `0`; the
coordinates `c = 1`, the shift rounds `c = 2`, the follower's `T` after the four scalars. -/
theorem ksLinkSpecE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (hk xl : ℕ)
    (hxl : xl ≤ hk) (rows : List ℕ) (hnd : rows.Nodup)
    (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ hk) (ks : β → ℕ → K) (Y M X : β → ℕ → ℕ → K)
    (R : β → Prop) (hT : T ≤ εS) :
    Nonempty (Spec (ksLinkProgE2 hk xl rows)
      (Doomed C (fun q ↦ SpongeLink hk rows (ks q) (Y q) (ksMsg (ksSplitN hk xl) (M q) (X q)) ∧ R q))
      (fun out hist ↦ out.2.1.1.length = hk ∧ Doomed C (fun q ↦
        KsClaimsE2 hk xl (ks q) (Y q) (M q) (X q) (out.1.drop hk) out.2.1.1 out.2.2 ∧ R q) hist)
      εS 0 T) := by
  have h0 : 0 ∉ rows := fun h ↦ by have := hrows 0 h; omega
  have hz1 : ((1 : ℕ) : ℝ≥0∞) * errG gC1 1 + 0 ≤ εS := by
    rw [add_zero, errG_grpEpsE]; exact table_arch7_εS.1
  have hs2 : ((1 : ℕ) : ℝ≥0∞) * errG gC2 2 + 0 ≤ εS := by
    rw [add_zero, errG_grpEpsE]; exact table_arch7_εS.2.1
  exact ⟨((zeroSpecE2 (T := 0) hst hcard (g := gC1) (by norm_num)
      (fun q ↦ ksDeltaF hk xl rows (ks q) (Y q) (M q) (X q)) R (n := hk + 5) (m := hk + 4)
      le_rfl hz1).mono
    (fun hist (hd : Doomed C (fun q ↦ SpongeLink hk rows (ks q) (Y q)
        (ksMsg (ksSplitN hk xl) (M q) (X q)) ∧ R q) hist) ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦
      ⟨spongeLink_of_zeroF hk xl rows (ks q) (Y q) (M q) (X q) hz, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun kchal ↦
  if hc : kchal.length = hk + 5 then
    ((sumcheckGSpec (T := 0) hst hcard R
        (FksF_plain hk xl rows (kchal.drop hk) ks Y M X (kchal.take hk)) (count := 3)
        (by norm_num) (by norm_num) (g := gC2) (by norm_num) hs2 hk [] 0 (by simp)).mono
      (fun _ (hd : kchal.length = hk + 4 + 1 ∧ Doomed C (fun q ↦
          ZeroOnF (ksDeltaF hk xl rows (ks q) (Y q) (M q) (X q)) kchal (hk + 5) ∧ R q) _) ↦
        Doomed.mono hd.2 fun q ⟨hcl, hR⟩ ↦
          ⟨ks_zero_of_claimF hk xl rows (ks q) (Y q) (M q) (X q) h0
            (fun i hi ↦ (hrows i hi).2) hc hcl, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun kshift ↦
    if hs : kshift.1.length = hk then
      ((e2ReadsSpec (T := T) hst
          (fun q ↦ kshift.2 = FksF hk xl rows (ks q) (Y q) (M q) (X q) (kchal.drop hk)
            (kchal.take hk) ([] ++ kshift.1) ∧ R q) hT 3).mono
        (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun vals ↦
      (Spec.require (Post := fun _ hist ↦ Doomed C (fun q ↦
          KsClaimsE2 hk xl (ks q) (Y q) (M q) (X q) (kchal.drop hk) kshift.1 vals ∧ R q) hist)
        (fun _ hd hcond ↦ Doomed.mono hd.2 fun q ⟨⟨h1, h2', h3, h4⟩, hR⟩ ↦ ⟨by
          rw [List.nil_append, FksF_end hk xl rows (ks q) (Y q) (M q) (X q) _ hxl hnd hrows
            (by simp [hc]) hs, hcond, h1, h2', h3, h4], hR⟩)).bind' fun _ ↦
      (Spec.ret (kchal, kshift, vals)).mono (fun _ hd ↦ ⟨hs, hd⟩) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hc hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩

end Lvm.E2V
