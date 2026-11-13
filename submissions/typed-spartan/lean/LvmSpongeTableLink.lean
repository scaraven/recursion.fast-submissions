-- New for lvm (WP-8): the KS sponge link as a doom specification (BLUEPRINT §4.2): V_S's `M3.v0` KS link
-- (`ksLink0`, `contShift`) on leanVM's DSL.
import LvmChainTableLink
import LvmSpongeTable

/-!
# The `KS` sponge link

For every row `i < 2^hk` and lane `l < 25`: `in_i[l] = cont_i·Y_{i−1}[l] + [l < 17]·Msg_l[i]`, where
`Msg_l[i]` is `C_rec`'s stream column `M_l` below the split `s = 2^hk − 2^xl` and `C_main`'s `X_l` (17 columns
of `2^xl` rows) from it, and `cont_i = [i ∈ rows]` (V_S's `contRows`, `0 ∉ rows`). This is
`SpongeRel.link` (`LvmSpongeTable`) with `msg = ksMsg s`. (lvm2 CR-K, KS14: at `P20` `hk = 14`, `xl = 10`, the
split 15,360 and the selector `x₁₃x₁₂x₁₁x₁₀`; v1's layout is `xl = hk − 1`, split `2^(hk−1)`, selector `x_{hk−1}`.)
The rows from the split are the subcube whose coordinates `xl … hk − 1` are all one, so their weight at `ρ'`
is `sel(ρ') · eq(ρ'_{<xl}, ·)` with `sel(ρ') = Π_{j ≥ xl} ρ'_j` (`selX`, `eqAt_split`).

`ksLinkProg` is V_S's phase 7, read for read:

```
kchal ← hk + 5 challenges (ρ, λ);  kshift ← hk plain rounds of degree 2 on the claim 0;
vals ← 4 scalars (Y_ω(ρ'), in_ω(ρ'), M_ω(ρ') on the rows below the split, X_ω(ρ'_{<xl}));
require f = Sc(ρ, ρ')·Y_ω + eq(ρ, ρ')·(in_ω + M_ω + sel(ρ')·X_ω)
```

**`ksLinkSpec`**: from doom of `SpongeLink ∧ R` to doom of the four combined claims (`KsClaims`)
and `R`. `contShiftE_eq` proves V_S's `contShift` (a sum over the rows of `cont`) is the shifted
kernel's extension. Groups: `ρλ`, `(hk + 5)·L₀/|E|`; each round `L₀·2/|E|`.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open Finset
open scoped ENNReal

/-! ## V_S's formulas over `E` -/

/-- V_S's `contShift`: `Sc(ρ, ρ') = Σ_{i ∈ rows} eq(ρ, i)·eq(ρ', i − 1)`. -/
def contShiftE (rows : List ℕ) (rho rho' : List E) : E :=
  (rows.map fun i ↦ eqAt rho i * eqAt rho' (i - 1)).sum

/-- The message lane `l` of row `i`: `M` below the split `s`, `X` (indexed from the split) from it. -/
def ksMsg (s : ℕ) (M X : ℕ → ℕ → K) (i l : ℕ) : K := if i < s then M i l else X (i - s) l

/-- The split of `2^hk` rows when `X` has `2^xl`: `2^hk − 2^xl`. -/
def ksSplitN (hk xl : ℕ) : ℕ := 2 ^ hk - 2 ^ xl

theorem ksSplitN_add {hk xl : ℕ} (hxl : xl ≤ hk) : ksSplitN hk xl + 2 ^ xl = 2 ^ hk := by
  have := Nat.pow_le_pow_right two_pos hxl
  unfold ksSplitN; omega

/-- **V_S's selector** of the rows from the split: `Π_{j ≥ xl} ρ'_j`. -/
def selX (xl : ℕ) (pt : List E) : E := (pt.drop xl).prod

/-- **The sponge link** on every row (`SpongeRel.link`, `cont i = [i ∈ rows]`). -/
def SpongeLink (hk : ℕ) (rows : List ℕ) (ks : ℕ → K) (Y msg : ℕ → ℕ → K) : Prop :=
  ∀ i < 2 ^ hk, ∀ l < 25,
    ks (i + 2 ^ hk * l) = (if i ∈ rows then Y (i - 1) l else 0) + (if l < 17 then msg i l else 0)

/-- **The `KS` link** (V_S phase 7, `M3.v0`; `X` on `2^xl` rows). -/
def ksLinkProg (hk xl : ℕ) (rows : List ℕ) :
    VerifierProgram (List E × (List E × E) × List E) :=
  VerifierProgram.sampleChallenges (hk + 5) >>= fun kchal ↦
  sumcheck 0 3 (List.replicate hk none) >>= fun kshift ↦
  VerifierProgram.readScalars 4 >>= fun vals ↦
  VerifierProgram.require (kshift.2 =
    contShiftE rows (kchal.take hk) kshift.1 * vals.getD 0 0 +
      eqEval (kchal.take hk) kshift.1 * (vals.getD 1 0 + vals.getD 2 0 +
        selX xl kshift.1 * vals.getD 3 0)) >>= fun _ ↦
  VerifierProgram.ret (kchal, kshift, vals)

/-- **The four combined claims** at `ρ'` (V_S's `yC`, `inC`, `mC`, `xC`): `M`'s on the rows below the split
(`eq(ρ', ·)` cut at `2^hk − 2^xl`), `X`'s at `ρ'_{<xl}`. -/
def KsClaims (hk xl : ℕ) (ks : ℕ → K) (Y M X : ℕ → ℕ → K) (lam rho' vals : List E) : Prop :=
  vals.getD 0 0 = ∑ l ∈ range 25, eqAt lam l * stepMle hk rho' (fun x ↦ Y x l) ∧
  vals.getD 1 0 = ∑ l ∈ range 25, eqAt lam l * stepMle hk rho' (fun x ↦ ks (x + 2 ^ hk * l)) ∧
  vals.getD 2 0 = ∑ l ∈ range 17, eqAt lam l * ∑ x ∈ range (ksSplitN hk xl), eqAt rho' x * ofK (M x l) ∧
  vals.getD 3 0 = ∑ l ∈ range 17, eqAt lam l * stepMle xl (rho'.take xl) (fun x ↦ X x l)

/-! ## `contShift` is the shifted kernel's extension -/

/-- The shifted continuation kernel on the cube: `Sc(ρ, k) = [k + 1 ∈ rows]·eq(ρ, k + 1)`. -/
def scK (rows : List ℕ) (rho : List E) (k : ℕ) : E := if k + 1 ∈ rows then eqAt rho (k + 1) else 0

theorem contShiftE_eq (n : ℕ) {rows : List ℕ} (hnd : rows.Nodup)
    (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ n) (rho rho' : List E) :
    contShiftE rows rho rho' = ∑ k ∈ range (2 ^ n), eqAt rho' k * scK rows rho k := by
  classical
  rw [contShiftE, ← List.sum_toFinset _ hnd]
  simp only [scK, mul_ite, mul_zero]
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

/-! ## The zero test and the sumcheck family -/

variable (hk xl : ℕ) (rows : List ℕ) (ks : ℕ → K) (Y M X : ℕ → ℕ → K) (lam : List E)

/-- The sponge link's zero-test table on `hk + 5` bits: row low, lane high. -/
def ksDelta (w : ℕ) : E :=
  if w / 2 ^ hk < 25 then
    ofK (ks (w % 2 ^ hk + 2 ^ hk * (w / 2 ^ hk))) +
      (if w % 2 ^ hk ∈ rows then ofK (Y (w % 2 ^ hk - 1) (w / 2 ^ hk)) else 0) +
      (if w / 2 ^ hk < 17 then ofK (ksMsg (ksSplitN hk xl) M X (w % 2 ^ hk) (w / 2 ^ hk)) else 0)
  else 0

theorem ofK_add' (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_zero' : ofK (0 : K) = 0 := map_zero (algebraMap K E)

theorem char2_sum3 {a b c : E} (h : a + b + c = 0) : a = b + c := by
  linear_combination h - (b + c) * CharTwo.two_eq_zero (R := E)

/-- A vanishing table is the sponge link. -/
theorem spongeLink_of_zero (hz : ZeroOn (ksDelta hk xl rows ks Y M X) [] (hk + 5)) :
    SpongeLink hk rows ks Y (ksMsg (ksSplitN hk xl) M X) := by
  rw [zeroOn_nil] at hz
  intro i hi l hl
  have := hz (i + 2 ^ hk * l) (by
    have : 2 ^ (hk + 5) = 2 ^ hk * 32 := by rw [pow_add]; rfl
    nlinarith)
  simp only [ksDelta, idx_div hk hi, idx_mod hk hi, if_pos hl] at this
  apply ofK_injective'
  rw [ofK_add', apply_ite ofK, apply_ite ofK, ofK_zero']
  exact char2_sum3 this

/-- `Y_ω(k)`, `in_ω(k)`, `Msg_ω(k)`: the lanes combined by `eq(λ, ·)`. -/
def yOm (k : ℕ) : E := ∑ l ∈ range 25, eqAt lam l * ofK (Y k l)
/-- `in_ω(k)`. -/
def inOm (k : ℕ) : E := ∑ l ∈ range 25, eqAt lam l * ofK (ks (k + 2 ^ hk * l))
/-- `Msg_ω(k)`. -/
def msgOm (k : ℕ) : E := ∑ l ∈ range 17, eqAt lam l * ofK (ksMsg (ksSplitN hk xl) M X k l)

/-- The `KS` link sumcheck's family. -/
noncomputable def Fks (rho acc : List E) : E :=
  cubeSum (fun pt ↦ (∑ k ∈ range (2 ^ hk), eqAt pt k * scK rows rho k) *
      (∑ k ∈ range (2 ^ hk), eqAt pt k * yOm Y lam k) +
    (∑ k ∈ range (2 ^ hk), eqAt pt k * eqAt rho k) *
      (∑ k ∈ range (2 ^ hk), eqAt pt k * (inOm hk ks lam k + msgOm hk xl M X lam k))) hk acc

theorem Fks_plain {β : Type} (kq : β → ℕ → K) (Yq Mq Xq : β → ℕ → ℕ → K) (rho : List E) :
    PlainFamily (fun q acc ↦ Fks hk xl rows (kq q) (Yq q) (Mq q) (Xq q) lam rho acc) 2 hk :=
  cube_plainFamily _ hk fun _ pre post ↦ PolyLE.add (polyLE_mle_mul _ _ _ _ pre post)
    (polyLE_mle_mul _ _ _ _ pre post)

/-- One row of the table, its lanes combined by `eq(λ, ·)`. -/
theorem ksDelta_row (hl : lam.length = 5) {x : ℕ} (hx : x < 2 ^ hk) :
    ∑ o ∈ range (2 ^ lam.length), eqAt lam o * ksDelta hk xl rows ks Y M X (x + 2 ^ hk * o) =
      inOm hk ks lam x + (if x ∈ rows then yOm Y lam (x - 1) else 0) + msgOm hk xl M X lam x := by
  rw [hl, show (2 : ℕ) ^ 5 = 25 + 7 from rfl, Finset.sum_range_add]
  have h7 : ∑ o ∈ range 7, eqAt lam (25 + o) * ksDelta hk xl rows ks Y M X (x + 2 ^ hk * (25 + o)) =
      0 := by
    refine Finset.sum_eq_zero fun o _ ↦ ?_
    rw [ksDelta, idx_div hk hx, if_neg (by omega), mul_zero]
  rw [h7, add_zero]
  have e : ∀ o ∈ range 25, eqAt lam o * ksDelta hk xl rows ks Y M X (x + 2 ^ hk * o) =
      eqAt lam o * ofK (ks (x + 2 ^ hk * o)) +
        ((if x ∈ rows then eqAt lam o * ofK (Y (x - 1) o) else 0) +
          (if o < 17 then eqAt lam o * ofK (ksMsg (ksSplitN hk xl) M X x o) else 0)) := by
    intro o ho
    rw [ksDelta, idx_div hk hx, idx_mod hk hx, if_pos (Finset.mem_range.1 ho), mul_add, mul_add,
      mul_ite, mul_ite, mul_zero, add_assoc]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hY : ∑ o ∈ range 25, (if x ∈ rows then eqAt lam o * ofK (Y (x - 1) o) else 0) =
      if x ∈ rows then yOm Y lam (x - 1) else 0 := by
    split_ifs <;> simp [yOm]
  have hM : ∑ o ∈ range 25, (if o < 17 then eqAt lam o * ofK (ksMsg (ksSplitN hk xl) M X x o) else 0) =
      msgOm hk xl M X lam x := by
    rw [show 25 = 17 + 8 from rfl, Finset.sum_range_add, msgOm,
      Finset.sum_eq_zero (s := range 8) fun o _ ↦ if_neg (by omega), add_zero]
    exact Finset.sum_congr rfl fun o ho ↦ if_pos (Finset.mem_range.1 ho)
  rw [hY, hM, inOm, add_assoc]

/-- **The zero test at `(ρ, λ)` is the claim `0`.** -/
theorem ks_zero_of_claim (h0 : 0 ∉ rows) (hrows : ∀ i ∈ rows, i < 2 ^ hk) {kchal : List E}
    (hc : kchal.length = hk + 5)
    (H : (0 : E) = Fks hk xl rows ks Y M X (kchal.drop hk) (kchal.take hk) []) :
    ZeroOn (ksDelta hk xl rows ks Y M X) kchal (hk + 5) := by
  have hr : (kchal.take hk).length = hk := by simp [hc]
  have hl : (kchal.drop hk).length = 5 := by simp [hc]
  set ρ := kchal.take hk with hρ
  set lm := kchal.drop hk with hlm
  rw [zeroOn_full _ hc]
  have hsplit : kchal = ρ ++ lm := (List.take_append_drop hk kchal).symm
  have e1 : ∑ w ∈ range (2 ^ (hk + 5)), eqAt kchal w * ksDelta hk xl rows ks Y M X w =
      ∑ x ∈ range (2 ^ hk), eqAt ρ x *
        (inOm hk ks lm x + (if x ∈ rows then yOm Y lm (x - 1) else 0) + msgOm hk xl M X lm x) := by
    conv_lhs => rw [hsplit]
    rw [show hk + 5 = hk + lm.length by rw [hl], col_split hr]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [← ksDelta_row hk xl rows ks Y M X lm hl (Finset.mem_range.1 hx), Finset.mul_sum]
    exact Finset.sum_congr rfl fun o _ ↦ by ring
  rw [e1]
  refine Eq.trans ?_ H.symm
  rw [Fks, cubeSum_nil]
  have hcube : ∀ u ∈ range (2 ^ hk),
      (∑ k ∈ range (2 ^ hk), eqAt (bitsE u hk) k * scK rows ρ k) *
        (∑ k ∈ range (2 ^ hk), eqAt (bitsE u hk) k * yOm Y lm k) +
      (∑ k ∈ range (2 ^ hk), eqAt (bitsE u hk) k * eqAt ρ k) *
        (∑ k ∈ range (2 ^ hk), eqAt (bitsE u hk) k * (inOm hk ks lm k + msgOm hk xl M X lm k)) =
      scK rows ρ u * yOm Y lm u + eqAt ρ u * (inOm hk ks lm u + msgOm hk xl M X lm u) := by
    intro u hu
    have hu' := Finset.mem_range.1 hu
    rw [sum_eqAt_bitsE hu', sum_eqAt_bitsE hu', sum_eqAt_bitsE hu', sum_eqAt_bitsE hu']
  rw [Finset.sum_congr rfl hcube, Finset.sum_add_distrib]
  have hp := Nat.two_pow_pos hk
  obtain ⟨Mk, hMk⟩ : ∃ Mk, 2 ^ hk = Mk + 1 := ⟨2 ^ hk - 1, by omega⟩
  have hshift : ∑ u ∈ range (2 ^ hk), scK rows ρ u * yOm Y lm u =
      ∑ x ∈ range (2 ^ hk), eqAt ρ x * (if x ∈ rows then yOm Y lm (x - 1) else 0) := by
    rw [hMk, Finset.sum_range_succ, Finset.sum_range_succ']
    have hlast : Mk + 1 ∉ rows := fun hm ↦ by have := hrows _ hm; omega
    simp only [scK, hlast, ite_false, zero_mul, add_zero, h0, mul_zero, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs <;> simp
  rw [hshift, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

/-! ## The end of the sumcheck -/

/-- `eq` at the all-ones index of a point is the product of its coordinates. -/
theorem eqAt_ones : ∀ pt : List E, eqAt pt (2 ^ pt.length - 1) = pt.prod
  | [] => by simp
  | r :: rs => by
    have h1 : 1 ≤ 2 ^ rs.length := Nat.one_le_two_pow
    have hm : (2 ^ rs.length * 2 - 1) % 2 = 1 := by omega
    have hd : (2 ^ rs.length * 2 - 1) / 2 = 2 ^ rs.length - 1 := by omega
    rw [eqAt_cons, List.length_cons, List.prod_cons, pow_succ, hm, hd, eqAt_ones rs, if_pos rfl]

/-- **A row from the split**: `eq(pt, 2^hk − 2^xl + j) = eq(pt_{<xl}, j)·sel(pt)`. -/
theorem eqAt_split {hk xl : ℕ} (hxl : xl ≤ hk) {pt : List E} (hpt : pt.length = hk) {j : ℕ}
    (hj : j < 2 ^ xl) : eqAt pt (ksSplitN hk xl + j) = eqAt (pt.take xl) j * selX xl pt := by
  have hd : (pt.drop xl).length = hk - xl := by simp [hpt]
  have ht : (pt.take xl).length = xl := by simp [hpt]; omega
  have hp : 2 ^ hk = 2 ^ xl * 2 ^ (hk - xl) := by rw [← pow_add]; congr 1; omega
  have h1 : 1 ≤ 2 ^ (hk - xl) := Nat.one_le_two_pow
  have hw : ksSplitN hk xl + j = j + 2 ^ xl * (2 ^ (hk - xl) - 1) := by
    have e := ksSplitN_add hxl
    rw [hp] at e
    rw [Nat.mul_sub_one]
    have : 2 ^ xl ≤ 2 ^ xl * 2 ^ (hk - xl) := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  conv_lhs => rw [← List.take_append_drop xl pt]
  rw [eqAt_append, ht, hw, eqAt_mod (pt.take xl), ht, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hj, zero_add, ← hd, eqAt_ones, selX]

/-- **The messages split at `2^hk − 2^xl`**: `M` on the rows below, `X` (its `xl` low coordinates) times the
selector on the rows from it. -/
theorem msgOm_mle (hxl : xl ≤ hk) {pt : List E} (hpt : pt.length = hk) :
    ∑ k ∈ range (2 ^ hk), eqAt pt k * msgOm hk xl M X lam k =
      ∑ x ∈ range (ksSplitN hk xl), eqAt pt x * ∑ l ∈ range 17, eqAt lam l * ofK (M x l) +
        selX xl pt * ∑ x ∈ range (2 ^ xl), eqAt (pt.take xl) x *
          ∑ l ∈ range 17, eqAt lam l * ofK (X x l) := by
  rw [show range (2 ^ hk) = range (ksSplitN hk xl + 2 ^ xl) by rw [ksSplitN_add hxl],
    Finset.sum_range_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [msgOm, ksMsg, if_pos (Finset.mem_range.1 hx)]
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.1 hj
    simp only [msgOm, ksMsg, if_neg (show ¬ ksSplitN hk xl + j < ksSplitN hk xl by omega),
      Nat.add_sub_cancel_left, eqAt_split hxl hpt hj']
    ring

/-- **The cut at the split** (char 2): the extension over all `2^hk` rows plus `sel(pt)` times the rows from the
split at `pt_{<xl}` is the extension over the rows below the split (V_S's `M` claim, KS14). -/
theorem cut_split {hk xl : ℕ} (hxl : xl ≤ hk) {pt : List E} (hpt : pt.length = hk) (F : ℕ → E) :
    ∑ n ∈ range (2 ^ hk), eqAt pt n * F n +
        selX xl pt * ∑ n ∈ range (2 ^ xl), eqAt (pt.take xl) n * F (ksSplitN hk xl + n) =
      ∑ n ∈ range (ksSplitN hk xl), eqAt pt n * F n := by
  have hz : ∑ j ∈ range (2 ^ xl), (eqAt pt (ksSplitN hk xl + j) * F (ksSplitN hk xl + j) +
      selX xl pt * (eqAt (pt.take xl) j * F (ksSplitN hk xl + j))) = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [eqAt_split hxl hpt (Finset.mem_range.1 hj),
        show selX xl pt * (eqAt (pt.take xl) j * F (ksSplitN hk xl + j)) =
          eqAt (pt.take xl) j * selX xl pt * F (ksSplitN hk xl + j) by ring]
      exact CharTwo.add_self_eq_zero _
  rw [show range (2 ^ hk) = range (ksSplitN hk xl + 2 ^ xl) by rw [ksSplitN_add hxl],
    Finset.sum_range_add, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib, hz, add_zero]

/-- **The `KS` link sumcheck's end** at `ρ'`, in V_S's closed forms. -/
theorem Fks_end (hxl : xl ≤ hk) (hnd : rows.Nodup) (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ hk)
    {rho pt : List E} (hr : rho.length = hk) (hpt : pt.length = hk) :
    Fks hk xl rows ks Y M X lam rho pt =
      contShiftE rows rho pt * ∑ l ∈ range 25, eqAt lam l * stepMle hk pt (fun x ↦ Y x l) +
        eqEval rho pt * (∑ l ∈ range 25, eqAt lam l * stepMle hk pt (fun x ↦ ks (x + 2 ^ hk * l)) +
          ∑ l ∈ range 17, eqAt lam l * ∑ x ∈ range (ksSplitN hk xl), eqAt pt x * ofK (M x l) +
          selX xl pt * ∑ l ∈ range 17, eqAt lam l * stepMle xl (pt.take xl) (fun x ↦ X x l)) := by
  rw [Fks, cubeSum_full _ hpt, ← contShiftE_eq hk hnd hrows]
  have hee : ∑ k ∈ range (2 ^ hk), eqAt pt k * eqAt rho k = eqEval rho pt := by
    rw [← sum_eqAt_mul_eqAt rho pt (by rw [hr, hpt]), hr]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hy : ∑ k ∈ range (2 ^ hk), eqAt pt k * yOm Y lam k =
      ∑ l ∈ range 25, eqAt lam l * stepMle hk pt (fun x ↦ Y x l) := by
    simp only [yOm, stepMle, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have hin : ∑ k ∈ range (2 ^ hk), eqAt pt k * inOm hk ks lam k =
      ∑ l ∈ range 25, eqAt lam l * stepMle hk pt (fun x ↦ ks (x + 2 ^ hk * l)) := by
    simp only [inOm, stepMle, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have hm : ∀ (n : ℕ) (a : List E) (Z : ℕ → ℕ → K), ∑ x ∈ range n, eqAt a x *
      ∑ l ∈ range 17, eqAt lam l * ofK (Z x l) =
      ∑ l ∈ range 17, eqAt lam l * ∑ x ∈ range n, eqAt a x * ofK (Z x l) := fun n a Z ↦ by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hee, hy, Finset.sum_congr rfl fun k _ ↦ mul_add _ _ _, Finset.sum_add_distrib, hin,
    msgOm_mle hk xl M X lam hxl hpt, hm, hm]
  simp only [stepMle]
  ring

/-! ## The specification -/

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **The `KS` sponge link**, round by round: from doom of the sponge link and `R` to doom of the
four combined claims at `ρ'` and `R`. Lead `(hk + 5)·L₀/|E|`. -/
noncomputable def ksLinkSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (hk xl : ℕ)
    (hxl : xl ≤ hk) (rows : List ℕ) (hnd : rows.Nodup)
    (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ hk) (ks : β → ℕ → K) (Y M X : β → ℕ → ℕ → K)
    (R : β → Prop) (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax) (hT : T ≤ εmax) :
    Spec (ksLinkProg hk xl rows)
      (Doomed C (fun q ↦ SpongeLink hk rows (ks q) (Y q) (ksMsg (ksSplitN hk xl) (M q) (X q)) ∧ R q))
      (fun out hist ↦ out.2.1.1.length = hk ∧ Doomed C (fun q ↦
        KsClaims hk xl (ks q) (Y q) (M q) (X q) (out.1.drop hk) out.2.1.1 out.2.2 ∧ R q) hist)
      εmax (((hk + 5 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) T :=
  have h0 : 0 ∉ rows := fun h ↦ by have := hrows 0 h; omega
  ((zeroSpec (T := 0) hst hcard (fun q ↦ ksDelta hk xl rows (ks q) (Y q) (M q) (X q)) R
      (n := hk + 5) (m := hk + 5) le_rfl).mono
    (fun hist (hd : Doomed C (fun q ↦ SpongeLink hk rows (ks q) (Y q) (ksMsg (ksSplitN hk xl) (M q) (X q)) ∧
        R q) hist) ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦
      ⟨spongeLink_of_zero hk xl rows (ks q) (Y q) (M q) (X q) hz, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun kchal ↦
  if hc : kchal.length = hk + 5 then
    ((sumcheckSpec (T := 0) hst hcard R
        (Fks_plain hk xl rows (kchal.drop hk) ks Y M X (kchal.take hk)) (count := 3)
        (by norm_num) (by norm_num) zero_le h2 hk [] 0 (by simp)).mono
      (fun _ (hd : kchal.length = hk + 5 ∧ Doomed C (fun q ↦
          ZeroOn (ksDelta hk xl rows (ks q) (Y q) (M q) (X q)) kchal (hk + 5) ∧ R q) _) ↦
        Doomed.mono hd.2 fun q ⟨hcl, hR⟩ ↦
          ⟨ks_zero_of_claim hk xl rows (ks q) (Y q) (M q) (X q) h0
            (fun i hi ↦ (hrows i hi).2) hc hcl, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun kshift ↦
    if hs : kshift.1.length = hk then
      ((doomReadN (T := T) hst
          (fun q ↦ kshift.2 = Fks hk xl rows (ks q) (Y q) (M q) (X q) (kchal.drop hk)
            (kchal.take hk) ([] ++ kshift.1) ∧ R q) hT 3).mono
        (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun vals ↦
      (Spec.require (Post := fun _ hist ↦ Doomed C (fun q ↦
          KsClaims hk xl (ks q) (Y q) (M q) (X q) (kchal.drop hk) kshift.1 vals ∧ R q) hist)
        (fun _ hd hcond ↦ Doomed.mono hd.2 fun q ⟨⟨h1, h2', h3, h4⟩, hR⟩ ↦ ⟨by
          rw [List.nil_append, Fks_end hk xl rows (ks q) (Y q) (M q) (X q) _ hxl hnd hrows
            (by simp [hc]) hs, hcond, h1, h2', h3, h4], hR⟩)).bind' fun _ ↦
      (Spec.ret (kchal, kshift, vals)).mono (fun _ hd ↦ ⟨hs, hd⟩) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hc hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm.KG
