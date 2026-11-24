-- New for lvm6 (WP-V1b): fast twins of WP K1's two input ends (`treeEnd6`, §6.2 row 10; `spongeEnd6`, §6.3)
-- in the word field. The final checks' sums over 64 slices and 64 slots are evaluated in exchanged order
-- (one pass over the weights per slot), proved equal to K1's closed forms in `E2`.
import Lvm6VTw
import Lvm6KProg

/-!
# Fast twins: the Keccak reductions' input ends

* `KClaimF` (weights in an array), `KClaimF.dec`; `EndOutF`, `EndOutF.dec`.
* **`treeFast`**, `treeSum_eq` (K1's `Σ_z treeWt(z)·s_z` in `E2` is `treeFast` of the eq table, weights and
  slices: slots `< 8` through the byte shift, slots `8 … 32` direct), `map_treeFast`.
* **`spFast`**, `spSum_eq` (the sponge's `Σ_z spWt(z)·s_z`), `map_spFast`.
* **`tw_treeEnd6`**, **`tw_spongeEnd6`**: `fTreeEnd6 P c`, `fSpongeEnd6 P c` are twins of `treeEnd6 P c.dec`,
  `spongeEnd6 P c.dec`.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V Lvm6.K
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Finset

/-! ## The sums in exchanged order -/

section Gen

variable {F : Type} [Field F]

/-- The byte-shift pull-back on a weight function (`shW`). -/
def shG (w : ℕ → F) (o z : ℕ) : F := if z < 56 then w (64 * o + z + 8) else w (64 * (o + 1) + z - 56)

/-- **The tree end's sum, slot by slot**: `Σ_{o<33} e(o)·(a_o·Σ_z shW(o,z)·s_z [o < 8] + C·Σ_z w(64(o−8)+z)·s_z [8 ≤ o])`
with `a_o = A + B·[o < 4]`. -/
def treeFast (A B C : F) (e w s : ℕ → F) : F :=
  ∑ o ∈ range 33, e o * ((if o < 8 then (A + if o < 4 then B else 0) * ∑ z ∈ range 64, shG w o z * s z else 0) +
    (if 8 ≤ o then C * ∑ z ∈ range 64, w (64 * (o - 8) + z) * s z else 0))

/-- **The sponge end's sum, slot by slot**: `Σ_m e₁(m)·Σ_ℓ e(25m+ℓ)·Σ_z w(64ℓ+z)·s_z`. -/
def spFast (e1 e w s : ℕ → F) : F :=
  ∑ m ∈ range 2, e1 m * ∑ l ∈ range 25, e (25 * m + l) * ∑ z ∈ range 64, w (64 * l + z) * s z

variable {F' : Type} [Field F'] (φ : F →+* F')

theorem map_treeFast (A B C : F) (e w s : ℕ → F) :
    φ (treeFast A B C e w s) = treeFast (φ A) (φ B) (φ C) (φ ∘ e) (φ ∘ w) (φ ∘ s) := by
  simp only [treeFast, shG, map_sum, map_mul, map_add, apply_ite (⇑φ), map_zero, Function.comp]

theorem map_spFast (e1 e w s : ℕ → F) :
    φ (spFast e1 e w s) = spFast (φ ∘ e1) (φ ∘ e) (φ ∘ w) (φ ∘ s) := by
  simp only [spFast, map_sum, map_mul, Function.comp]

end Gen

theorem sum_range_trunc {F : Type} [AddCommMonoid F] (f : ℕ → F) {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ i, m ≤ i → i < n → f i = 0) : ∑ i ∈ range n, f i = ∑ i ∈ range m, f i :=
  (sum_subset (range_mono hmn) fun i hi hni =>
    h i (by simpa using hni) (by simpa using hi)).symm

/-- **K1's tree-end sum is `treeFast`.** -/
theorem treeSum_eq (rseg rtop ϱtop : E2) (w ϱs s : List E2) :
    ∑ z ∈ range 64, treeWt rseg rtop ϱtop w ϱs z * s.getD z 0 =
      treeFast ((1 + rseg) * (1 + rtop) * (1 + ϱtop)) ((1 + rseg) * (rtop * ϱtop)) (rseg * (1 + rtop + ϱtop))
        (eqAtF ϱs) (fun i => w.getD i 0) (fun i => s.getD i 0) := by
  unfold treeWt treeFast
  simp only [sum_mul]
  rw [sum_comm, sum_range_trunc _ (show 33 ≤ 64 by norm_num)]
  · refine sum_congr rfl fun o ho => ?_
    have ho : o < 33 := mem_range.1 ho
    by_cases h8 : o < 8
    · rw [if_pos h8, if_neg (show ¬ 8 ≤ o by omega), add_zero, mul_sum, mul_sum]
      refine sum_congr rfl fun z _ => ?_
      simp only [pwP, pwL, pwM, shW, shG]
      split_ifs <;> first | omega | ring
    · rw [if_neg h8, if_pos (show 8 ≤ o by omega), zero_add, mul_sum, mul_sum]
      refine sum_congr rfl fun z _ => ?_
      simp only [pwP, pwL, pwM, shW, shG]
      split_ifs <;> first | omega | ring
  · intro o h1 h2
    refine sum_eq_zero fun z _ => ?_
    simp only [pwP, pwL, pwM]
    split_ifs <;> first | omega | ring

/-- **K1's sponge-end sum is `spFast`.** -/
theorem spSum_eq (rseg : E2) (w ϱs s : List E2) :
    ∑ z ∈ range 64, spWt rseg w ϱs z * s.getD z 0 =
      spFast (eqAtF [rseg]) (eqAtF ϱs) (fun i => w.getD i 0) (fun i => s.getD i 0) := by
  unfold spWt spFast
  simp only [sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_comm]

/-! ## Claims and end outputs in the word field -/

/-- A Keccak claim in the word field (weights in an array). -/
structure KClaimF where
  value : FE2
  mu : List FE2
  point : List FE2
  weights : Array FE2

/-- Its value in `E2`. -/
def KClaimF.dec (c : KClaimF) : KClaim E2 :=
  ⟨FE2.toE2 c.value, c.mu.map FE2.toE2, c.point.map FE2.toE2, c.weights.toList.map FE2.toE2⟩

/-- An end's output in the word field. -/
structure EndOutF where
  ϱ : List FE2
  pt : List FE2
  s : List FE2

/-- Its value in `E2`. -/
def EndOutF.dec (o : EndOutF) : EndOut := ⟨o.ϱ.map FE2.toE2, o.pt.map FE2.toE2, o.s.map FE2.toE2⟩

theorem arr_getD (w : Array FE2) (j : ℕ) : w.getD j 0 = w.toList.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem toE2_arr_getD (w : Array FE2) (j : ℕ) : FE2.toE2 (w.getD j 0) = (w.toList.map FE2.toE2).getD j 0 := by
  rw [arr_getD, toE2_getD]

theorem toE2_optGetD (o : Option FE2) : FE2.toE2 (o.getD 0) = (o.map FE2.toE2).getD 0 := by
  cases o
  · exact toE2_zero'
  · rfl

/-- `C^t` on the array of weights. -/
def cWF (w : Array FE2) (bits : List ℕ) : FE2 := (bits.map fun j => w.getD j 0).sum

theorem toE2_cWF (w : Array FE2) (bits : List ℕ) : FE2.toE2 (cWF w bits) = cW (w.toList.map FE2.toE2) bits := by
  unfold cWF cW
  rw [← coe_tE, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  exact toE2_arr_getD w j

/-! ## The tree end -/

/-- `treeV'` in the word field. -/
def treeV'F (P : ℕ) (c : KClaimF) : FE2 :=
  c.value + (1 + c.point.getD P 0) * c.mu.sum *
    ((1 + c.point.getD (P - 1) 0) * cWF c.weights cPbits + c.point.getD (P - 1) 0 * cWF c.weights cLbits)

theorem toE2_treeV'F (P : ℕ) (c : KClaimF) : FE2.toE2 (treeV'F P c) = treeV' P c.dec := by
  simp only [treeV'F, treeV', KClaimF.dec, toE2_add', toE2_mul', toE2_one', toE2_getD, toE2_cWF]
  rw [← coe_tE, map_list_sum]

/-- The tree end's final sum in the word field (`ϱ` = the 11 round challenges). -/
def treeSumF (P : ℕ) (c : KClaimF) (ϱ s : List FE2) : FE2 :=
  let rseg := c.point.getD P 0
  let rtop := c.point.getD (P - 1) 0
  let ϱtop := ϱ.getD 4 0
  let sA := s.toArray
  treeFast ((1 + rseg) * (1 + rtop) * (1 + ϱtop)) ((1 + rseg) * (rtop * ϱtop)) (rseg * (1 + rtop + ϱtop))
    (eqAtF (ϱ.drop 5)) (fun i => c.weights.getD i 0) (fun i => sA.getD i 0)

theorem toE2_treeSumF (P : ℕ) (c : KClaimF) (ϱ s : List FE2) :
    FE2.toE2 (treeSumF P c ϱ s) = ∑ z ∈ range 64, treeWt (c.dec.point.getD P 0) (c.dec.point.getD (P - 1) 0)
      ((ϱ.map FE2.toE2).getD 4 0) c.dec.weights ((ϱ.map FE2.toE2).drop 5) z * (s.map FE2.toE2).getD z 0 := by
  rw [treeSum_eq]
  simp only [treeSumF]
  rw [← coe_tE, map_treeFast]
  simp only [coe_tE]
  congr 1
  all_goals first
    | (funext i; simp [Function.comp, toE2_eqAtF, List.map_drop, toE2_arr_getD, toE2_getD, toE2_optGetD, KClaimF.dec])
    | simp [toE2_add', toE2_mul', toE2_one', toE2_getD, toE2_optGetD, KClaimF.dec]

/-- **Fast `treeEnd6 P`.** -/
def fTreeEnd6 (P : ℕ) (c : KClaimF) : VF EndOutF :=
  VF.bind (fSumcheck gC2 (treeV'F P c) 3 (List.replicate 11 none)) fun lv =>
  VF.bind (fE2Reads 64) fun s =>
  VF.guard (decide (multilinearEvalF c.mu (lv.1.take 4) * treeSumF P c lv.1 s = lv.2))
    (VF.pure ⟨lv.1, lv.1.take 4 ++ c.point.take (P - 1) ++ [lv.1.getD 4 0] ++ lv.1.drop 5, s⟩)

theorem tw_treeEnd6 (P : ℕ) (c : KClaimF) : TwinF EndOutF.dec (treeEnd6 P c.dec) (fTreeEnd6 P c) := by
  rw [treeEnd6, ← toE2_treeV'F]
  refine tw_bind (tw_sumcheckPlain gC2 3 11 _) fun lv => ?_
  refine tw_bind (tw_e2Reads 64) fun s => ?_
  refine tw_guard _ _ ?_ (tw_pure ?_)
  · have h : multilinearEvalF c.dec.mu ((scD lv).1.take 4) * ∑ z ∈ range 64, treeWt (c.dec.point.getD P 0)
        (c.dec.point.getD (P - 1) 0) ((scD lv).1.getD 4 0) c.dec.weights ((scD lv).1.drop 5) z *
          (s.map FE2.toE2).getD z 0 = FE2.toE2 (multilinearEvalF c.mu (lv.1.take 4) * treeSumF P c lv.1 s) := by
      rw [toE2_mul', toE2_treeSumF, toE2_multilinearEvalF, List.map_take]
      all_goals rfl
    exact (Eq.congr_left h).trans (toE2_eq_iff _ _)
  · simp only [EndOutF.dec, scD, KClaimF.dec, List.map_append, List.map_take, List.map_drop, List.map_cons,
      List.map_nil, toE2_getD]

/-! ## The sponge end -/

/-- The sponge end's final sum in the word field (`ϱ` = the 10 round challenges). -/
def spSumF (P : ℕ) (c : KClaimF) (ϱ s : List FE2) : FE2 :=
  let sA := s.toArray
  spFast (eqAtF [c.point.getD P 0]) (eqAtF (ϱ.drop 4)) (fun i => c.weights.getD i 0) (fun i => sA.getD i 0)

theorem toE2_spSumF (P : ℕ) (c : KClaimF) (ϱ s : List FE2) :
    FE2.toE2 (spSumF P c ϱ s) = ∑ z ∈ range 64, spWt (c.dec.point.getD P 0) c.dec.weights
      ((ϱ.map FE2.toE2).drop 4) z * (s.map FE2.toE2).getD z 0 := by
  rw [spSum_eq]
  simp only [spSumF]
  rw [← coe_tE, map_spFast]
  simp only [coe_tE]
  congr 1
  all_goals first
    | (funext i; simp [Function.comp, toE2_eqAtF, List.map_drop, toE2_arr_getD, toE2_getD, toE2_optGetD, KClaimF.dec])
    | simp [toE2_add', toE2_mul', toE2_one', toE2_getD, toE2_optGetD, KClaimF.dec]

/-- **Fast `spongeEnd6 P`.** -/
def fSpongeEnd6 (P : ℕ) (c : KClaimF) : VF EndOutF :=
  VF.bind (fSumcheck gC2 c.value 3 (List.replicate 10 none)) fun lv =>
  VF.bind (fE2Reads 64) fun s =>
  VF.guard (decide (multilinearEvalF c.mu (lv.1.take 4) * spSumF P c lv.1 s = lv.2))
    (VF.pure ⟨lv.1, lv.1.take 4 ++ c.point.take P ++ lv.1.drop 4, s⟩)

theorem tw_spongeEnd6 (P : ℕ) (c : KClaimF) : TwinF EndOutF.dec (spongeEnd6 P c.dec) (fSpongeEnd6 P c) := by
  rw [spongeEnd6]
  refine tw_bind (tw_sumcheckPlain gC2 3 10 c.value) fun lv => ?_
  refine tw_bind (tw_e2Reads 64) fun s => ?_
  refine tw_guard _ _ ?_ (tw_pure ?_)
  · have h : multilinearEvalF c.dec.mu ((scD lv).1.take 4) * ∑ z ∈ range 64, spWt (c.dec.point.getD P 0)
        c.dec.weights ((scD lv).1.drop 4) z * (s.map FE2.toE2).getD z 0 =
          FE2.toE2 (multilinearEvalF c.mu (lv.1.take 4) * spSumF P c lv.1 s) := by
      rw [toE2_mul', toE2_spSumF, toE2_multilinearEvalF, List.map_take]
      all_goals rfl
    exact (Eq.congr_left h).trans (toE2_eq_iff _ _)
  · simp only [EndOutF.dec, scD, KClaimF.dec, List.map_append, List.map_take, List.map_drop]

end Lvm6.V
