-- new for lvm (WP-9b): the bus phase, the table sumcheck and the fixed-column check of the lvm
-- instance in the form WP-14's `MidSpec` composes (`Doomed C (… ∧ R)` over the candidate pairs,
-- as WP-8's `kgSpec`), from the history-doom specs `lbusTableSpec` (LvmM3FidTab) and
-- `tableCheckSpec` (LvmM3FidFixC) through a gluing rule (`Spec.glue`, new).
import LvmM3FidFixC
import LvmFrontMech
import LvmLayoutStack
import LvmCpAmbientStacking
import LvmEqLemmas
import LvmCpFingerprint
import LvmM3Fid

-- ===== merged from `LvmFrontBusStack` (GOLF module merge: `LvmFrontBusStack.lean` is now a stub importing `LvmM3Mid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/BusStack.lean` (formal rev 40f877dc) as `LvmFrontBusStack` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.BusStack

  The verifier's stacking of a list of blocks (`stack_offsets` and the placements of
  `bus_layout`) is the oracle protocol's stacking of the same blocks sorted largest first: the same
  order, the same offsets, and each placement's weight `eq_above` at a point is the protocol's
  selector weight of the block.
-/

/-!
# Stacking a list of blocks

A list `L` of blocks with log-sizes `κ`: the verifier stacks the indices `0, …, n-1` by
`stack_offsets` (larger first, ties by index) and places block `i` at its offset; the protocol
sorts `L` largest first, stably (`sortedL`), and lays the blocks end to end (`blocksL`, the shape of
`Bus.blocks`). They are one layout:

* `sortedL_eq_map_ordL`: the sorted blocks are `L` read in the verifier's order `ordL`;
* `stackOffsets_getD_ordL`: the verifier's offset of the block at sorted position `b` is the
  protocol's offset of block `b`;
* `eqAbove_eq_selectorWeight`: the verifier's `eq_above` of that placement at a point is the
  protocol's selector weight of block `b`;
* `sum_selectorWeight_eq`: a sum over the protocol's blocks of the selector weight times a quantity
  of the block is the sum over the verifier's placements of `eq_above` times the quantity of the
  block at that index.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval

section

variable {α : Type} (L : List α) (κ : α → ℕ)

/-- The blocks sorted largest first, stably: `Bus.sorted`'s order. -/
def sortedL : List α := L.mergeSort fun a b ↦ decide (κ b ≤ κ a)

/-- The verifier's order of the indices: `stack_offsets`' stable sort by size. -/
def ordL : List ℕ :=
  (List.range L.length).mergeSort fun i j ↦ decide ((L.map κ).getD j 0 ≤ (L.map κ).getD i 0)

theorem ordL_perm : (ordL L κ).Perm (List.range L.length) := List.mergeSort_perm _ _

theorem length_ordL : (ordL L κ).length = L.length := by
  rw [(ordL_perm L κ).length_eq, List.length_range]

theorem length_sortedL : (sortedL L κ).length = L.length := List.length_mergeSort _

theorem ordL_lt {i : ℕ} (hi : i ∈ ordL L κ) : i < L.length :=
  List.mem_range.mp ((ordL_perm L κ).mem_iff.mp hi)

/-- **The sorted blocks are `L` in the verifier's order.** -/
theorem sortedL_eq_map_ordL (x₀ : α) : sortedL L κ = (ordL L κ).map fun i ↦ L.getD i x₀ := by
  rw [ordL, List.map_mergeSort (s := fun a b ↦ decide (κ b ≤ κ a))]
  · congr 1
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getElem?_eq_getElem h1]
  · intro a ha b hb
    rw [List.mem_range] at ha hb
    simp [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]

/-- The `b`-th sorted block. -/
theorem getElem_sortedL (x₀ : α) (b : ℕ) (hb : b < (sortedL L κ).length) :
    (sortedL L κ)[b] = L.getD ((ordL L κ)[b]'(by rw [length_ordL]; rwa [length_sortedL] at hb))
      x₀ := by
  simp only [sortedL_eq_map_ordL L κ x₀, List.getElem_map]

/-- **The verifier's offsets are prefix sums in the sorted order.** -/
theorem stackOffsets_getD_ordL (x₀ : α) (b : ℕ) (hb : b < L.length) :
    (stackOffsets (L.map κ)).1.getD ((ordL L κ)[b]'(by rwa [length_ordL])) 0 =
      (((sortedL L κ).take b).map fun a ↦ 2 ^ κ a).sum := by
  have hnd : (ordL L κ).Nodup := (ordL_perm L κ).nodup_iff.mpr List.nodup_range
  rw [stackOffsets_eq]
  simp only [List.length_map]
  change ((ordL L κ).foldl (placeStep fun i ↦ 2 ^ (L.map κ).getD i 0)
    (List.replicate L.length 0, 0)).1.getD _ 0 = _
  have hfold := placeFold_getElem? (fun i ↦ 2 ^ (L.map κ).getD i 0) (ordL L κ) hnd
    (List.replicate L.length 0, 0) (fun i hi ↦ by simpa using ordL_lt L κ hi) b
    (by rwa [length_ordL])
  rw [List.getD_eq_getElem?_getD, hfold, Option.getD_some, zero_add,
    sortedL_eq_map_ordL L κ x₀, ← List.map_take, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
  have hi' := ordL_lt L κ (List.mem_of_mem_take hi)
  simp [List.getElem?_eq_getElem hi']

/-! ## The protocol's layout of the sorted blocks -/

/-- A layout of the sorted blocks: its offsets are prefix sums in the sorted order. -/
theorem offsetNat_sortedL (B : Blocks) (hn : B.n = (sortedL L κ).length)
    (hs : ∀ b : Fin B.n, B.size b = κ ((sortedL L κ)[b.val]'(hn ▸ b.isLt))) (k : ℕ)
    (hk : k ≤ B.n) : B.offsetNat k = (((sortedL L κ).take k).map fun a ↦ 2 ^ κ a).sum := by
  induction k with
  | zero => simp [Blocks.offsetNat]
  | succ k ih =>
    rw [Blocks.offsetNat_succ _ k (by omega), ih (by omega),
      List.take_succ_eq_append_getElem (by omega), List.map_append, List.sum_append, hs]
    simp

/-! ## Placements and selector weights -/

/-- The verifier's placements of the blocks of sizes `sizes` (`bus_layout`). -/
def refPlacements (sizes : List ℕ) : List Placement :=
  List.zipWith (fun size offset ↦ ({ variableCount := size, index := offset } : Placement)) sizes
    (stackOffsets sizes).1

theorem length_stackOffsets_fst (sizes : List ℕ) :
    (stackOffsets sizes).1.length = sizes.length := by
  rw [stackOffsets_eq]
  simp only
  rw [placeFold_length, List.length_replicate]

theorem length_pyPlacements (sizes : List ℕ) : (refPlacements sizes).length = sizes.length := by
  simp [refPlacements, length_stackOffsets_fst]

/-- The placement of the block at sorted position `b`. -/
theorem refPlacements_getElem_ordL (x₀ : α) (b : ℕ) (hb : b < L.length) :
    (refPlacements (L.map κ))[(ordL L κ)[b]'(by rwa [length_ordL])]'(by
        rw [length_pyPlacements, List.length_map]
        exact ordL_lt L κ (List.getElem_mem _)) =
      { variableCount := κ ((sortedL L κ)[b]'(by rwa [length_sortedL])),
        index := (((sortedL L κ).take b).map fun a ↦ 2 ^ κ a).sum } := by
  have hi := ordL_lt L κ (List.getElem_mem (l := ordL L κ) (n := b) (by rwa [length_ordL]))
  simp only [refPlacements, List.getElem_zipWith, List.getElem_map]
  rw [← stackOffsets_getD_ordL L κ x₀ b hb, List.getD_eq_getElem _ _ (by
    rw [length_stackOffsets_fst, List.length_map]; exact hi), getElem_sortedL L κ x₀,
    List.getD_eq_getElem _ _ hi]

/-- `eq_eval` is symmetric. -/
theorem eqEval_comm (a b : List E) : eqEval a b = eqEval b a := by
  rw [eqEval_eq_list_prod, eqEval_eq_list_prod, List.zipWith_comm]
  have hf : (fun x y : E ↦ 1 + y + x) = fun x y ↦ 1 + x + y := by
    funext x y; ring
  rw [hf]

/-- The high coordinates of a point, as a list, are the point's list past the low ones. -/
theorem toList_highPoint (B : Blocks) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (z : Vector E μ) : (B.highPoint hμ b z).toList = z.toList.drop (B.size b) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [Blocks.highPoint, highVec]

/-- **`eq_above` is the selector weight**: the verifier's weight of a block placed at the protocol's
offset, at a point, is the protocol's selector weight of the block there. -/
theorem eqAbove_eq_selectorWeight (B : Blocks) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (z : Vector E μ) :
    ({ variableCount := B.size b, index := B.offset b } : Placement).eqAbove z.toList =
      B.selectorWeight hμ b z := by
  rw [Blocks.selectorWeight]
  have h := eqEval_boolPoint (B.highPoint hμ b z) (B.selector hμ b)
  rw [← h, toList_highPoint, eqEval_comm, Blocks.selector_val]
  simp only [Placement.eqAbove, Vector.length_toList, selectorPoint_eq_boolPoint,
    Nat.shiftRight_eq_div_pow]

/-! ## Sums over the blocks -/

/-- The verifier's order as a bijection of the sorted positions onto the indices. -/
theorem ordL_bijective (hn : (ordL L κ).length = L.length) :
    Function.Bijective fun b : Fin L.length ↦
      (⟨(ordL L κ)[b.val]'(by rw [hn]; exact b.isLt),
        ordL_lt L κ (List.getElem_mem _)⟩ : Fin L.length) := by
  have hnd : (ordL L κ).Nodup := (ordL_perm L κ).nodup_iff.mpr List.nodup_range
  constructor
  · intro a b hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext ((hnd.getElem_inj_iff).mp hab)
  · intro i
    have hi : i.val ∈ ordL L κ := (ordL_perm L κ).mem_iff.mpr (List.mem_range.mpr i.isLt)
    obtain ⟨b, hb, hbi⟩ := List.mem_iff_getElem.mp hi
    exact ⟨⟨b, by rwa [← hn]⟩, Fin.ext hbi⟩

/-- **A sum over the protocol's blocks is a sum over the verifier's placements**: the selector
weight of block `b` times a quantity of the `b`-th sorted block, summed over the blocks, is
`eq_above` of placement `i` times the quantity of block `i` of `L`, summed over the indices. -/
theorem sum_selectorWeight_eq (x₀ : α) (B : Blocks) (hn : B.n = (sortedL L κ).length)
    (hs : ∀ b : Fin B.n, B.size b = κ ((sortedL L κ)[b.val]'(hn ▸ b.isLt))) {μ : ℕ}
    (hμ : B.total ≤ 2 ^ μ) (z : Vector E μ) (F : α → E) :
    ∑ b : Fin B.n, B.selectorWeight hμ b z * F ((sortedL L κ)[b.val]'(hn ▸ b.isLt)) =
      ∑ i : Fin L.length, ((refPlacements (L.map κ))[i.val]'(by
        rw [length_pyPlacements, List.length_map]; exact i.isLt)).eqAbove z.toList * F L[i] := by
  have hn' : B.n = L.length := by rw [hn, length_sortedL]
  rw [← (Equiv.ofBijective _ (ordL_bijective L κ (length_ordL L κ))).sum_comp]
  rw [← (finCongr hn').sum_comp]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [Equiv.ofBijective_apply, finCongr_apply, Fin.val_cast]
  have hb : b.val < L.length := by rw [← hn']; exact b.isLt
  congr 1
  · rw [refPlacements_getElem_ordL L κ x₀ b hb, ← eqAbove_eq_selectorWeight B hμ b z, hs b,
      Blocks.offset, offsetNat_sortedL L κ B hn hs b b.isLt.le]
  · rw [getElem_sortedL L κ x₀, List.getD_eq_getElem _ _ (ordL_lt L κ (List.getElem_mem _))]
    rfl

end
end LeanVM.Protocol.EndToEnd.Front
end
-- ===== end of `LvmFrontBusStack` =====

-- ===== merged from `LvmFrontEqKernel` (GOLF module merge: `LvmFrontEqKernel.lean` is now a stub importing `LvmM3Mid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/EqKernel.lean` (formal rev 40f877dc) as `LvmFrontEqKernel` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.EqKernel

  The verifier program's equality kernel `eq_kernel(point)` is CompPoly's `lagrangeBasis`, the
  first coordinate the lowest bit.
-/

/-!
# The equality kernel

The verifier program (`LeanVM.Protocol.Verifier`; `crates/verifier/src/multilinear.rs:6-19` at
leanVM `40f877dc`) weighs the bus's tuple slots by `eq_kernel(alphas)` (`eqKernel`), built one
coordinate at a time, the first coordinate the lowest bit; the oracle protocol weighs them by
CompPoly's `lagrangeBasis` (`fingerprintWeights`).

* `eqKernel_snoc`: one more coordinate doubles the kernel;
* `eqKernel_getElem_prod`: the kernel's weight at `x` is `Π_j (r_j if bit j of x else 1 + r_j)`;
* `lagrangeBasis_ofFn_getD`: the kernel of a list is `lagrangeBasis` of its coordinates, in
  characteristic two.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval

section

/-- One more coordinate doubles the kernel: the old weights times `1 + r`, then times `r`. -/
theorem eqKernel_snoc (l : List E) (r : E) :
    eqKernel (l ++ [r]) = (eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r) := by
  simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **The kernel's weight at `x`**: `Π_j (r_j if bit j of x else 1 + r_j)`, the first coordinate
the lowest bit. -/
theorem eqKernel_getElem_prod (l : List E) (x : ℕ) (hx : x < (eqKernel l).length) :
    (eqKernel l)[x] =
      ∏ j ∈ Finset.range l.length, (if x.testBit j then l.getD j 0 else 1 + l.getD j 0) := by
  induction l using List.reverseRecOn generalizing x with
  | nil =>
    have : x = 0 := by simpa [eqKernel] using hx
    subst this
    rfl
  | append_singleton l r ih =>
    have hlen := Whir.Complete.length_eqKernel l
    have hgetD : ∀ j < l.length, (l ++ [r]).getD j 0 = l.getD j 0 := fun j hj ↦ by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have hlast : (l ++ [r]).getD l.length 0 = r := by simp [List.getD_eq_getElem?_getD]
    simp only [eqKernel_snoc]
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
    by_cases hlo : x < 2 ^ l.length
    · rw [List.getElem_append_left (by simp [hlen, hlo]), List.getElem_map,
        ih x (by rw [hlen]; exact hlo), Nat.testBit_lt_two_pow hlo, hlast]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by rw [hgetD j (Finset.mem_range.mp hj)]
    · have hx' : x < 2 ^ l.length + 2 ^ l.length := by
        simp [eqKernel_snoc, hlen] at hx
        omega
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ l.length + y := ⟨x - 2 ^ l.length, by omega⟩
      have hy : y < 2 ^ l.length := by omega
      rw [List.getElem_append_right (by simp [hlen]), List.getElem_map]
      simp only [List.length_map, hlen, Nat.add_sub_cancel_left]
      rw [ih y (by rw [hlen]; exact hy), Nat.testBit_two_pow_add_eq,
        Nat.testBit_lt_two_pow hy, hlast]
      simp only [Bool.not_false, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by
        rw [hgetD j (Finset.mem_range.mp hj),
          Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hj)]

/-- **The program's kernel is CompPoly's `lagrangeBasis`**, the first coordinate the lowest bit,
in characteristic two. -/
theorem lagrangeBasis_ofFn_getD {n : ℕ} {l : List E} (hl : l.length = n) (x : Fin (2 ^ n)) :
    (lagrangeBasis (Vector.ofFn fun i : Fin n ↦ l.getD i 0))[x] =
      (eqKernel l)[x.val]'(by rw [Whir.Complete.length_eqKernel, hl]; exact x.isLt) := by
  rw [lagrangeBasis_getElem, eqKernel_getElem_prod, hl,
    ← Fin.prod_univ_eq_prod_range (fun j ↦ if x.val.testBit j then l.getD j 0 else 1 + l.getD j 0)]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [BitVec.getLsb_eq_getElem, BitVec.getElem_ofFin, Fin.getElem_fin,
    Vector.getElem_ofFn, CharTwo.sub_eq_add]

end
end LeanVM.Protocol.EndToEnd.Front
end
-- ===== end of `LvmFrontEqKernel` =====

-- ===== merged from `LvmM3FidBus` (GOLF module merge: `LvmM3FidBus.lean` is now a stub importing `LvmM3Mid`) =====
section
-- adapted from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/TableFidLeanIsaBus.lean` (formal
-- rev 40f877dc): `formAt_append`, `formAt_flatMap`, `formAt_form`, `evalRow_oneRow`,
-- `fingerprintWeights_toAlpha`, `sum_zipIdx`; new for lvm (WP-9b): the lvm instance's leaf
-- decomposition is the program's (`busResV`, `LvmM3Fid`): `totals_busResV`, `formAt_busResV`.

/-!
# The lvm bus result is the protocol's

For the lvm instance `I = inst L tabs hτ` with every table a sumcheck table (`AllSc`), at a read of
the bus phase with four fingerprint challenges, the GKR point on `μ_bus` coordinates and three
values:

* `totals_busResV`: the program's side totals `v + 1 + Σ_b w_b` are the protocol's
  (`Bus.total`: no boundary block, and no padding row since `rows = 2^τ`, so no public part);
* `formAt_busResV`: the program's form of a side and a table, evaluated at the table's values, is the
  protocol's (`Bus.forms`), when every message has at most thirteen value limbs (`KeysOk`).

The program's blocks are the protocol's sources in order (`sideBlocksV_eq`, through `vsrc`), its
stacking is the protocol's sorted layout (`stackBlocksV_eq`, `sum_sides`), its block weight
`eq_above` is the selector weight (`eqAbove_eq_selectorWeight`), and a block's leaf form is its
flush's fingerprint form (`formAt_src`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open CompPoly CMlPolynomialEval
open LeanVM.Protocol.TableSumcheck (formAt evalRow)

/-! ## Sums and forms over `E` -/

theorem foldl_add_E (a : E) (l : List E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem sumE_eq_sum (l : List E) : sumE l = l.sum := by
  rw [sumE, foldl_add_E, zero_add]

theorem foldl_mul_col (col : ℕ → E) (c : E) (l : List ℕ) :
    l.foldl (fun acc i ↦ acc * col i) c = c * (l.map col).prod := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- A form's value: `Σ c · Π column(i)`. -/
theorem evaluate_eq (f : Form) (col : ℕ → E) :
    f.evaluate col = (f.terms.map fun t ↦ t.2 * (t.1.map col).prod).sum := by
  rw [Form.evaluate, sumE_eq_sum]
  exact congrArg List.sum (List.map_congr_left fun t _ ↦ foldl_mul_col col t.2 t.1)

theorem evaluate_append (a b : List (List ℕ × E)) (col : ℕ → E) :
    (⟨a ++ b⟩ : Form).evaluate col = (⟨a⟩ : Form).evaluate col + (⟨b⟩ : Form).evaluate col := by
  simp only [evaluate_eq, List.map_append, List.sum_append]

theorem evaluate_flatMap {X : Type} (g : X → List (List ℕ × E)) (col : ℕ → E) (l : List X) :
    (⟨l.flatMap g⟩ : Form).evaluate col = (l.map fun x ↦ (⟨g x⟩ : Form).evaluate col).sum := by
  induction l with
  | nil => simp [evaluate_eq]
  | cons x l ih => rw [List.flatMap_cons, evaluate_append, ih, List.map_cons, List.sum_cons]

theorem evaluate_scale (w : E) (ts : List (List ℕ × E)) (col : ℕ → E) :
    (⟨ts.map fun t ↦ (t.1, w * t.2)⟩ : Form).evaluate col = w * (⟨ts⟩ : Form).evaluate col := by
  simp only [evaluate_eq, List.map_map, Function.comp_def, ← List.sum_map_mul_left, mul_assoc]

/-- A table's bucket on a side, evaluated: its blocks' weighted values. -/
theorem evaluate_bucketV (s : List (VBlock × E)) (j : ℕ) (col : ℕ → E) :
    (⟨bucketV s j⟩ : Form).evaluate col =
      (s.map fun bw ↦ bw.2 * if bw.1.tab = j then bw.1.form.evaluate col else 0).sum := by
  rw [bucketV, evaluate_flatMap, List.map_reverse, List.sum_reverse]
  induction s with
  | nil => simp
  | cons bw s ih =>
    by_cases h : bw.1.tab = j
    · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ih,
        List.map_cons, List.sum_cons, if_pos h, evaluate_scale]
    · rw [List.filter_cons_of_neg (by simpa using h), ih, List.map_cons, List.sum_cons, if_neg h,
        mul_zero, zero_add]

/-- The value of a `CPoly` at a row. -/
theorem evalV_eq (v : ℕ → E) (P : CPoly) :
    CPoly.evalV v P = (P.map fun m ↦ kE m.1 * (m.2.map v).prod).sum := by
  rw [CPoly.evalV, foldl_add_E, zero_add]
  refine congrArg List.sum (List.map_congr_left fun m _ ↦ ?_)
  rw [← List.prod_eq_foldl]

theorem evaluate_cpolyFormV (w : E) (P : CPoly) (col : ℕ → E) :
    (cpolyFormV w P).evaluate col = w * CPoly.evalV col P := by
  rw [cpolyFormV, evaluate_eq, evalV_eq, List.map_map, ← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun m _ ↦ by simp [mul_assoc])

theorem evaluate_const (c : E) (col : ℕ → E) : (Form.const c).evaluate col = c := by
  simp [Form.const, evaluate_eq]

theorem evaluate_formSumV (fs : List Form) (col : ℕ → E) :
    (formSumV fs).evaluate col = (fs.map (·.evaluate col)).sum := by
  rw [formSumV, evaluate_flatMap]

/-- A sum over a list with its indices is a sum over the indices. -/
theorem sum_zipIdx {α : Type} (g : ℕ → α → E) (d : α) :
    ∀ (l : List α) (n : ℕ), ((l.zipIdx n).map fun x ↦ g x.2 x.1).sum =
      ∑ k ∈ Finset.range l.length, g (n + k) (l.getD k d)
  | [], _ => by simp
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx g d l (n + 1),
      List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ ↦ by rw [add_assoc, add_comm 1 k])
      rfl

/-- **A leaf form's value**: `β + eq(α,0)·sep + eq(α,1)·addr + eq(α,2)·cnt + Σ_l eq(α,3+l)·val_l`. -/
theorem evaluate_leafFormV (eqα : List E) (β : E) (k : Key) (cnt : CPoly) (col : ℕ → E) :
    (leafFormV eqα β k cnt).evaluate col = β + eqα.getD 0 0 * kE k.sep +
      eqα.getD 1 0 * CPoly.evalV col k.addr + eqα.getD 2 0 * CPoly.evalV col cnt +
      ∑ l ∈ Finset.range k.val.length, eqα.getD (3 + l) 0 * CPoly.evalV col (k.val.getD l []) := by
  rw [leafFormV, evaluate_formSumV, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, evaluate_const,
    evaluate_cpolyFormV, add_zero, List.map_map, Function.comp_def]
  rw [sum_zipIdx (fun l P ↦ eqα.getD (3 + l) 0 * CPoly.evalV col P) [] k.val 0]
  simp only [zero_add]
  ring

/-! ## The instance -/

section Inst

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- Every table of the instance is a sumcheck table. -/
theorem sumcheckTable_of (hsc : AllSc tabs) (j : Fin tabs.length) :
    (inst L tabs hτ).SumcheckTable j := by
  right; left
  show (tabs.get j).flushes ≠ []
  have hl : (tabs.get j).flushes.length =
      2 * (tabs.get j).reads.length + 2 * (tabs.get j).seeds.length := by
    simp [Tab.flushes]; ring
  apply List.ne_nil_of_length_pos
  rw [hl]
  rcases hsc (tabs.get j) (List.get_mem _ _) with h | h
  · have := List.length_pos_of_ne_nil h; (clear * - hl this; omega)
  · have := List.length_pos_of_ne_nil h; (clear * - hl this; omega)

/-- The bus conditions of the instance when every table is a sumcheck table. -/
theorem condOf (hsc : AllSc tabs) : Bus.Conditions (inst L tabs hτ) :=
  inst_conditions L tabs hτ fun t ht _ ↦ hsc t ht

end Inst

/-! ## A table's flushes, as keys and counts -/

/-- A table's flushes: side, key and count, in `Tab.flushes`' order. -/
def Tab.kcs (t : Tab) : List (Side × Key × CPoly) :=
  t.reads.map (fun r ↦ (.pull, r.1, CPoly.var r.2)) ++
    t.reads.map (fun r ↦ (.push, r.1, [(FK.x, [r.2])])) ++
    t.seeds.map (fun s ↦ (.push, s.1, CPoly.const 1)) ++
    t.seeds.map (fun s ↦ (.pull, s.1, CPoly.var s.2))

theorem flushes_eq_kcs (t : Tab) : t.flushes = t.kcs.map fun x ↦ (x.1, x.2.1.vec t.w x.2.2) := by
  simp [Tab.flushes, Tab.kcs, Tab.readVec, Tab.bumpVec, Tab.seedVec, Tab.finVec,
    Function.comp_def]

theorem length_kcs (t : Tab) : t.kcs.length = t.flushes.length := by
  rw [flushes_eq_kcs, List.length_map]

/-- The default key and count. -/
def kc0 : Side × Key × CPoly := (.push, ⟨0, [], []⟩, [])

/-- Flush `f` of a table is its key's message at its count. -/
theorem flushes_getElem (t : Tab) (f : ℕ) (hf : f < t.flushes.length) :
    t.flushes[f] = ((t.kcs.getD f kc0).1, (t.kcs.getD f kc0).2.1.vec t.w (t.kcs.getD f kc0).2.2) := by
  have hf' : f < t.kcs.length := by rw [length_kcs]; exact hf
  simp only [List.getElem_of_eq (flushes_eq_kcs t) hf, List.getElem_map,
    List.getD_eq_getElem _ _ hf']

/-- The filtered indices of a list, read back through `getD`. -/
theorem filter_finRange_getD {A B : Type} (p : A → Bool) (G : A → B) (d : A) :
    ∀ (l : List A), ((List.finRange l.length).filter fun i ↦ p (l.getD i.val d)).map
      (fun i ↦ G (l.getD i.val d)) = (l.filter p).map G
  | [] => rfl
  | a :: l => by
    have ih := filter_finRange_getD p G d l
    rw [List.length_cons, List.finRange_succ, List.filter_cons, List.filter_map]
    have e1 : ((fun i : Fin (l.length + 1) ↦ p ((a :: l).getD i.val d)) ∘ Fin.succ) =
        fun i : Fin l.length ↦ p (l.getD i.val d) := funext fun _ ↦ rfl
    have e2 : ((fun i : Fin (l.length + 1) ↦ G ((a :: l).getD i.val d)) ∘ Fin.succ) =
        fun i : Fin l.length ↦ G (l.getD i.val d) := funext fun _ ↦ rfl
    have e0 : (a :: l).getD (0 : Fin (l.length + 1)).val d = a := rfl
    rw [e1, e0]
    by_cases h : p a
    · rw [if_pos h, List.map_cons, List.map_map, e2, ih, List.filter_cons_of_pos h, List.map_cons, e0]
    · rw [if_neg h, List.map_map, e2, ih, List.filter_cons_of_neg h]

theorem zipIdx_eq_finRange {α : Type} (l : List α) :
    l.zipIdx = (List.finRange l.length).map fun j ↦ (l.get j, j.val) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx]

/-! ## The program's blocks are the protocol's sources -/

section Sources

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (eqα : List E) (β : E)

/-- **The program's block of a source** of the lvm instance. -/
def vsrc : Bus.Source (inst L tabs hτ) → VBlock
  | .boundary b => ⟨0, b.κ, {}⟩
  | .flush j f => ⟨j.val, (tabs.get j).τ,
      leafFormV eqα β ((tabs.get j).kcs.getD f.val kc0).2.1 ((tabs.get j).kcs.getD f.val kc0).2.2⟩
  | .count j c => ⟨j.val, (tabs.get j).τ, Form.col c.val⟩

theorem vsrc_κ (s : Bus.Source (inst L tabs hτ)) : (vsrc L tabs hτ eqα β s).κ = s.κ := by
  cases s <;> rfl

/-- Table `j`'s flushes of side `s`, as the program's blocks. -/
theorem side_map_vsrc (s : Side) (j : Fin tabs.length) :
    (((List.finRange ((inst L tabs hτ).flushes j).length).filter fun f ↦
        decide (((inst L tabs hτ).flushes j)[f].1 = s)).map (Bus.Source.flush j)).map
      (vsrc L tabs hτ eqα β) =
    ((tabs.get j).kcs.filter fun x ↦ decide (x.1 = s)).map fun x ↦
      (⟨j.val, (tabs.get j).τ, leafFormV eqα β x.2.1 x.2.2⟩ : VBlock) := by
  rw [List.map_map]
  have hlen : ((inst L tabs hτ).flushes j).length = (tabs.get j).kcs.length :=
    (length_kcs _).symm
  have key := filter_finRange_getD (fun x : Side × Key × CPoly ↦ decide (x.1 = s))
    (fun x ↦ (⟨j.val, (tabs.get j).τ, leafFormV eqα β x.2.1 x.2.2⟩ : VBlock)) kc0 (tabs.get j).kcs
  rw [← key]
  have : ∀ (n m : ℕ) (h : n = m) (P : Fin n → Bool) (Q : Fin m → Bool) (F : Fin n → VBlock)
      (G : Fin m → VBlock), (∀ i, P i = Q (Fin.cast h i)) → (∀ i, F i = G (Fin.cast h i)) →
      ((List.finRange n).filter P).map F = ((List.finRange m).filter Q).map G := by
    intro n m h P Q F G hP hF
    subst h
    have hP' : P = Q := funext fun i ↦ hP i
    have hF' : F = G := funext fun i ↦ hF i
    rw [hP', hF']
  refine this _ _ hlen _ _ _ _ (fun f ↦ ?_) (fun f ↦ rfl)
  show decide ((((tabs.get j).flushes)[f.val]'f.isLt).1 = s) = _
  rw [flushes_getElem]
  rfl

theorem kcs_push (t : Tab) : (t.kcs.filter fun x ↦ decide (x.1 = Side.push)) =
    t.reads.map (fun r ↦ (.push, r.1, [(FK.x, [r.2])])) ++
      t.seeds.map (fun s ↦ (.push, s.1, CPoly.const 1)) := by
  simp [Tab.kcs, List.filter_append, List.filter_map, Function.comp_def]

theorem kcs_pull (t : Tab) : (t.kcs.filter fun x ↦ decide (x.1 = Side.pull)) =
    t.reads.map (fun r ↦ (.pull, r.1, CPoly.var r.2)) ++
      t.seeds.map (fun s ↦ (.pull, s.1, CPoly.var s.2)) := by
  simp [Tab.kcs, List.filter_append, List.filter_map, Function.comp_def]

/-- **The program's blocks of a side are the protocol's sources**, in order. -/
theorem sideBlocksV_eq :
    sideBlocksV tabs eqα β = [(Bus.sources (inst L tabs hτ) 0).map (vsrc L tabs hτ eqα β),
      (Bus.sources (inst L tabs hτ) 1).map (vsrc L tabs hτ eqα β),
      (Bus.sources (inst L tabs hτ) 2).map (vsrc L tabs hτ eqα β)] := by
  have hb : (inst L tabs hτ).boundary = [] := rfl
  simp only [sideBlocksV, Bus.sources, Bus.sideSources, Bus.countSources, hb, List.filter_nil,
    List.map_nil, List.nil_append, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, List.map_flatMap, zipIdx_eq_finRange, List.flatMap_map]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  · refine congrArg (List.flatMap · _) (funext fun j ↦ ?_)
    rw [side_map_vsrc, kcs_push]
    simp [Function.comp_def]
  · refine congrArg (List.flatMap · _) (funext fun j ↦ ?_)
    rw [side_map_vsrc, kcs_pull]
    simp [Function.comp_def]
  · refine congrArg (List.flatMap · _) (funext fun j ↦ ?_)
    rw [List.map_map]
    rfl

end Sources

/-! ## Stacking -/

/-- `stackBlocksV`'s fold: each block at the sum of the heights before it. -/
theorem stack_fold (l : List VBlock) (acc : List (VBlock × ℕ)) (o : ℕ) :
    l.foldl (fun (acc : List (VBlock × ℕ) × ℕ) b ↦ (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ))
        (acc, o) =
      (acc ++ l.mapIdx (fun i b ↦ (b, o + ((l.take i).map fun b ↦ 2 ^ b.κ).sum)),
        o + (l.map fun b ↦ 2 ^ b.κ).sum) := by
  induction l generalizing acc o with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih]
    simp only [List.mapIdx_cons, List.take_zero, List.map_nil, List.sum_nil, add_zero,
      List.take_succ_cons, List.map_cons, List.sum_cons, List.append_assoc, List.singleton_append,
      Prod.mk.injEq, add_assoc, true_and]

/-- A sum over a `mapIdx`, as a sum over the positions. -/
theorem sum_map_mapIdx {X Y : Type} (g : Y → E) :
    ∀ (l : List X) (f : ℕ → X → Y), ((l.mapIdx f).map g).sum = ∑ i : Fin l.length, g (f i l[i])
  | [], _ => by simp
  | a :: l, f => by
    rw [List.mapIdx_cons, List.map_cons, List.sum_cons, sum_map_mapIdx g l]
    exact (Fin.sum_univ_succ (n := l.length) (fun i ↦ g (f i (a :: l)[i]))).symm

/-- **A weighted sum over a side's stacked blocks** is the protocol's sum over its sorted blocks,
each at its selector weight. -/
theorem sum_stack {I : M3Instance} (hI : Bus.Conditions I) (k : Fin 3)
    (φ : Bus.Source I → VBlock) (hφ : ∀ s, (φ s).κ = s.κ) (point : List E)
    (hp : point.length = I.μBus) (G : VBlock → E) :
    (((stackBlocksV ((Bus.sources I k).map φ)).map fun bo ↦
        (bo.1, blockWeightV point bo.1.κ bo.2)).map fun bw ↦ bw.2 * G bw.1).sum =
      ∑ b : Fin (Bus.blocks I k).n, Bus.weight hI k b (vecOf I.μBus point) *
        G (φ (Bus.src I k b)) := by
  have hsort : ((Bus.sources I k).map φ).mergeSort (fun a b ↦ decide (b.κ ≤ a.κ)) =
      (Bus.sorted I k).map φ :=
    (List.map_mergeSort (fun a _ b _ ↦ by simp only [hφ])).symm
  have hstack : stackBlocksV ((Bus.sources I k).map φ) = ((Bus.sorted I k).map φ).mapIdx
      fun i b ↦ (b, ((((Bus.sorted I k).map φ).take i).map fun b ↦ 2 ^ b.κ).sum) := by
    rw [stackBlocksV, hsort, stack_fold]
    simp
  rw [hstack, List.map_map, sum_map_mapIdx]
  have hn : ((Bus.sorted I k).map φ).length = (Bus.blocks I k).n := by
    rw [List.length_map]; rfl
  refine Fintype.sum_equiv (finCongr hn) _ _ fun i ↦ ?_
  simp only [Function.comp_apply, List.getElem_map, finCongr_apply]
  congr 1
  have hoff : ((((Bus.sorted I k).map φ).take i.val).map fun b ↦ 2 ^ b.κ).sum =
      (Bus.blocks I k).offset (Fin.cast hn i) := by
    rw [Blocks.offset, offsetNat_sortedL (Bus.sources I k) Bus.Source.κ (Bus.blocks I k) rfl
      (fun _ ↦ rfl) _ (by simp only [Fin.val_cast]; (clear * - hn; omega)), ← List.map_take, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun a _ ↦ by simp [hφ])
  have hκ : ((Bus.sorted I k).map φ)[i].κ = (Bus.blocks I k).size (Fin.cast hn i) := by
    simp only [Fin.getElem_fin, List.getElem_map, hφ]
    rfl
  have h := eqAbove_eq_selectorWeight (Bus.blocks I k) (hI.fits k) (Fin.cast hn i)
    (vecOf I.μBus point)
  rw [toList_vecOf point hp] at h
  rw [hoff, blockWeightV, hκ, h]
  simp only [Fin.getElem_fin, List.getElem_map]
  rfl

/-! ## Row polynomials at values in `E` -/

/-- Values of a table's `n` columns, read by index with zeros past the width (leanVM `rowE`). -/
def rowE {n : ℕ} (e : Fin n → E) : ℕ → E := fun i ↦ if h : i < n then e ⟨i, h⟩ else 0

theorem eval₂_xv {w : ℕ} (e : Fin w → E) (i : ℕ) :
    MvPolynomial.eval₂ (algebraMap K E) e (CPoly.xv w i) = rowE e i := by
  unfold CPoly.xv rowE; split <;> simp

/-- **A `CPoly` as a row polynomial**, at values in `E`, is its value at the row. -/
theorem eval₂_toMv {w : ℕ} (e : Fin w → E) (P : CPoly) :
    MvPolynomial.eval₂ (algebraMap K E) e (CPoly.toMv w P) = CPoly.evalV (rowE e) P := by
  rw [evalV_eq]
  have h : ∀ q, MvPolynomial.eval₂ (algebraMap K E) e q =
      MvPolynomial.eval₂Hom (algebraMap K E) e q := fun _ ↦ rfl
  rw [h]
  unfold CPoly.toMv
  induction P with
  | nil => simp
  | cons m P ih =>
    rw [List.map_cons, List.sum_cons, map_add, ih, List.map_cons, List.sum_cons, map_mul,
      MvPolynomial.eval₂Hom_C, map_list_prod, List.map_map]
    congr 2
    exact congrArg List.prod (List.map_congr_left fun i _ ↦ eval₂_xv e i)

/-! ## Forms of the protocol (leanVM `TableFidLeanIsaBus`, generic part) -/

section Generic

variable {I : M3Instance}

/-- `formAt` of a concatenation is the sum of the parts'. -/
theorem formAt_append {j : Fin I.ntab} (a b : I.Form j) (e : Fin (I.width j) → E) :
    formAt (a ++ b) e = formAt a e + formAt b e := by
  simp [formAt]

/-- `formAt` of a `flatMap` is the sum of the pieces'. -/
theorem formAt_flatMap {α : Type} {j : Fin I.ntab} (g : α → I.Form j) (e : Fin (I.width j) → E) :
    ∀ l : List α, formAt (l.flatMap g) e = (l.map fun x ↦ formAt (g x) e).sum
  | [] => by simp [formAt]
  | x :: l => by rw [List.flatMap_cons, formAt_append, formAt_flatMap g e l]; simp

/-- The constant row `1` evaluates to `1`. -/
theorem evalRow_oneRow (j : Fin I.ntab) (e : Fin (I.width j) → E) :
    evalRow (Bus.oneRow j).1 e = 1 := by
  simp [evalRow, Bus.oneRow]

/-- **A block's form is linear in its weight.** -/
theorem formAt_form (src : Bus.Source I) (hd : 1 ≤ I.d) (w : E) (α : Fin 4 → E) (β : E)
    (j : Fin I.ntab) (e : Fin (I.width j) → E) :
    formAt (src.form hd w α β j) e = w * formAt (src.form hd 1 α β j) e := by
  cases src with
  | boundary b => simp [Bus.Source.form, formAt]
  | flush j' f =>
    by_cases hj : j' = j
    · subst hj
      simp only [Bus.Source.form, dite_true, Bus.flushForm, formAt, List.map_cons, List.sum_cons,
        List.map_map, Function.comp_def]
      rw [mul_add, ← List.sum_map_mul_left]
      exact congrArg₂ (· + ·) (by ring) (congrArg List.sum (List.map_congr_left fun i _ ↦ by ring))
    · simp [Bus.Source.form, hj, formAt]
  | count j' c =>
    by_cases hj : j' = j
    · subst hj
      simp only [Bus.Source.form, dite_true, Bus.countForm, formAt, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      ring
    · simp [Bus.Source.form, hj, formAt]

/-- The protocol's form of a side and a sumcheck table, evaluated: the sum over the sorted blocks
of the selector weight times the block's form at weight `1`. -/
theorem formAt_forms (hI : Bus.Conditions I) (k : Fin 3) (α : Fin 4 → E) (β : E)
    (ζ : Vector E I.μBus) (j : I.SumcheckTables) (e : Fin (I.width j.1) → E) :
    formAt (Bus.forms hI k α β ζ j) e = ∑ b : Fin (Bus.blocks I k).n, Bus.weight hI k b ζ *
      formAt ((Bus.src I k b).form hI.one_le_d 1 α β j.1) e := by
  rw [Bus.forms, formAt_flatMap, ← Fin.sum_univ_def]
  exact Finset.sum_congr rfl fun b _ ↦ formAt_form _ _ _ _ _ _ _

end Generic

/-- The wire's weights are the protocol's fingerprint weights, for four `α`. -/
theorem fingerprintWeights_toAlpha {alphas : List E} (ha : alphas.length = 4) (k : Fin 16) :
    (fingerprintWeights (toAlpha alphas))[k.val] = (eqKernel alphas).getD k 0 := by
  have h := lagrangeBasis_ofFn_getD ha k
  rw [List.getD_eq_getElem _ _ (by rw [Whir.Complete.length_eqKernel, ha]; exact k.isLt)]
  exact h

/-- A flush's form at weight `1`: `β + Σ_i eq(α, i)·coord_i` (characteristic two). -/
theorem formAt_flushForm {I : M3Instance} (j : Fin I.ntab) (f : Fin (I.flushes j).length)
    (α : Fin 4 → E) (β : E) (e : Fin (I.width j) → E) :
    formAt (Bus.flushForm j f 1 α β) e = β + ∑ i : Fin 16, (fingerprintWeights α)[i.val] *
      MvPolynomial.eval₂ (algebraMap K E) e (Bus.flushPolys j f)[i] := by
  simp only [Bus.flushForm, formAt, List.map_cons, List.sum_cons, List.map_map, evalRow_oneRow,
    one_mul, mul_one]
  rw [Fin.sum_univ_def]
  refine congrArg (β + ·) (congrArg List.sum (List.map_congr_left fun i _ ↦ ?_))
  simp only [Function.comp_apply, evalRow, CharTwo.neg_eq]

/-! ## A message's coordinates -/

/-- Coordinate `i` of the message with key `k` and count `cnt`, at a row of `E` values. -/
def kvV (k : Key) (cnt : CPoly) (v : ℕ → E) (i : ℕ) : E :=
  if i = 0 then kE k.sep else if i = 1 then CPoly.evalV v k.addr
  else if i = 2 then CPoly.evalV v cnt else CPoly.evalV v (k.val.getD (i - 3) [])

theorem eval₂_vec {w : ℕ} (k : Key) (cnt : CPoly) (e : Fin w → E) (i : Fin 16) :
    MvPolynomial.eval₂ (algebraMap K E) e (k.vec w cnt)[i] = kvV k cnt (rowE e) i := by
  simp only [Key.vec, Fin.getElem_fin, Vector.getElem_ofFn, kvV]
  split_ifs <;> first | rfl | (rw [MvPolynomial.eval₂_C]; rfl) | exact eval₂_toMv e _

theorem evalV_nil (v : ℕ → E) : CPoly.evalV v [] = 0 := by simp [CPoly.evalV]

/-- **The sixteen weighted coordinates** of a message with at most thirteen value limbs. -/
theorem sum_kvV (eqα : List E) (k : Key) (cnt : CPoly) (v : ℕ → E) (hk : k.val.length ≤ 13) :
    ∑ i : Fin 16, eqα.getD i 0 * kvV k cnt v i = eqα.getD 0 0 * kE k.sep +
      eqα.getD 1 0 * CPoly.evalV v k.addr + eqα.getD 2 0 * CPoly.evalV v cnt +
      ∑ l ∈ Finset.range k.val.length, eqα.getD (3 + l) 0 * CPoly.evalV v (k.val.getD l []) := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ eqα.getD i 0 * kvV k cnt v i) 16,
    Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have h13 : ∑ i ∈ Finset.range 13, eqα.getD (i + 1 + 1 + 1) 0 * kvV k cnt v (i + 1 + 1 + 1) =
      ∑ l ∈ Finset.range k.val.length, eqα.getD (3 + l) 0 * CPoly.evalV v (k.val.getD l []) := by
    rw [← Finset.sum_range_add_sum_Ico _ hk]
    have hz : ∑ i ∈ Finset.Ico k.val.length 13,
        eqα.getD (i + 1 + 1 + 1) 0 * kvV k cnt v (i + 1 + 1 + 1) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by
        have hi' := (Finset.mem_Ico.mp hi).1
        simp only [kvV, show i + 1 + 1 + 1 - 3 = i by (clear * -; omega),
          List.getD_eq_default _ _ hi', evalV_nil]
        simp
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show i + 1 + 1 + 1 = 3 + i by (clear * -; omega)]
    simp only [kvV, if_neg (by (clear * -; omega) : 3 + i ≠ 0), if_neg (by (clear * -; omega) : 3 + i ≠ 1),
      if_neg (by (clear * -; omega) : 3 + i ≠ 2), show 3 + i - 3 = i by (clear * -; omega)]
  rw [h13]
  simp only [kvV]
  simp
  ring

/-- The default key has no value limb. -/
theorem kcs_getD_val (t : Tab) (hk : (∀ r ∈ t.reads, r.1.val.length ≤ 13) ∧
    ∀ s ∈ t.seeds, s.1.val.length ≤ 13) (f : ℕ) : (t.kcs.getD f kc0).2.1.val.length ≤ 13 := by
  by_cases hf : f < t.kcs.length
  · rw [List.getD_eq_getElem _ _ hf]
    have hm := List.getElem_mem hf
    generalize t.kcs[f] = x at hm ⊢
    simp only [Tab.kcs, List.mem_append, List.mem_map] at hm
    rcases hm with (((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩)
    · exact hk.1 r hr
    · exact hk.1 r hr
    · exact hk.2 s hs
    · exact hk.2 s hs
  · rw [List.getD_eq_default _ _ (by (clear * - hf; omega))]
    simp [kc0]

/-- Every message of the tables has at most thirteen value limbs (sixteen coordinates). -/
def KeysOk (tabs : List Tab) : Prop :=
  ∀ t ∈ tabs, (∀ r ∈ t.reads, r.1.val.length ≤ 13) ∧ ∀ s ∈ t.seeds, s.1.val.length ≤ 13

/-! ## The program's blocks' forms are the protocol's -/

section Result

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- **A source's form at weight `1` is its program block's**, on the block's table. -/
theorem formAt_src (hkey : KeysOk tabs) {alphas : List E} (ha : alphas.length = 4) (β : E)
    (hd : 1 ≤ (inst L tabs hτ).d) (s : Bus.Source (inst L tabs hτ)) (j : Fin tabs.length)
    (e : Fin ((inst L tabs hτ).width j) → E) :
    formAt (s.form hd 1 (toAlpha alphas) β j) e =
      if (vsrc L tabs hτ (eqKernel alphas) β s).tab = j.val then
        (vsrc L tabs hτ (eqKernel alphas) β s).form.evaluate (rowE e) else 0 := by
  cases s with
  | boundary b => simp [Bus.Source.form, formAt, vsrc, evaluate_eq]
  | flush j' f =>
    by_cases hj : j' = j
    · subst hj
      simp only [Bus.Source.form, dite_true, vsrc, if_true]
      rw [formAt_flushForm, evaluate_leafFormV]
      have hfp : Bus.flushPolys (I := inst L tabs hτ) j' f =
          ((tabs.get j').kcs.getD f.val kc0).2.1.vec (tabs.get j').w
            ((tabs.get j').kcs.getD f.val kc0).2.2 := by
        show ((tabs.get j').flushes[f.val]'f.isLt).2 = _
        rw [flushes_getElem]
      rw [hfp]
      simp only [eval₂_vec, fingerprintWeights_toAlpha ha]
      rw [sum_kvV _ _ _ _ (kcs_getD_val _ (hkey _ (List.get_mem _ _)) _)]
      ring
    · have hj' : j'.val ≠ j.val := fun h ↦ hj (Fin.ext h)
      simp [Bus.Source.form, hj, formAt, vsrc, hj']
  | count j' c =>
    by_cases hj : j' = j
    · subst hj
      simp only [Bus.Source.form, dite_true, Bus.countForm, formAt, vsrc, if_true, evaluate_eq,
        Form.col, gpow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero,
        one_mul, add_zero, List.prod_cons, List.prod_nil, mul_one]
      simp [evalRow, rowE]
    · have hj' : j'.val ≠ j.val := fun h ↦ hj (Fin.ext h)
      simp [Bus.Source.form, hj, formAt, vsrc, hj']

/-- A side's weighted program blocks. -/
theorem sidesV_getD (alphas : List E) (β : E) (point : List E) (k : Fin 3) :
    (sidesV tabs alphas β point).getD k [] =
      (stackBlocksV ((Bus.sources (inst L tabs hτ) k).map
        (vsrc L tabs hτ (eqKernel alphas) β))).map fun bo ↦ (bo.1, blockWeightV point bo.1.κ bo.2) := by
  rw [sidesV, sideBlocksV_eq L tabs hτ]
  fin_cases k <;> rfl

/-- The lvm instance's sources are its tables' flushes and count columns. -/
theorem not_boundary (k : Fin 3) (s : Bus.Source (inst L tabs hτ)) (hs : s ∈ Bus.sources _ k)
    (b : BoundaryBlock (inst L tabs hτ).toShape) : s ≠ .boundary b := by
  rintro rfl
  have hb : (inst L tabs hτ).boundary = [] := rfl
  fin_cases k <;>
    simp [Bus.sources, Bus.sideSources, Bus.countSources, hb] at hs

/-- A table block's public part vanishes: no padding row (`rows = 2^τ`). -/
theorem publicValue_zero (α : Fin 4 → E) (β : E) (vals : Vector E (inst L tabs hτ).busClaims)
    (s : Bus.Source (inst L tabs hτ)) (hs : ∀ b, s ≠ .boundary b) (z : Vector E s.κ) :
    s.publicValue α β vals z = 0 := by
  have hpw : ∀ (m : ℕ) (z : Vector E m), Bus.padWeight (2 ^ m) z = 0 := fun m z ↦ by
    rw [Bus.padWeight, evalMle_eq_sum]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    simp [not_le.mpr x.isLt]
  cases s with
  | boundary b => exact absurd rfl (hs b)
  | flush j f =>
    simp only [Bus.Source.publicValue, Bus.Source.padTerm]
    exact mul_eq_zero_of_right _ (hpw _ z)
  | count j c =>
    simp only [Bus.Source.publicValue, Bus.Source.padTerm]
    exact mul_eq_zero_of_right _ (hpw _ z)

/-- **The program's side totals are the protocol's.** -/
theorem totals_busResV (hsc : AllSc tabs) (b : LBus) (hp : b.point.length = (inst L tabs hτ).μBus)
    (k : Fin 3) :
    (busResV tabs b).totals.getD k 0 =
      (lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.totals k := by
  have hI := condOf L tabs hτ hsc
  have hl : (busResV tabs b).totals.getD k 0 = b.values.getD k 0 + 1 +
      sumE (((sidesV tabs b.alphas b.beta b.point).getD k []).map (·.2)) := by
    simp only [busResV, busFinalV]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  rw [hl, sidesV_getD L tabs hτ, sumE_eq_sum]
  have hs := sum_stack hI k (vsrc L tabs hτ (eqKernel b.alphas) b.beta)
    (vsrc_κ L tabs hτ _ _) b.point hp (fun _ ↦ 1)
  simp only [mul_one] at hs
  rw [hs]
  show _ = Bus.total _ k _ _ _ _ _
  rw [Bus.total]
  have h0 : ∀ x : Fin (Bus.blocks (inst L tabs hτ) k).n, ∀ z, (Bus.src (inst L tabs hτ) k x).publicValue (toAlpha b.alphas)
      b.beta (vals0 L tabs hτ) z = 0 := fun x z ↦
    publicValue_zero L tabs hτ _ _ _ _ (not_boundary L tabs hτ k _
      (List.mem_mergeSort.mp (List.getElem_mem _))) z
  simp only [h0, mul_zero, Finset.sum_const_zero, zero_add, CharTwo.sub_eq_add, layerStmtOf,
    valuesFn]
  ring

/-- **The program's forms are the protocol's**: the form of side `k` on table `j`, evaluated at
values `e` of the table's columns. -/
theorem formAt_busResV (hsc : AllSc tabs) (hkey : KeysOk tabs) (b : LBus)
    (ha : b.alphas.length = 4) (hp : b.point.length = (inst L tabs hτ).μBus) (k : Fin 3)
    (j : (inst L tabs hτ).SumcheckTables) (e : Fin ((inst L tabs hτ).width j.1) → E) :
    formAt ((lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.forms k j) e =
      (((busResV tabs b).forms.getD j.1.val []).getD k.val {}).evaluate (rowE e) := by
  have hI := condOf L tabs hτ hsc
  have hr : ((busResV tabs b).forms.getD j.1.val []).getD k.val {} =
      ⟨bucketV ((sidesV tabs b.alphas b.beta b.point).getD k []) j.1.val⟩ := by
    have hj : (busResV tabs b).forms.getD j.1.val [] =
        (sidesV tabs b.alphas b.beta b.point).map fun s ↦ (⟨bucketV s j.1.val⟩ : Form) := by
      simp only [busResV, busFinalV]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
    rw [hj, show ({} : Form) = ⟨bucketV [] j.1.val⟩ from rfl, List.getD_map]
  rw [hr, evaluate_bucketV, sidesV_getD L tabs hτ]
  have hs := sum_stack hI k (vsrc L tabs hτ (eqKernel b.alphas) b.beta)
    (vsrc_κ L tabs hτ _ _) b.point hp
    (fun vb ↦ if vb.tab = j.1.val then vb.form.evaluate (rowE e) else 0)
  rw [List.map_map] at hs ⊢
  rw [hs]
  show formAt (Bus.forms hI k _ _ _ j) e = _
  rw [formAt_forms]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [layerStmtOf]
  rw [formAt_src L tabs hτ hkey ha]

end Result

end Lvm.M3
end
-- ===== end of `LvmM3FidBus` =====

-- ===== merged from `LvmM3FidTab` (GOLF module merge: `LvmM3FidTab.lean` is now a stub importing `LvmM3Mid`) =====
section
-- adapted from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/TableFidLeanIsa.lean`,
-- `.../Front/TableFidLeanIsaBus.lean` (`foldl_max_le`, `le_foldl_max_of_mem`) and
-- `.../Complete/TableMath.lean` (`weightFactor`, `getD_tableWeights`) (formal rev 40f877dc):
-- `powersFrom_eq`, `eq_factor`, `flatten_getD`, `refTableTerms_snd`, `ofFn_vecOf`, `prodWeight_eq`,
-- `tableValues_eq`, `rounds/target/formula/claims` for any number of tables (leanVM's are at six
-- leanISA tables), `sampleN_bind_congr`, `abGuard`, `abProg_bind_guard`, `abSpec4`; new for lvm
-- (WP-9b): `tableFidL` (the table phase's identities at the lvm instance) and `lbusTableSpec`
-- (the bus phase and the table sumcheck with no fidelity hypothesis).

/-!
# The table phase's identities at the lvm instance

For the lvm instance `I = inst L tabs hτ` with every table a sumcheck table (`AllSc`), every
message of at most thirteen value limbs (`KeysOk`) and every table of positive width, at every
read of the bus phase with four fingerprint challenges, the GKR point on `μ_bus` coordinates and
three values:

* `tableFidL`: the table phase's identities (`TableFidG`) for the program objects of `LvmM3Fid`
  (`vTables`, `vLayout`, `busResV`, `colOfL`): the rounds are `τ_max` (`rounds_lvm`), the target is
  the protocol's batched claim (`target_lvm`, from `totals_busResV`), the final check's value is
  the protocol's formula (`formula_lvm`: weights `prodWeight_eq`, values `tableValues_eq`,
  constraints `eval₂_toMv`, forms `formAt_busResV`), every protocol claim is the program's
  (`claims_lvm`);
* `lbusTableSpec`: the lvm bus phase then the table sumcheck, with no fidelity hypothesis left
  (`lvmBusSpec4`: the bus phase with the four challenges recorded, from `abSpec4`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Compile LeanVM.Protocol.TableSumcheck CompPoly CMlPolynomialEval
open Finset
open scoped NNReal ENNReal

/-! ## Generic facts (leanVM) -/

/-- `powers_from(acc, base, n)` is `acc · base^i` for `i < n`. -/
theorem powersFrom_eq (base : E) : ∀ (n : ℕ) (acc : E),
    powersFrom acc base n = (List.range n).map fun i ↦ acc * base ^ i
  | 0, _ => rfl
  | n + 1, acc => by
    rw [powersFrom, powersFrom_eq base n, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [pow_zero, mul_one, Function.comp_def, pow_succ']
    exact congrArg (_ :: ·) (List.map_congr_left fun i _ ↦ by ring)

theorem powers_eq (ξ : E) (n : ℕ) : powers ξ n = (List.range n).map (ξ ^ ·) := by
  rw [powers, powersFrom_eq]; simp

/-- A fold of `max` is below a bound above the start and every entry. -/
theorem foldl_max_le {b : ℕ} : ∀ (l : List ℕ) (i0 : ℕ), i0 ≤ b → (∀ x ∈ l, x ≤ b) →
    l.foldl max i0 ≤ b
  | [], _, h, _ => h
  | x :: l, i0, h, hl =>
    foldl_max_le l _ (max_le h (hl x (by simp))) fun y hy ↦ hl y (by simp [hy])

/-- An entry is below the fold of `max`. -/
theorem le_foldl_max_of_mem {x : ℕ} : ∀ {l : List ℕ} {i0 : ℕ}, x ∈ l → x ≤ l.foldl max i0
  | y :: l, i0, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact (le_max_right _ _).trans (le_foldl_max_init l _)
    · exact le_foldl_max_of_mem h
where
  le_foldl_max_init : ∀ (l : List ℕ) (i0 : ℕ), i0 ≤ l.foldl max i0
    | [], _ => le_rfl
    | y :: l, i0 => (le_max_left i0 y).trans (le_foldl_max_init l _)

/-- The equality factor in characteristic two. -/
theorem eq_factor (a b : E) : (1 - a) * (1 - b) + a * b = 1 + b + a := by
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  linear_combination (a * b) * Whir.Complete.two_eq_zero_E

/-- The factor of coordinate `v` in the weight of a table of log-height `h`. -/
def weightFactor (e : List E) (h v : ℕ) (c : E) : E :=
  if v < h then 1 + e.getD v 0 + c else c

private theorem foldl_weights (heights : List ℕ) (e : List E) :
    ∀ (r : List E) (k : ℕ) (W : List E), W.length = heights.length →
      (r.zipIdx k).foldl (fun weights (challenge, coord) ↦
        List.zipWith (fun weight height ↦ weight *
          if coord < height then 1 + e.getD coord 0 + challenge else challenge) weights heights)
        W = List.zipWith (fun w height ↦ w * ∏ i ∈ range r.length,
          weightFactor e height (k + i) (r.getD i 0)) W heights
  | [], k, W, hW => by
    simp only [List.zipIdx_nil, List.foldl_nil, List.length_nil, prod_range_zero, mul_one]
    apply List.ext_getElem (by simp [hW])
    intro i h1 h2
    simp
  | c :: r, k, W, hW => by
    rw [List.zipIdx_cons, List.foldl_cons,
      foldl_weights heights e r (k + 1) _ (by simp [hW])]
    apply List.ext_getElem (by simp [hW])
    intro i h1 h2
    simp only [List.getElem_zipWith, List.length_cons]
    rw [prod_range_succ', mul_assoc]
    refine congrArg (W[i]'(by simp_all) * ·) ?_
    rw [mul_comm]
    refine congrArg₂ (· * ·) (prod_congr rfl fun j _ ↦ ?_) ?_
    · rw [show k + (j + 1) = k + 1 + j by ring]
      rfl
    · simp [weightFactor]

/-- The verifier's weights, one per table. -/
theorem length_tableWeights (heights : List ℕ) (e r : List E) :
    (tableWeights heights e r).length = heights.length := by
  rw [Verifier.tableWeights, foldl_weights heights e r 0 _ (by simp)]
  simp

/-- **The verifier's table weight** of a table of log-height `h` at `r`:
`Π_{v < h} (1 + e_v + r_v) · Π_{h ≤ v} r_v`. -/
theorem getD_tableWeights (heights : List ℕ) (e r : List E) (t : ℕ) (ht : t < heights.length) :
    (tableWeights heights e r).getD t 0 =
      ∏ v ∈ range r.length, weightFactor e (heights.getD t 0) v (r.getD v 0) := by
  rw [Verifier.tableWeights, foldl_weights heights e r 0 _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_zipWith,
    List.getD_eq_getElem _ _ ht]
  simp

/-- Entry `i` of list `t` of a list of lists, inside the concatenation. -/
theorem flatten_getD : ∀ (l : List (List E)) (t i : ℕ), t < l.length → i < (l.getD t []).length →
    l.flatten.getD ((∑ u ∈ range t, (l.getD u []).length) + i) 0 = (l.getD t []).getD i 0
  | [], _, _, h, _ => by simp at h
  | a :: l, 0, i, _, hi => by
    simp only [List.getD_cons_zero] at hi ⊢
    rw [Finset.sum_range_zero, zero_add, List.flatten_cons, List.getD_append _ _ _ _ hi]
  | a :: l, t + 1, i, ht, hi => by
    simp only [List.getD_cons_succ, List.length_cons] at hi ht ⊢
    rw [Finset.sum_range_succ', List.getD_cons_zero, List.flatten_cons]
    simp only [List.getD_cons_succ]
    rw [add_comm _ a.length, add_assoc, List.getD_append_right _ _ _ _ (by (clear * -; omega)),
      Nat.add_sub_cancel_left]
    exact flatten_getD l t i (by (clear * - ht; omega)) hi

/-- The claims the final loop returns: the given ones, then every table's values, each on its
column at the point's first `height` coordinates. -/
theorem refTableTerms_snd (tables : List Table) (cps fps pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (evs : List (List E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim),
      (refTableTerms tables cps fps pt rows evs cursor final claims).2 = claims ++
        (List.zip rows evs).flatMap fun p ↦ p.2.zipIdx.map fun (value, column) ↦
          (⟨(globalColumnBases tables).getD p.1.1.opcode 0 + column, pt.take p.1.2.1, value⟩ :
            Verifier.ColumnClaim)
  | [], _, _, _, claims => by simp [refTableTerms]
  | _ :: _, [], _, _, claims => by simp [refTableTerms]
  | (table, height, forms, weight) :: rest, ev :: evs, cursor, final, claims => by
    rw [refTableTerms, refTableTerms_snd tables cps fps pt rest evs]
    simp

/-- The final value of the loop: the given one plus every table's weighted terms, the constraint
powers taken from the cursor on. -/
theorem refTableTerms_fst (tables : List Table) (cps fps pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (evs : List (List E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim), rows.length = evs.length →
      (refTableTerms tables cps fps pt rows evs cursor final claims).1 = final +
        ∑ i ∈ range rows.length, ((rows.getD i default).2.2.2 *
          (dot ((cps.drop (cursor + ∑ i' ∈ range i, (rows.getD i' default).1.nConstraints)).take
              (rows.getD i default).1.nConstraints)
            ((rows.getD i default).1.constraints (evs.getD i [])) +
          dot fps ((rows.getD i default).2.2.1.map (·.evaluate ((evs.getD i []).getD · 0)))))
  | [], _, _, _, _, _ => by simp [refTableTerms]
  | _ :: _, [], _, _, _, h => by simp at h
  | (table, height, forms, weight) :: rest, ev :: evs, cursor, final, claims, h => by
    have h' : rest.length = evs.length := by simpa using h
    have e := refTableTerms_fst tables cps fps pt rest evs (cursor + table.nConstraints)
      (final + weight * (dot ((cps.drop cursor).take table.nConstraints) (table.constraints ev) +
        dot fps (forms.map (·.evaluate (ev.getD · 0))))) (claims ++ ev.zipIdx.map
          fun (value, column) ↦ ⟨(globalColumnBases tables).getD table.opcode 0 + column,
            pt.take height, value⟩) h'
    refine e.trans ?_
    rw [List.length_cons, Finset.sum_range_succ' _ rest.length, add_assoc, add_comm (weight * _)]
    refine congrArg (final + ·) (congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_) ?_)
    · have hs : ∑ i' ∈ range (i + 1),
          (((table, height, forms, weight) :: rest).getD i' default).1.nConstraints =
          ∑ i' ∈ range i, (rest.getD i' default).1.nConstraints + table.nConstraints := by
        rw [Finset.sum_range_succ']; rfl
      rw [List.getD_cons_succ, List.getD_cons_succ, hs, add_assoc cursor, add_comm table.nConstraints]
    · simp only [List.getD_cons_zero, Finset.sum_range_zero, add_zero]

/-- The low coordinates of a list read as a vector. -/
theorem ofFn_vecOf (p : List E) {μ m : ℕ} (hm : m ≤ μ) (hp : p.length = μ) :
    (List.ofFn fun j : Fin m ↦ (vecOf μ p)[j.val]'(by omega)) = p.take m := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_ofFn, vecOf, Vector.getElem_ofFn, List.getElem_take]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

/-- A sum over a list's positions, as a sum over the indices. -/
theorem sum_fin_length {α : Type} (l : List α) (c : ℕ) (ξ : E) (g : α → E) :
    ∑ i : Fin l.length, ξ ^ (c + i.val) * g l[i] =
      ∑ k ∈ range l.length, ξ ^ (c + k) * (l.map g).getD k 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]
  rfl

/-- A sum over a list's entries, as a sum over its positions. -/
theorem sum_map_get {α M : Type} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ j : Fin l.length, f (l.get j) = (l.map f).sum := by
  have h : (List.finRange l.length).map (fun j ↦ f (l.get j)) =
      ((List.finRange l.length).map l.get).map f := by rw [List.map_map]; rfl
  rw [Fin.sum_univ_def, h, List.map_get_finRange]

/-- The constraint powers from `c` on, `m` of them, against `m` values. -/
theorem dot_cps (ξ : E) (n c m : ℕ) (l : List E) (hl : l.length = m) (hcm : c + m ≤ n) :
    dot ((((powers ξ (n + 3)).take n).drop c).take m) l =
      ∑ i ∈ range m, ξ ^ (c + i) * l.getD i 0 := by
  have hlen : ((((powers ξ (n + 3)).take n).drop c).take m).length = m := by
    simp [powers_eq]; omega
  rw [Whir.Complete.dot_eq_sum _ _ (by rw [hlen, hl]), hlen]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi')]
  simp [powers_eq]

/-- The form powers: `ξ^n, ξ^(n+1), ξ^(n+2)`. -/
theorem fps_eq (ξ : E) (n : ℕ) : (powers ξ (n + 3)).drop n = (List.range 3).map fun s ↦ ξ ^ (n + s) := by
  rw [powers_eq, List.range_add, List.map_append, List.drop_append_of_le_length (by simp),
    List.drop_eq_nil_of_le (by simp), List.nil_append, List.map_map]
  rfl

/-! ## The lvm instance -/

section Lvm

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)

/-- The lvm tables are the instance's sumcheck tables, in order. -/
def stEq : Fin tabs.length ≃ (inst L tabs hτ).SumcheckTables where
  toFun j := ⟨j, sumcheckTable_of L tabs hτ hsc j⟩
  invFun t := t.1
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem stEq_val (j : Fin tabs.length) : (stEq L tabs hτ hsc j).1 = j := rfl

include hsc in
/-- **The rounds**: `τ_max` is the largest log-height. -/
theorem rounds_lvm : (vLayout tabs).tableLogHeights.foldl max 0 = (inst L tabs hτ).τmax := by
  apply le_antisymm
  · refine foldl_max_le _ _ (Nat.zero_le _) fun x hx ↦ ?_
    simp only [vLayout, List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := List.get_of_mem ht
    exact (inst L tabs hτ).τ_le_τmax (stEq L tabs hτ hsc j)
  · refine Finset.sup_le fun j _ ↦ ?_
    exact le_foldl_max_of_mem (List.mem_map_of_mem (f := Tab.τ) (List.get_mem _ _))

theorem vTables_getD (j : ℕ) (hj : j < tabs.length) : (vTables tabs).getD j default = vTable j tabs[j] := by
  rw [List.getD_eq_getElem _ _ (by rw [length_vTables]; exact hj)]
  simp [vTables, List.getElem_zipIdx]

theorem nConstraints_vTable (j : ℕ) (t : Tab) : (vTable j t).nConstraints = t.cons.length := by
  simp [Table.nConstraints, vTable]

theorem width_vTable (j : ℕ) (t : Tab) : (vTable j t).width = t.w := by
  simp [Table.width, vTable]

include hsc in
/-- **The number of constraints** is the program's. -/
theorem nCons_eq : nCons (vTables tabs) = (inst L tabs hτ).B := by
  unfold M3Instance.B nCons
  rw [← (stEq L tabs hτ hsc).sum_comp]
  simp only [stEq_val]
  change _ = ∑ j : Fin tabs.length, ((tabs.get j).cons.map (CPoly.toMv _)).length
  simp only [List.length_map]
  rw [sum_map_get tabs fun t ↦ t.cons.length, vTables, zipIdx_eq_finRange, List.map_map,
    List.map_map, ← Fin.sum_univ_def, ← sum_map_get]
  exact Finset.sum_congr rfl fun j _ ↦ by simp [nConstraints_vTable]

/-- Kept sizes of the sumcheck tables before `j`: every table is one. -/
theorem prefix_onSumcheck (f : Fin (inst L tabs hτ).ntab → ℕ) (g : ℕ → ℕ)
    (hfg : ∀ j, f j = g j.val) (j : Fin tabs.length) :
    ∑ j' : Fin (stEq L tabs hτ hsc j).1.val,
        onSumcheck (inst L tabs hτ) f (Fin.castLE (stEq L tabs hτ hsc j).1.isLt.le j') =
      ∑ u ∈ range j, g u := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j' _ ↦ ?_
  simp only [onSumcheck, if_pos (sumcheckTable_of L tabs hτ hsc _), hfg]
  rfl

variable {L tabs hτ} in
/-- The rows of the final loop, entry by entry. -/
theorem rowsOf_getD (bus : BusResult) (pt : List E) (hf : bus.forms.length = tabs.length)
    (j : ℕ) (hj : j < tabs.length) :
    (rowsOf (vTables tabs) (vLayout tabs) bus pt).getD j default =
      (vTable j tabs[j], tabs[j].τ, bus.forms.getD j [],
        (Verifier.tableWeights (tabs.map (·.τ)) bus.point pt).getD j 0) := by
  have hw := length_tableWeights (tabs.map (·.τ)) bus.point pt
  rw [List.length_map] at hw
  rw [List.getD_eq_getElem _ _ (by simp [rowsOf, vLayout, length_vTables, hf, hw, hj])]
  simp only [rowsOf, vLayout, List.getElem_zip, List.getElem_map]
  rw [← vTables_getD tabs j hj, List.getD_eq_getElem _ _ (by rw [length_vTables]; exact hj),
    List.getD_eq_getElem _ _ (by rw [hf]; exact hj), List.getD_eq_getElem _ _ (by rw [hw]; exact hj)]

theorem length_rowsOf (bus : BusResult) (pt : List E) (hf : bus.forms.length = tabs.length) :
    (rowsOf (vTables tabs) (vLayout tabs) bus pt).length = tabs.length := by
  have hw := length_tableWeights (tabs.map (·.τ)) bus.point pt
  simp [rowsOf, vLayout, length_vTables, hf, hw]

theorem length_forms (b : LBus) : (busResV tabs b).forms.length = tabs.length := by
  simp [busResV, busFinalV]

theorem length_forms_getD (b : LBus) (j : ℕ) (hj : j < tabs.length) :
    ((busResV tabs b).forms.getD j []).length = 3 := by
  simp only [busResV, busFinalV]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
    List.length_map]
  simp [sidesV, sideBlocksV]

/-- What a read of the right shape is: one list per table, of the table's width. -/
theorem readShape_facts (bus : BusResult) (pt : List E) (hf : bus.forms.length = tabs.length)
    (evs : List (List E)) (hs : ReadShape (rowsOf (vTables tabs) (vLayout tabs) bus pt) evs) :
    evs.length = tabs.length ∧ ∀ j (hj : j < tabs.length), (evs.getD j []).length = tabs[j].w := by
  have hl := hs.length_eq
  rw [length_rowsOf tabs bus pt hf] at hl
  refine ⟨hl.symm, fun j hj ↦ ?_⟩
  obtain ⟨-, h⟩ := List.forall₂_iff_get.mp hs
  have := h j (by rw [length_rowsOf tabs bus pt hf]; exact hj) (by rw [← hl]; exact hj)
  rw [List.getD_eq_getElem _ _ (by rw [← hl]; exact hj)]
  have hr := rowsOf_getD bus pt hf j hj
  rw [List.getD_eq_getElem _ _ (by rw [length_rowsOf tabs bus pt hf]; exact hj)] at hr
  simp only [List.get_eq_getElem] at this
  rw [this, hr, width_vTable]

/-- **The values read are the protocol's**: column `i` of table `j` among the values of all the
columns is entry `i` of table `j`'s read. -/
theorem tableValues_eq (evs : List (List E)) (hlen : evs.length = tabs.length)
    (hw : ∀ j (hj : j < tabs.length), (evs.getD j []).length = tabs[j].w) (j : Fin tabs.length)
    (i : Fin ((inst L tabs hτ).width (stEq L tabs hτ hsc j).1)) :
    tableValues (inst L tabs hτ) (vecOf _ evs.flatten) (stEq L tabs hτ hsc j) i =
      (evs.getD j []).getD i 0 := by
  unfold tableValues
  simp only [vecOf, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [show (((columnPos (inst L tabs hτ)) ⟨stEq L tabs hτ hsc j, i⟩ : Fin _) : ℕ) = _
    from position_val _ _ _, prefix_onSumcheck L tabs hτ hsc _ (fun u ↦ (evs.getD u []).length)
      (fun j' ↦ by rw [hw j' j'.isLt]; rfl)]
  exact flatten_getD evs j i (by rw [hlen]; exact j.isLt)
    (by rw [hw j j.isLt]; exact i.isLt)

end Lvm

/-! ## The identities -/

theorem getD_map_evaluate (l : List Form) (k : ℕ) (col : ℕ → E) :
    (l.map (·.evaluate col)).getD k 0 = (l.getD k {}).evaluate col := by
  by_cases hk : k < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getD_eq_getElem _ _ hk]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [evaluate_eq]

section Fid

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)

/-- Table `u`'s constraint count (`0` past the tables). -/
def consLen (tabs : List Tab) (u : ℕ) : ℕ := (tabs[u]?.map fun t ↦ t.cons.length).getD 0

theorem consLen_eq (u : ℕ) (hu : u < tabs.length) : consLen tabs u = tabs[u].cons.length := by
  simp [consLen, List.getElem?_eq_getElem hu]

theorem nCons_eq_sum : nCons (vTables tabs) = ∑ u ∈ range tabs.length, consLen tabs u := by
  unfold nCons
  rw [vTables, zipIdx_eq_finRange, List.map_map, List.map_map, ← Fin.sum_univ_def,
    ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ ↦ by
    simp [nConstraints_vTable, consLen_eq tabs j j.isLt]

/-- The protocol's statement after the lvm bus phase. -/
noncomputable abbrev sOf (b : LBus) : (inst L tabs hτ).Stmt × BusOut (inst L tabs hτ) :=
  lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)

/-- **The weights**: the protocol's weight of table `j` at the reversed challenges is the
verifier's. -/
theorem prodWeight_eq (b : LBus) (ch : List E) (hch : ch.length = (inst L tabs hτ).τmax)
    (j : Fin tabs.length) :
    prodWeight (TableSumcheck.tableWeights (inst L tabs hτ) (sOf L tabs hτ hsc b).2.point
        (stEq L tabs hτ hsc j)) (vecOf _ ch).reverse =
      (Verifier.tableWeights (tabs.map (·.τ)) b.point ch.reverse).getD j 0 := by
  rw [getD_tableWeights _ _ _ _ (by simp), List.length_reverse, hch, prodWeight,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  have hz : ((vecOf (inst L tabs hτ).τmax ch).reverse)[a.val] = ch.reverse.getD a 0 := by
    rw [Vector.getElem_reverse, List.getD_eq_getElem _ _ (by simp [hch]), List.getElem_reverse]
    simp only [vecOf, Vector.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ (by (clear * - hτ hch; omega))]
    congr 1
    (clear * - hτ hch; omega)
  have hζ : ((sOf L tabs hτ hsc b).2.point)[a.val] = b.point.getD a 0 := by
    simp [sOf, lbusStmt, Bus.busOut, Bus.point, Gkr.lowPoint, layerStmtOf, vecOf]
  have hτj : (tabs.map (·.τ)).getD j 0 = (inst L tabs hτ).τ (stEq L tabs hτ hsc j).1 := by
    simp [List.getD_eq_getElem?_getD]
  rw [Fin.getElem_fin, hz, hτj]
  simp only [TableSumcheck.tableWeights, weightFactor]
  split_ifs with h
  · simp only [Fin.getElem_fin, hζ]
    exact eq_factor _ _
  · simp

include hsc in
/-- **The target**: the form powers against the program's totals are the protocol's batched
claim. -/
theorem target_lvm (b : LBus) (hp : b.point.length = (inst L tabs hτ).μBus) (ξ : E) :
    dot (fpsOf (vTables tabs) ξ) (busResV tabs b).totals =
      powerBatch (claimed (inst L tabs hτ) (sOf L tabs hτ hsc b)) ξ := by
  have h3 : (busResV tabs b).totals.length = 3 := by simp [busResV, busFinalV]
  rw [powerBatch, claimed, Fin.sum_univ_add]
  simp only [Fin.append_left, zero_mul, Finset.sum_const_zero, zero_add, Fin.append_right,
    Fin.val_natAdd]
  rw [fpsOf, nCons_eq L tabs hτ hsc, fps_eq, Whir.Complete.dot_eq_sum _ _ (by rw [h3]; simp),
    List.length_map, List.length_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, mul_comm,
    totals_busResV L tabs hτ hsc b hp i]

/-- The values read as the table's row: below the width the protocol's values, zero above. -/
theorem rowE_tableValues (evs : List (List E)) (hlen : evs.length = tabs.length)
    (hw : ∀ j (hj : j < tabs.length), (evs.getD j []).length = tabs[j].w) (j : Fin tabs.length) :
    rowE (tableValues (inst L tabs hτ) (vecOf _ evs.flatten) (stEq L tabs hτ hsc j)) =
      fun i ↦ (evs.getD j []).getD i 0 := by
  funext i
  unfold rowE
  split_ifs with hi
  · exact tableValues_eq L tabs hτ hsc evs hlen hw j ⟨i, hi⟩
  · exact (List.getD_eq_default _ _ (by rw [hw j j.isLt]; exact not_lt.mp hi)).symm

/-- **The final check's value is the protocol's formula**. -/
theorem formula_lvm (hkey : KeysOk tabs) (b : LBus) (ha : b.alphas.length = 4)
    (hp : b.point.length = (inst L tabs hτ).μBus) (ξ : E) (ch : List E) (evs : List (List E))
    (hch : ch.length = (inst L tabs hτ).τmax)
    (hs : ReadShape (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse) evs) :
    (refTableTerms (vTables tabs) (cpsOf (vTables tabs) ξ) (fpsOf (vTables tabs) ξ) ch.reverse
        (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse) evs 0 0 []).1 =
      TableSumcheck.formula (inst L tabs hτ) (sOf L tabs hτ hsc b, ξ)
        (vecOf (inst L tabs hτ).τmax ch).reverse
        (vecOf (inst L tabs hτ).tableColumns evs.flatten) := by
  have hf := length_forms tabs b
  obtain ⟨hlen, hw⟩ := readShape_facts tabs _ ch.reverse hf evs hs
  rw [refTableTerms_fst _ _ _ _ _ _ _ _ _ (by rw [length_rowsOf tabs _ _ hf, hlen]), zero_add,
    length_rowsOf tabs _ _ hf]
  unfold TableSumcheck.formula
  rw [← (stEq L tabs hτ hsc).sum_comp, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcur : ∑ i' ∈ range j.val,
      ((rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse).getD i' default).1.nConstraints =
      ∑ u ∈ range j.val, consLen tabs u :=
    Finset.sum_congr rfl fun u hu ↦ by
      have hu' : u < tabs.length := (Finset.mem_range.mp hu).trans j.isLt
      rw [rowsOf_getD _ _ hf u hu', nConstraints_vTable, consLen_eq tabs u hu']
  rw [hcur, rowsOf_getD _ _ hf j j.isLt, zero_add]
  simp only
  rw [show (busResV tabs b).point = b.point from rfl, ← prodWeight_eq L tabs hτ hsc b ch hch j]
  refine congrArg (_ * ·) ?_
  have hcol := rowE_tableValues L tabs hτ hsc evs hlen hw j
  set e := tableValues (inst L tabs hτ) (vecOf _ evs.flatten) (stEq L tabs hτ hsc j)
  unfold rowValue
  dsimp only
  refine congrArg₂ (· + ·) ?_ ?_
  · -- the constraints
    have hpos : ∀ i, (constraintPos (inst L tabs hτ) ⟨stEq L tabs hτ hsc j, i⟩ : ℕ) =
        (∑ u ∈ range j.val, consLen tabs u) + i := fun i ↦ by
      rw [show ((constraintPos (inst L tabs hτ) ⟨stEq L tabs hτ hsc j, i⟩ : Fin _) : ℕ) = _
        from position_val _ _ _, prefix_onSumcheck L tabs hτ hsc _ (consLen tabs)
          (fun j' ↦ by rw [consLen_eq tabs j' j'.isLt]; simp)]
    have hR : ∑ i : Fin ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1).length,
        ξ ^ (constraintPos (inst L tabs hτ) ⟨stEq L tabs hτ hsc j, i⟩ : ℕ) *
          evalRow ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1)[i] e =
        ∑ i : Fin ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1).length,
          ξ ^ ((∑ u ∈ range j.val, consLen tabs u) + i.val) *
            evalRow ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1)[i] e :=
      Finset.sum_congr rfl fun i _ ↦ by rw [hpos i]
    have hm : ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1).length =
        tabs[j.val].cons.length := by
      show ((tabs.get j).cons.map _).length = _
      simp
    have hcm : (∑ u ∈ range j.val, consLen tabs u) + tabs[j.val].cons.length ≤
        nCons (vTables tabs) := by
      rw [nCons_eq_sum, ← consLen_eq tabs j j.isLt, ← Finset.sum_range_succ]
      exact Finset.sum_le_sum_of_subset fun x hx ↦
        Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le j.isLt)
    have hmap : ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1).map (evalRow · e) =
        (vTable j tabs[j.val]).constraints (evs.getD j []) := by
      show ((tabs.get j).cons.map _).map _ = (tabs[j.val].cons.map _)
      rw [List.map_map]
      refine List.map_congr_left fun P _ ↦ ?_
      simp only [Function.comp_apply, evalRow]
      rw [eval₂_toMv, hcol]
    rw [hR, sum_fin_length ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1) _ ξ
      (fun P ↦ evalRow P e), hm, hmap, cpsOf, nConstraints_vTable,
      dot_cps ξ _ _ _ _ (by simp [vTable]) hcm]
  · -- the forms
    have h3 := length_forms_getD tabs b j j.isLt
    rw [fpsOf, nCons_eq L tabs hτ hsc, fps_eq,
      Whir.Complete.dot_eq_sum _ _ (by rw [List.length_map, List.length_map, h3, List.length_range]),
      List.length_map, List.length_range, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
      getD_map_evaluate]
    refine congrArg (_ * ·) ?_
    rw [formAt_busResV L tabs hτ hsc hkey b ha hp k (stEq L tabs hτ hsc j) e, hcol]
    rfl

/-- A sumcheck table's point, listed: the point's first `τ` coordinates. -/
theorem toList_lowPoint (I : M3Instance) (r : Vector E I.τmax) (t : I.SumcheckTables) :
    (I.lowPoint r t).toList = r.toList.take (I.τ t.1) := by
  apply List.ext_getElem (by simp [I.τ_le_τmax t])
  intro i h1 h2
  rw [List.getElem_take, Vector.getElem_toList, Vector.getElem_toList]
  simp only [M3Instance.lowPoint, Vector.getElem_cast]
  rw [Vector.getElem_take]

/-- **The protocol's output claims are among the program's.** -/
theorem claims_lvm (b : LBus) (ξ : E) (ch : List E) (claim : E) (evs : List (List E))
    (hch : ch.length = (inst L tabs hτ).τmax)
    (hs : ReadShape (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse) evs) :
    ∀ c ∈ (tableOut (inst L tabs hτ) (tableStmtG (inst L tabs hτ) (sOf L tabs hτ hsc b) ξ ch claim)
      (vecOf (inst L tabs hτ).tableColumns evs.flatten)).2.columns.toList,
      (⟨colOfL L tabs hτ c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
        (busResV tabs b).claims ++ (refTableTerms (vTables tabs) (cpsOf (vTables tabs) ξ)
          (fpsOf (vTables tabs) ξ) ch.reverse
          (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse) evs 0 0 []).2 := by
  intro c hc
  have hf := length_forms tabs b
  obtain ⟨hlen, hw⟩ := readShape_facts tabs _ ch.reverse hf evs hs
  simp only [tableOut, tableStmtG, Vector.toList_append, List.mem_append] at hc
  rcases hc with hc | hc
  · exfalso
    have h0 : ((sOf L tabs hτ hsc b).2.columns.toList).length = 0 := by
      rw [Vector.length_toList]; exact busClaims_zero L tabs hτ
    rw [List.eq_nil_of_length_eq_zero h0] at hc
    exact List.not_mem_nil hc
  simp only [finalClaims, Vector.toList_ofFn, List.mem_ofFn] at hc
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨⟨t, i⟩, hk⟩ : ∃ p, (columnPos (inst L tabs hτ)).symm k = p := ⟨_, rfl⟩
  obtain ⟨j, rfl⟩ := (stEq L tabs hτ hsc).surjective t
  have hk' : k = columnPos (inst L tabs hτ) ⟨stEq L tabs hτ hsc j, i⟩ := by
    rw [← hk, Equiv.apply_symm_apply]
  subst hk'
  have hv : (vecOf (inst L tabs hτ).tableColumns evs.flatten)[columnPos (inst L tabs hτ)
      ⟨stEq L tabs hτ hsc j, i⟩] = (evs.getD j []).getD i 0 :=
    tableValues_eq L tabs hτ hsc evs hlen hw j i
  simp only [finalClaim, Equiv.symm_apply_apply, hv]
  refine List.mem_append_right _ ?_
  rw [refTableTerms_snd, List.nil_append, List.mem_flatMap]
  have hjr : j.val < (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse).length := by
    rw [length_rowsOf tabs _ _ hf]; exact j.isLt
  have hje : j.val < evs.length := by rw [hlen]; exact j.isLt
  refine ⟨((rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse).getD j default,
    evs.getD j []), ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hjr, List.getD_eq_getElem _ _ hje]
    have hz : j.val < (List.zip (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b)
        ch.reverse) evs).length := by rw [List.length_zip]; (clear * - hτ hlen hjr; omega)
    exact List.mem_iff_getElem.mpr ⟨j.val, hz, List.getElem_zip⟩
  · have hi : i.val < (evs.getD j []).length := by rw [hw j j.isLt]; exact i.isLt
    refine List.mem_map.mpr ⟨((evs.getD j []).getD i 0, i), ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hi]
      have := List.getElem_zipIdx (l := evs.getD j []) (j := 0) (i := i.val) (by simpa using hi)
      rw [zero_add] at this
      exact this ▸ List.getElem_mem _
    · rw [rowsOf_getD _ _ hf j j.isLt]
      simp only [colOfL, vTable, stEq_val]
      rw [toList_lowPoint, Vector.toList_reverse, toList_vecOf ch hch]
      have hsnd : (((columnPos (inst L tabs hτ)).symm (columnPos (inst L tabs hτ)
          ⟨stEq L tabs hτ hsc j, i⟩)).2 : ℕ) = i := by rw [hk]
      have hfst : ((columnPos (inst L tabs hτ)).symm (columnPos (inst L tabs hτ)
          ⟨stEq L tabs hτ hsc j, i⟩)).1 = stEq L tabs hτ hsc j := by rw [hk]
      rw [hsnd, hfst]
      rfl

/-- **The table phase's identities at the lvm instance** (leanVM `TableFid`, discharged). -/
theorem tableFidL (hkey : KeysOk tabs) (b : LBus) (ha : b.alphas.length = 4)
    (hp : b.point.length = (inst L tabs hτ).μBus) :
    TableFidG (vTables tabs) (inst L tabs hτ) (vLayout tabs) (colOfL L tabs hτ)
      (sOf L tabs hτ hsc b) (busResV tabs b) where
  rounds := rounds_lvm L tabs hτ hsc
  target := target_lvm L tabs hτ hsc b hp
  formula ξ ch evs hch hs := formula_lvm L tabs hτ hsc hkey b ha hp ξ ch evs hch hs
  claims ξ ch claim evs hch hs := claims_lvm L tabs hτ hsc b ξ ch claim evs hch hs


end Fid

/-! ## The fingerprint challenges are four (leanVM `TableFidLeanIsa`) -/

section Spec4

variable {εmax : ℝ≥0∞}

/-- `n` challenges are a list of `n`: continuations that agree on such lists give one program. -/
theorem sampleN_bind_congr {β : Type} : ∀ (n : ℕ) (k k' : List E → VerifierProgram β),
    (∀ as, as.length = n → k as = k' as) →
      (VerifierProgram.sampleChallenges n).bind k = (VerifierProgram.sampleChallenges n).bind k'
  | 0, k, k', h => h [] rfl
  | n + 1, k, k', h => by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq,
        VerifierProgram.bind_assoc]
    exact congrArg (VerifierProgram.sampleChallenge.bind ·) (funext fun x ↦
      sampleN_bind_congr n _ _ fun as has ↦ h (x :: as) (by simp [has]))

/-- The guard that the fingerprint challenges are four. -/
def abGuard (ab : List E × E) : VerifierProgram (List E × E) :=
  if ab.1.length = 4 then VerifierProgram.ret ab else VerifierProgram.fail

/-- The wire's fingerprint challenges are four: guarding it changes nothing. -/
theorem abProg_bind_guard : abProg.bind abGuard = abProg := by
  unfold abProg
  rw [VerifierProgram.bind_assoc]
  refine sampleN_bind_congr 4 _ _ fun as has ↦ ?_
  rw [VerifierProgram.bind_assoc]
  refine congrArg (VerifierProgram.sampleChallenge.bind ·) (funext fun b ↦ ?_)
  simp [abGuard, has]

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt)

/-- **The fingerprint challenges, four of them**: `abSpec` with the length of the challenges
recorded. -/
noncomputable def abSpec4 {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hlt : abError I L₀ < 1) :
    Spec abProg (HDoom cands (Seam.commit I) input)
      (fun ab h ↦ ab.1.length = 4 ∧
        HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h) εmax
      (abError I L₀ + 0) 0 :=
  let P4 : List E × E → List Ev → Prop := fun ab h ↦ ab.1.length = 4 ∧
    HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h
  let G : ∀ ab : List E × E, Spec (abGuard ab)
      (fun h ↦ HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h) P4 εmax 0 0 :=
    fun ab ↦ if h : ab.1.length = 4 then
      Spec.congr (p := VerifierProgram.ret ab) (by simp [abGuard, h])
        ((Spec.ret (Post := P4) ab).mono (fun _ hp ↦ ⟨h, hp⟩) (fun _ _ hq ↦ hq) le_rfl le_rfl
          le_rfl)
    else Spec.congr (p := VerifierProgram.fail) (by simp [abGuard, h]) Spec.fail
  Spec.congr abProg_bind_guard ((abSpec I cands input hI hfin hcard hlt (T := 0)).bind' G)

/-- **The lvm bus phase with its four challenges recorded** (`lvmBusSpec` from `abSpec4`). -/
noncomputable def lvmBusSpec4 (vals : Vector E I.busClaims) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {Lk : ℝ≥0∞} (hLk : Lk ≤ εmax) :
    Spec (lvmBusProg I.μBus) (HDoom cands (Seam.commit I) input)
      (fun b h ↦ b.alphas.length = 4 ∧ LBusAt I hI cands input vals b h) εmax
      (abError I L₀ + 0) Lk :=
  (abSpec4 I hI cands input hfin hcard hab).bind' fun ab ↦
    if h4 : ab.1.length = 4 then
      ((gkrSpec I cands (input, (toAlpha ab.1, ab.2)) hI hfin hcard hμ he hT hlam).mono
        (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun r ↦
        let P : List Ev → Prop := fun h ↦ r.2.1.length = I.μBus ∧ r.2.2.length = 3 ∧
            HDoom cands (Seam.bus I) (lbusStmt I hI input ⟨ab.1, ab.2, r.2.1, r.2.2⟩ vals) h
        (Spec.require (T := 0) (Post := fun _ h ↦ P h)
          fun _ hp hc ↦ by
            obtain ⟨hl, hv, W, hW, hR⟩ := hp.resolve_left hc
            exact ⟨hl, hv, W, hW, values_keep I hI hR vals⟩).bind' fun _ ↦
        (Spec.readE (Post := fun _ h ↦ P h)
          (fun _ _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.append _⟩) hLk).bind' fun _ ↦
        (Spec.require (Post := fun _ h ↦ P h) fun _ hp _ ↦ hp).bind' fun _ ↦
        (Spec.ret (Post := fun b h ↦ b.alphas.length = 4 ∧ LBusAt I hI cands input vals b h)
          _).mono (fun _ hp ↦ ⟨h4, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else specOfFalse fun _ hp ↦ h4 hp.1

end Spec4

/-! ## The bus phase and the table sumcheck at the lvm instance, no fidelity hypothesis -/

section Spec

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)
  (cands : Word → Set (∀ i, TheOracle (inst L tabs hτ) i)) {εmax : ℝ≥0∞}

theorem width_pos_vTables (hw : ∀ t ∈ tabs, 0 < t.w) : ∀ t ∈ vTables tabs, 0 < t.width := by
  intro t ht
  simp only [vTables, zipIdx_eq_finRange, List.map_map, List.mem_map] at ht
  obtain ⟨j, -, rfl⟩ := ht
  simp only [Function.comp_apply, width_vTable]
  exact hw _ (List.get_mem _ _)

/-- **The lvm bus phase, then the table sumcheck, with no fidelity hypothesis**: from the
commitment's doom to the table seam on the wire, for the program objects of `LvmM3Fid`. Only the
side conditions (every table reads or seeds, at most thirteen value limbs, positive widths, a
nonzero bus depth) and the errors of `lvmBusTableSpec` remain. -/
noncomputable def lbusTableSpec (hkey : KeysOk tabs) (hw : ∀ t ∈ tabs, 0 < t.w) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : (inst L tabs hτ).μBus ≠ 0) (hab : abError (inst L tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst L tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lvmBusTableProg (vTables tabs) (vLayout tabs) (inst L tabs hτ).μBus (busResV tabs))
      (HDoom cands (Seam.commit (inst L tabs hτ)) ())
      (TablePost (inst L tabs hτ) cands () (colOfL L tabs hτ)) εmax
      (abError (inst L tabs hτ) L₀ + 0) T :=
  (lvmBusSpec4 (inst L tabs hτ) (condOf L tabs hτ hsc) cands () (vals0 L tabs hτ) hfin hcard hμ
      hab he4 hT hlam hxi).bind
    (fun b ↦ if hb : b.alphas.length = 4 ∧ b.point.length = (inst L tabs hτ).μBus ∧
        b.values.length = 3 then
      (tablePhaseSpecG (vTables tabs) (inst L tabs hτ) cands (vLayout tabs) (colOfL L tabs hτ)
        (sOf L tabs hτ hsc b) (busResV tabs b) (tableFidL L tabs hτ hsc hkey b hb.1 hb.2.1)
        (width_pos_vTables tabs hw) le_rfl hfin hcard he3 hTf).mono
        (fun _ hp ↦ hp.2.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else specOfFalse fun _ hp ↦ hb ⟨hp.1, hp.2.1, hp.2.2.1⟩)

end Spec

/-! ## Non-vacuity -/

/-- A one-row table seeding one cell (an input array's shape). -/
def seedTab : Tab where
  τ := 0
  cols := [.com false 0, .com false 1]
  cons := []
  reads := []
  seeds := [(⟨0, CPoly.var 1, [CPoly.var 0]⟩, 0)]
  deg := by
    refine ⟨fun C hC ↦ by simp at hC, fun r hr ↦ by simp at hr, fun s hs ↦ ?_⟩
    simp only [List.mem_singleton] at hs; subst hs
    refine ⟨fun m hm ↦ by simp [CPoly.var] at hm; subst hm; simp, fun P hP ↦ ?_⟩
    simp only [List.mem_singleton] at hP; subst hP
    intro m hm; simp [CPoly.var] at hm; subst hm; simp

/-- **Non-vacuity of `lbusTableSpec`'s side conditions**: a seeding table meets them. -/
theorem seedTab_conditions : AllSc [seedTab] ∧ KeysOk [seedTab] ∧ ∀ t ∈ [seedTab], 0 < t.w := by
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩ <;> simp only [List.mem_singleton] at ht <;>
    subst ht
  · exact Or.inr (by simp [seedTab])
  · exact ⟨fun r hr ↦ by simp [seedTab] at hr, fun s hs ↦ by simp [seedTab] at hs; subst hs; simp⟩
  · simp [seedTab, Tab.w]

end Lvm.M3
end
-- ===== end of `LvmM3FidTab` =====

/-!
# The bus and table phases for `MidSpec`

* **`lbusTableCheckSpec`**: V_S phases 2–3 (`decideProg`'s bus phase, table sumcheck and
  `require (tableCheck)`) on the program objects of `LvmM3Fid`: from the commitment's doom to the
  committed claims' doom (`TablePostC`), over history candidates `cands`.
* **`Spec.glue`**: a family of specifications of one program indexed by `σ h₀` is one
  specification, when `σ` does not move along a run (`G h₀ → σ (h₀ ++ l) = σ h₀`). The fields of
  `Spec` are statements at each start `h₀`, so the glued doom and potential are the family's at
  `σ h₀` (where `G h₀` fails, no doom and potential `1`).
* **`midBusTableSpec`**: `lbusTableCheckSpec` glued at the candidate set `stk '' {p ∈ C h₀ | R p}`
  (candidates `β`, e.g. WP-14's pairs `(qm, qr)`, `stk` their stack). Pre: WP-14's root doom
  `Doomed C (M3Holds ∘ stk ∧ R)` (with a first commitment and `G`); Post `MidTablePost`: some table
  seam output whose committed claims, carried with `R`, are doomed on `C`, and whose claims are
  among the program's (the claims WP-14 hands to the openings).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.TableSumcheck CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

/-! ## Phases 2–3 with the fixed-column check -/

/-- **V_S phases 2–3** on the program objects: the bus phase, the table sumcheck, then the
fixed-column check (`decideProg`'s `require (m.tableCheck pub evals)`); the claims. -/
def lbusTableCheckProg (tabs : List Tab) (μ : ℕ) : VerifierProgram (List Verifier.ColumnClaim) :=
  (lvmBusTableProg (vTables tabs) (vLayout tabs) μ (busResV tabs)).bind fun cl ↦
    (VerifierProgram.require (tableCheckVB tabs cl = true)).bind fun _ ↦ VerifierProgram.ret cl

section Phase

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)
  (cands : Word → Set (∀ i, TheOracle (inst L tabs hτ) i)) {εmax : ℝ≥0∞}

/-- **The lvm bus phase, the table sumcheck and the fixed-column check**: from the commitment's
doom to the committed columns' claims' doom (`TablePostC`), with `lbusTableSpec`'s side
conditions and errors and the closed forms' `FixOk`. -/
noncomputable def lbusTableCheckSpec (hkey : KeysOk tabs) (hw : ∀ t ∈ tabs, 0 < t.w)
    (hfix : FixOk tabs) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : (inst L tabs hτ).μBus ≠ 0) (hab : abError (inst L tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst L tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lbusTableCheckProg tabs (inst L tabs hτ).μBus)
      (HDoom cands (Seam.commit (inst L tabs hτ)) ())
      (TablePostC (inst L tabs hτ) cands () (colOfL L tabs hτ)) εmax
      (abError (inst L tabs hτ) L₀ + 0) T :=
  (lbusTableSpec L tabs hτ hsc cands hkey hw hfin hcard hμ hab he4 hT hlam he3 hTf hxi).bind
    fun cl ↦ (tableCheckSpec L tabs hτ hfix cands cl (T := T)).bind fun _ ↦
      Spec.ret (Post := TablePostC (inst L tabs hτ) cands () (colOfL L tabs hτ)) cl

end Phase

/-! ## Gluing a family of specifications -/

section Glue

variable {α ι : Type} {p : VerifierProgram α} {Pre : ι → List Ev → Prop}
  {Post : ι → α → List Ev → Prop} {εmax L T : ℝ≥0∞}

theorem avg_one : (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ _c : E, (1 : ℝ≥0∞) ≤ 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_le_one _

open Classical in
/-- **Gluing.** A specification of `p` for every index, the index read off the start `σ h₀`, stable
along a run where `G h₀` holds, is one specification: doom and potential are the index's (no doom,
potential `1`, where `G h₀` fails). -/
noncomputable def Spec.glue (σ : List Ev → ι) (G : List Ev → Prop)
    (hσ : ∀ h₀ l, G h₀ → σ (h₀ ++ l) = σ h₀) (F : ∀ i, Spec p (Pre i) (Post i) εmax L T) :
    Spec p (fun h ↦ G h ∧ Pre (σ h) h) (fun a h ↦ Post (σ h) a h) εmax L T where
  D h₀ l := G h₀ ∧ (F (σ h₀)).D h₀ l
  V h₀ l := if G h₀ then (F (σ h₀)).V h₀ l else 1
  le_one h₀ l := by split_ifs <;> simp [(F _).le_one]
  start_D h₀ hp := ⟨hp.1, (F _).start_D h₀ hp.2⟩
  start_V h₀ hp := by rw [if_pos hp.1]; exact (F _).start_V h₀ hp.2
  read x hr ha hD := ⟨hD.1, (F _).read x hr ha hD.2⟩
  grind hr ha hD := ⟨hD.1, (F _).grind hr ha hD.2⟩
  commit word hr ha hw hD := ⟨hD.1, (F _).commit word hr ha hw hD.2⟩
  sample {h₀ l k} hr ha := by
    by_cases hG : G h₀
    · simp only [if_pos hG]; exact (F _).sample hr ha
    · simp only [if_neg hG]; exact avg_one
  query {h₀ l i ps k rows} hr ha hans := by
    by_cases hG : G h₀
    · simp only [if_pos hG]; exact (F _).query hr ha hans
    · simp only [if_neg hG]; exact le_rfl
  moveEnd {h₀ l q} hr ha hm hD := by
    by_cases hG : G h₀
    · rw [if_pos hG]; exact (F _).moveEnd hr ha hm fun h ↦ hD ⟨hG, h⟩
    · rw [if_neg hG]
  retEnd {h₀ l a} hr ha hD := by
    by_cases hG : G h₀
    · rw [if_pos hG]; exact (F _).retEnd hr ha fun h ↦ hD ⟨hG, h⟩
    · rw [if_neg hG]
  retDoom hr ha hD := by rw [if_pos hD.1]; exact (F _).retDoom hr ha hD.2
  post {h₀ l a} hr ha hD := by
    rw [hσ h₀ l hD.1]; exact (F _).post hr ha hD.2
  bound hr hne hm hD := by rw [if_pos hD.1]; exact (F _).bound hr hne hm hD.2

end Glue

/-! ## The doomed candidates' form -/

section Mid

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)
  {β : Type} (C : List Ev → Set β) (stk : β → Column L.μ) (R : β → Prop) {L₀ : ℕ}
  {εmax : ℝ≥0∞}

/-- The stack of a candidate as the instance's one oracle. -/
def oraOf (q : Column L.μ) : ∀ i, TheOracle (inst L tabs hτ) i := fun _ ↦ q

/-- The candidate set the history-doom specs run at: the stacks of the candidates meeting `R`,
finite and at most `L₀` when `C h` is. -/
def candSet (h : List Ev) : Set (∀ i, TheOracle (inst L tabs hτ) i) :=
  (fun p ↦ oraOf L tabs hτ (stk p)) '' {p | p ∈ C h ∧ R p}

theorem candSet_finite {h : List Ev} (hf : (C h).Finite) : (candSet L tabs hτ C stk R h).Finite :=
  (hf.subset fun _ hp ↦ hp.1).image _

theorem candSet_ncard {h : List Ev} (hf : (C h).Finite) :
    (candSet L tabs hτ C stk R h).ncard ≤ (C h).ncard :=
  (Set.ncard_image_le (hf.subset fun _ hp ↦ hp.1)).trans (Set.ncard_le_ncard (fun _ hp ↦ hp.1) hf)

/-- The index of the glued family: a candidate set, finite and at most `L₀`. -/
abbrev CandIdx (L₀ : ℕ) : Type :=
  {S : Set (∀ i, TheOracle (inst L tabs hτ) i) // S.Finite ∧ S.ncard ≤ L₀}

/-- The candidate set of a history as an index. -/
noncomputable def candIdx (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀) (h : List Ev) :
    CandIdx L tabs hτ L₀ :=
  ⟨candSet L tabs hτ C stk R h, candSet_finite L tabs hτ C stk R (hf h),
    (candSet_ncard L tabs hτ C stk R (hf h)).trans (hc h)⟩

/-- **The table seam for `MidSpec`**: a table seam output whose committed claims, with `R`, hold of
no candidate's stack, every claim of which the program returned. (The public lines and the Keccak
predicate are empty for the lvm instance.) -/
def MidTablePost (claims : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∃ tout : Unit × TableOut (inst L tabs hτ),
    Doomed C (fun p ↦ (∀ c ∈ tout.2.columns.toList, (inst L tabs hτ).derived c.col = none →
      c.Holds (stk p)) ∧ R p) h ∧
    (∀ c ∈ tout.2.columns.toList,
      (⟨colOfL L tabs hτ c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈ claims) ∧
    ∃ (st : SumcheckRound.Stmt (Data (inst L tabs hτ)) E (inst L tabs hτ).τmax)
      (v : Vector E (inst L tabs hτ).tableColumns), tout = tableOut (inst L tabs hτ) st v

theorem publicLines_lvm (q : Column L.μ) : (inst L tabs hτ).PublicLinesHold () q := by
  intro l hl; simp [inst] at hl

theorem auxAt_lvm (pt : List E) (q : Column L.μ) : (inst L tabs hτ).auxAt pt q := by
  intro r hr; simp [inst] at hr

/-- **The bus phase, the table sumcheck and the fixed-column check in `MidSpec`'s form**: from
`Doomed C (M3Holds ∘ stk ∧ R)` (at a history with a first commitment, where `G` holds) to
`MidTablePost`. `C` is finite with at most `L₀` candidates, and stable along runs from where `G`
holds (`hCG`; for WP-14's `candPairs`, `G h := 2 ≤ (commits h).length`). -/
noncomputable def midBusTableSpec (hkey : KeysOk tabs) (hw : ∀ t ∈ tabs, 0 < t.w)
    (hfix : FixOk tabs) (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L tabs hτ).μBus ≠ 0) (hab : abError (inst L tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst L tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lbusTableCheckProg tabs (inst L tabs hτ).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L tabs hτ) () (stk p) ∧ R p) h)
      (MidTablePost L tabs hτ C stk R) εmax (abError (inst L tabs hτ) L₀ + 0) T :=
  let σ := candIdx L tabs hτ C stk R hf hc
  ((Spec.glue (Pre := fun (S : CandIdx L tabs hτ L₀) ↦
        HDoom (fun _ ↦ S.1) (Seam.commit (inst L tabs hτ)) ())
      (Post := fun (S : CandIdx L tabs hτ L₀) ↦
        TablePostC (inst L tabs hτ) (fun _ ↦ S.1) () (colOfL L tabs hτ))
      σ G (fun h₀ l hG ↦ by simp only [σ, candIdx, candSet, hCG h₀ l hG])
      fun S ↦ lbusTableCheckSpec L tabs hτ hsc (fun _ ↦ S.1) hkey hw hfix
        (fun _ ↦ S.2.1) (fun _ ↦ S.2.2) hμ hab he4 hT hlam he3 hTf hxi)).mono
    (fun h ⟨hG, ⟨W, hW⟩, hD⟩ ↦ ⟨hG, W, hW, fun o ho hR ↦ by
      obtain ⟨p, ⟨hpC, hpR⟩, rfl⟩ := ho
      exact hD p hpC ⟨hR, hpR⟩⟩)
    (fun cl h hp ↦ by
      obtain ⟨W, tout, -, hD, -, hcl, hout⟩ := hp
      refine ⟨tout, fun p hpC ⟨hcm, hpR⟩ ↦ hD _ ⟨p, ⟨hpC, hpR⟩, rfl⟩
        ⟨hcm, publicLines_lvm L tabs hτ _, auxAt_lvm L tabs hτ _ _⟩, hcl, hout⟩)
    le_rfl le_rfl le_rfl

end Mid

end Lvm.M3
