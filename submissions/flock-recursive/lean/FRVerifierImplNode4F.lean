-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.7 L's rows, A.8 `evalM`/`evalL` on a node;
-- stage INT-9, track L-circ).
import FRVerifierImplNode4T
import FRNodeRows4Plan
import FRVIRTpl4Bridge
import FRSoundness4P4bNames

/-!
# The revision 4.1 node's final ops: `evalM` and `evalL` on the 4.1 rows

S-CN4's `implN4`/`implN4T` take `evalM`/`evalL` from the 3.x base (`implC`: 3.x's plan, 3.x's L
rows at 15/23 coordinates). This module replaces them with the 4.1 node's:

* **`evalM := evalMT4 planOf4 ν`** (S-E12b): the MLEs of `nodeIRows4 ν` (`evalMT4_eq`);
* **`evalL := evalL4I ν`** (new): the MLEs of `lRows4 ν` at `logL` row and `m − 7` cell
  coordinates. Row `i = σ·nJ + j` of `lRows4` is `b·(1 − b) = 0` for the bit cell
  `b = lBase·128 + σ·2^14 + 299 + j` (`lRows4_eq`). With the row point's two-level table (`bt`) and
  the cell point split at 14 coordinates (`eqAtR_splitK`: the `2^14` table of the low coordinates at
  `299 + j`, the high ones at `lBase·128/2^14 + σ`), A's MLE is
  `Σ_σ eq(r4_hi, hb + σ) Σ_j eq(rL, σ nJ + j) eq(r4_lo, 299 + j)`, B's is
  `(Σ_i eq(rL, i))·eq(r4, one) − A`, and C's is `0` (**`evalL4I_eq`**).

**`implN4F base ν`** is `implN4T base ν` with these two fields; **`implN4F_meets`**. For R4
(`FRSoundness4R4FrE.e_fin4`, `not_rejFinE4_node`, R4d D11) the sources are **`srcE4`**
(`nodeIRows4`'s indexed entries) and **`srcL4`** (`ESrc.ofRows (lRows4 ν)`), and **`implN4F_hM`**,
**`implN4F_hL`** are the parameters `hM`/`hL` in the form `e_fin4` takes. **`implTF_implN4F`**
(and `implTF_implN4` for S-E12e's open question): the kind-free template fields stay the base's.
-/

namespace FR
namespace NI4F
open Finset RecursionFast Rev4 Impl NI4 NI4T Circ TEval

/-! ## `eq` split at `k` coordinates -/

/-- The coordinates `k … n − 1` of an `n`-coordinate point. -/
def hiK (k n : ℕ) (a : Array F) : Fin (n - k) → F := fun l => a.getD (k + l) 0

theorem eqAtR_splitK {k n : ℕ} (hk : k ≤ n) (a : Array F) (x : ℕ) :
    eqAtR (ptA n a) x = eqAtR (ptA k a) (x % 2 ^ k) * eqAtR (hiK k n a) (x / 2 ^ k) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  unfold eqAtR ptA hiK
  rw [Fin.prod_univ_eq_prod_range (fun l => if x.testBit l then a.getD l 0 else 1 - a.getD l 0),
    Fin.prod_univ_eq_prod_range (fun l => if (x % 2 ^ k).testBit l then a.getD l 0 else 1 - a.getD l 0),
    Fin.prod_univ_eq_prod_range
      (fun l => if (x / 2 ^ k).testBit l then a.getD (k + l) 0 else 1 - a.getD (k + l) 0),
    Finset.prod_range_add, Nat.add_sub_cancel_left]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    rw [Nat.testBit_mod_two_pow]
    simp [mem_range.1 hl]
  · refine Finset.prod_congr rfl fun l _ => ?_
    rw [Nat.testBit_div_two_pow, add_comm l k]

/-! ## L's rows as a function of the row index -/

/-- Declared bits per slot (A.7: 266 digit bits, 399 step selectors, 7,552 position bits, 3 kind
selector bits). -/
def nJ : ℕ := 8220

/-- **Row `i`'s bit cell**: slot `i / nJ`, bit `i % nJ`. -/
def cellL (κ : NodeKind) (i : ℕ) : ℕ := κ.lBase * 128 + i / nJ * 2 ^ 14 + 299 + i % nJ

/-- L row `i` (`b · (1 − b) = 0` at `b = cellL κ i`). -/
def rowL (κ : NodeKind) (i : ℕ) : Row :=
  ⟨Lin.cell (cellL κ i), (Lin.cell κ.oneCell).sub (Lin.cell (cellL κ i)), []⟩

theorem flatMap_lBits (κ : NodeKind) (S : ℕ) :
    (List.range S).flatMap (lBitCells4 κ) = (List.range (S * nJ)).map (cellL κ) := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.map_append,
      List.flatMap_singleton, List.map_map]
    refine congrArg ((List.range (S * nJ)).map (cellL κ) ++ ·) ?_
    simp only [lBitCells4, show 266 + 399 + 7552 + 3 = nJ from rfl]
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.1 hj
    have h1 : (S * nJ + j) / nJ = S := by simp only [nJ] at hj ⊢; omega
    have h2 : (S * nJ + j) % nJ = j := by simp only [nJ] at hj ⊢; omega
    simp only [Function.comp, cellL, h1, h2]

/-- **`lRows4` row by row.** -/
theorem lRows4_eq (κ : NodeKind) : lRows4 κ = (List.range (κ.vslots * nJ)).map (rowL κ) := by
  rw [lRows4, flatMap_lBits, List.map_map]; rfl

/-! ## The bounds -/

theorem lCells_fit (κ : NodeKind) : κ.lBase * 128 + κ.vslots * 2 ^ 14 ≤ κ.oneCell ∧
    κ.oneCell < 2 ^ (κ.m - 7) ∧ κ.lBase * 128 % 2 ^ 14 = 0 ∧ κ.vslots * nJ ≤ 2 ^ κ.dims.logL ∧
    9 ≤ κ.dims.logL ∧ 14 ≤ κ.m - 7 := by
  obtain ⟨-, h2, h3, h4⟩ := regions_fit κ
  have h5 := lSlots_fit κ
  have hnl : κ.nL / 128 * 128 = κ.nL := by cases κ <;> decide
  have hnm : 0 < κ.nM / 128 := by cases κ <;> decide
  have hlb : κ.lBase % 256 = 0 := by unfold NodeKind.lBase; omega
  have hd : 9 ≤ κ.dims.logL ∧ 14 ≤ κ.m - 7 := by cases κ <;> decide
  simp only [NodeKind.cells] at h4
  have h6 : κ.vslots * nJ ≤ κ.vslots * 2 ^ 14 := Nat.mul_le_mul_left _ (by simp only [nJ]; norm_num)
  simp only [NodeKind.oneCell] at h4 ⊢
  refine ⟨by omega, by omega, by omega, h6.trans (h5.trans_eq rfl), hd⟩

theorem cellL_lt (κ : NodeKind) {i : ℕ} (hi : i < κ.vslots * nJ) : cellL κ i < 2 ^ (κ.m - 7) := by
  obtain ⟨h1, h2, -⟩ := lCells_fit κ
  have : i / nJ < κ.vslots := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
  have : i % nJ < nJ := Nat.mod_lt _ (by decide)
  simp only [cellL, nJ] at *
  omega

/-- The bit cell of row `σ nJ + j`, split at 14 coordinates. -/
theorem cellL_split (κ : NodeKind) {σ j : ℕ} (hj : j < nJ) :
    cellL κ (σ * nJ + j) % 2 ^ 14 = 299 + j ∧
      cellL κ (σ * nJ + j) / 2 ^ 14 = κ.lBase * 128 / 2 ^ 14 + σ := by
  obtain ⟨-, -, h3, -⟩ := lCells_fit κ
  have h1 : (σ * nJ + j) / nJ = σ := by simp only [nJ] at hj ⊢; omega
  have h2 : (σ * nJ + j) % nJ = j := by simp only [nJ] at hj ⊢; omega
  simp only [cellL, h1, h2]
  simp only [nJ] at hj
  omega

/-! ## `evalL` -/

/-- Slot `σ`'s two sums over its `nJ` rows: `Σ_j eq(rL, σ nJ + j)` and
`Σ_j eq(rL, σ nJ + j) · eq(r4_lo, 299 + j)` (`T`: the row point's tables, `tY`: the low cell
coordinates' table). -/
def slotL (T : BT) (tY : Array F) (σ : ℕ) : F × F :=
  sumTo nJ fun j => let e := T.eq (σ * nJ + j); (e, e * tY.getD (299 + j) 0)

/-- **`evalL` of a 4.1 node**: `lRows4 κ`'s three matrices at `(rL, r4)` (`logL` and `m − 7`
coordinates). -/
def evalL4I (κ : NodeKind) (rL r4 : Array F) : F × F × F :=
  let T := bt κ.dims.logL rL
  let tY := eqTable (List.ofFn (ptA 14 r4))
  let hb := κ.lBase * 128 / 2 ^ 14
  let s := sumTo κ.vslots fun σ =>
    let p := slotL T tY σ
    (p.1, eqAtR (hiK 14 (κ.m - 7) r4) (hb + σ) * p.2)
  (s.2, s.1 * eqAtR (ptA (κ.m - 7) r4) κ.oneCell - s.2, 0)

/-- **`evalL`'s specification**: the MLEs of `lRows4 κ` (`FRVIREval.evalRowsSpec`). -/
noncomputable def evalLS4 (κ : NodeKind) (rL r4 : Array F) : F × F × F :=
  Eval.evalRowsSpec κ.dims.logL (κ.m - 7) (lRows4 κ) rL r4

theorem sum_range_mul {M : Type*} [AddCommMonoid M] (S J : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (S * J), f i = ∑ σ ∈ range S, ∑ j ∈ range J, f (σ * J + j) := by
  induction S with
  | zero => simp
  | succ S ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem list_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem zipIdx_range_map {α : Type*} (g : ℕ → α) (n : ℕ) :
    ((List.range n).map g).zipIdx = (List.range n).map fun i => (g i, i) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem_zipIdx]

theorem sparse_flatMap {a b : ℕ} (l : List ℕ) (f : ℕ → Eval.Entries) (τ : Fin a → F) (σ : Fin b → F) :
    Eval.sparseEval (l.flatMap f) τ σ = (l.map fun i => Eval.sparseEval (f i) τ σ).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    simp only [Eval.sparseEval, List.map_append, List.sum_append]

theorem sparse_rows {a b : ℕ} (n : ℕ) (g : ℕ → Row) (sel : Row → Lin) (τ : Fin a → F) (σ : Fin b → F) :
    Eval.sparseEval (Eval.entriesOf sel ((List.range n).map g)) τ σ =
      ∑ i ∈ range n, Eval.sparseEval ((sel (g i)).map fun t => (i, t.1, t.2)) τ σ := by
  rw [Eval.entriesOf, zipIdx_range_map, List.flatMap_map, sparse_flatMap, list_sum_range]

theorem eqAt_R (n : ℕ) (a : Array F) (x : ℕ) : Eval.eqAt (Eval.ptOf n a) x = eqAtR (ptA n a) x := rfl

/-- The specification's three sums over the rows. -/
theorem evalLS4_sums (κ : NodeKind) (rL r4 : Array F) :
    evalLS4 κ rL r4 =
      (∑ i ∈ range (κ.vslots * nJ), eqAtR (ptA κ.dims.logL rL) i * eqAtR (ptA (κ.m - 7) r4) (cellL κ i),
       (∑ i ∈ range (κ.vslots * nJ), eqAtR (ptA κ.dims.logL rL) i) * eqAtR (ptA (κ.m - 7) r4) κ.oneCell -
         ∑ i ∈ range (κ.vslots * nJ), eqAtR (ptA κ.dims.logL rL) i * eqAtR (ptA (κ.m - 7) r4) (cellL κ i),
       0) := by
  obtain ⟨-, h2, -, h4, -⟩ := lCells_fit κ
  rw [evalLS4, ← Eval.evalRows_eq, Eval.evalRows, lRows4_eq, sparse_rows, sparse_rows, sparse_rows]
  have hi : ∀ i ∈ range (κ.vslots * nJ), i < 2 ^ κ.dims.logL := fun i hi =>
    lt_of_lt_of_le (mem_range.1 hi) h4
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only
  · refine Finset.sum_congr rfl fun i hm => ?_
    simp only [rowL, Lin.cell, List.map_cons, List.map_nil, Eval.sparseEval, List.sum_cons,
      List.sum_nil, add_zero, eqAt_R, hi i hm, cellL_lt κ (mem_range.1 hm), and_self, ↓reduceIte,
      one_mul]
  · simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hm => ?_
    simp only [rowL, Lin.cell, Lin.sub, Lin.smul, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Eval.sparseEval, List.sum_cons, List.sum_nil, add_zero, eqAt_R, hi i hm,
      cellL_lt κ (mem_range.1 hm), h2, and_self, ↓reduceIte]
    ring
  · simp [rowL, Eval.sparseEval]

/-- The implementation's sums (`sumTo` as `Finset` sums). -/
theorem evalL4I_sums (κ : NodeKind) (rL r4 : Array F) :
    evalL4I κ rL r4 =
      (∑ σ ∈ range κ.vslots, eqAtR (hiK 14 (κ.m - 7) r4) (κ.lBase * 128 / 2 ^ 14 + σ) *
          ∑ j ∈ range nJ, (bt κ.dims.logL rL).eq (σ * nJ + j) * (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0,
       (∑ σ ∈ range κ.vslots, ∑ j ∈ range nJ, (bt κ.dims.logL rL).eq (σ * nJ + j)) *
          eqAtR (ptA (κ.m - 7) r4) κ.oneCell -
        ∑ σ ∈ range κ.vslots, eqAtR (hiK 14 (κ.m - 7) r4) (κ.lBase * 128 / 2 ^ 14 + σ) *
          ∑ j ∈ range nJ, (bt κ.dims.logL rL).eq (σ * nJ + j) * (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0,
       0) := by
  simp only [evalL4I, slotL, sumTo_eq, Prod.fst_sum, Prod.snd_sum]

/-- **`evalL_eq` for the 4.1 nodes**: `evalL4I` is the MLE of `lRows4 κ`. -/
theorem evalL4I_eq (κ : NodeKind) (rL r4 : Array F) : evalL4I κ rL r4 = evalLS4 κ rL r4 := by
  obtain ⟨-, -, -, h4, h9, h14⟩ := lCells_fit κ
  rw [evalLS4_sums, sum_range_mul, sum_range_mul, evalL4I_sums]
  have hrow : ∀ σ ∈ range κ.vslots, ∀ j ∈ range nJ,
      (bt κ.dims.logL rL).eq (σ * nJ + j) = eqAtR (ptA κ.dims.logL rL) (σ * nJ + j) := by
    intro σ hσ j hj
    refine bt_eq h9 rL (lt_of_lt_of_le ?_ h4)
    have := mem_range.1 hσ; have := mem_range.1 hj
    calc σ * nJ + j < σ * nJ + nJ := by omega
      _ = (σ + 1) * nJ := by ring
      _ ≤ κ.vslots * nJ := Nat.mul_le_mul_right _ (by omega)
  have hcol : ∀ σ, ∀ j ∈ range nJ, eqAtR (ptA (κ.m - 7) r4) (cellL κ (σ * nJ + j)) =
      (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0 *
        eqAtR (hiK 14 (κ.m - 7) r4) (κ.lBase * 128 / 2 ^ 14 + σ) := by
    intro σ j hj
    have hj' : j < nJ := mem_range.1 hj
    obtain ⟨e1, e2⟩ := cellL_split κ (σ := σ) hj'
    rw [eqAtR_splitK h14, e1, e2, eqTable_ofFn_getD _ (by simp only [nJ] at hj'; omega)]
  have hA : ∑ σ ∈ range κ.vslots, eqAtR (hiK 14 (κ.m - 7) r4) (κ.lBase * 128 / 2 ^ 14 + σ) *
        ∑ j ∈ range nJ, (bt κ.dims.logL rL).eq (σ * nJ + j) * (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0 =
      ∑ σ ∈ range κ.vslots, ∑ j ∈ range nJ,
        eqAtR (ptA κ.dims.logL rL) (σ * nJ + j) * eqAtR (ptA (κ.m - 7) r4) (cellL κ (σ * nJ + j)) := by
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hrow σ hσ j hj, hcol σ j hj]; ring
  have hS : ∑ σ ∈ range κ.vslots, ∑ j ∈ range nJ, (bt κ.dims.logL rL).eq (σ * nJ + j) =
      ∑ σ ∈ range κ.vslots, ∑ j ∈ range nJ, eqAtR (ptA κ.dims.logL rL) (σ * nJ + j) :=
    Finset.sum_congr rfl fun σ hσ => Finset.sum_congr rfl fun j hj => hrow σ hσ j hj
  rw [hA, hS]

/-! ## The node's final ops -/

/-- **`implN4F base ν`**: `implN4T base ν` (S-CN4's node ops with the computed `targetS`, S-T2's
`rsWeight`) with the 4.1 node's `evalM` (`evalMT4 planOf4 ν`) and `evalL` (`evalL4I ν`). -/
def implN4F (base : NodeKind → OpImpl) (ν : NodeKind) : OpImpl :=
  { implN4T base ν with evalM := evalMT4 planOf4 ν, evalL := evalL4I ν }

/-- Its specification: `specN4` with the MLEs of `nodeIRows4 ν` and `lRows4 ν`. -/
noncomputable def specN4F (spec : NodeKind → OpSpec) (ν : NodeKind) : OpSpec :=
  { specN4 spec ν with evalM := evalMS4 ν, evalL := evalLS4 ν }

/-- **`implN4F ⊨ specN4F`**, given the base's ops only. -/
theorem implN4F_meets {base : NodeKind → OpImpl} {spec : NodeKind → OpSpec} (ν : NodeKind)
    (h : (base ν).Meets (spec ν)) : (implN4F base ν).Meets (specN4F spec ν) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -, h10, h11, h12, h13, h14, h15, h16, h17⟩ :=
    implN4T_meets ν h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun a b => evalMT4_eq planOf4 ν a b, fun a b => evalL4I_eq ν a b,
    h10, h11, h12, h13, h14, h15, h16, h17⟩

/-! ## For R4: `RejFinE4`'s parameters `hM`, `hL` (R4d D11) -/

/-- **The node's M source**: `nodeIRows4 ν`'s indexed entries. -/
noncomputable def srcE4 (ν : NodeKind) : Snd.P4b.ESrc := Snd.P4b.ESrc.ofIRows (nodeIRows4 ν)

/-- **The node's L source**: `lRows4 ν` (row `i` at index `i`). -/
def srcL4 (ν : NodeKind) : Snd.P4b.ESrc := Snd.P4b.ESrc.ofRows (lRows4 ν)

/-- **`hM`** in `FRSoundness4R4FrE.e_fin4`'s form, for `implN4F`. -/
theorem implN4F_hM (base : NodeKind → OpImpl) (ν : NodeKind) :
    ∀ r2 r4 : Array F, r2.size = Snd.P4b.e2R ν → r4.size = Snd.P4b.ncR ν → (implN4F base ν).evalM r2 r4 =
      (Eval.matMLE (srcE4 ν).ea (FR.Impl.ptA (Snd.P4b.e2R ν) r2) (FR.Impl.ptA (Snd.P4b.ncR ν) r4),
       Eval.matMLE (srcE4 ν).eb (FR.Impl.ptA (Snd.P4b.e2R ν) r2) (FR.Impl.ptA (Snd.P4b.ncR ν) r4),
       Eval.matMLE (srcE4 ν).ec (FR.Impl.ptA (Snd.P4b.e2R ν) r2) (FR.Impl.ptA (Snd.P4b.ncR ν) r4)) :=
  fun r2 r4 _ _ => by cases ν <;> exact evalMT4_eq planOf4 _ r2 r4

/-- **`hL`** in `FRSoundness4R4FrE.e_fin4`'s form, for `implN4F`. -/
theorem implN4F_hL (base : NodeKind → OpImpl) (ν : NodeKind) :
    ∀ rL r4 : Array F, rL.size = Snd.P4b.lrR ν → r4.size = Snd.P4b.ncR ν → (implN4F base ν).evalL rL r4 =
      (Eval.matMLE (srcL4 ν).ea (FR.Impl.ptA (Snd.P4b.lrR ν) rL) (FR.Impl.ptA (Snd.P4b.ncR ν) r4),
       Eval.matMLE (srcL4 ν).eb (FR.Impl.ptA (Snd.P4b.lrR ν) rL) (FR.Impl.ptA (Snd.P4b.ncR ν) r4),
       Eval.matMLE (srcL4 ν).ec (FR.Impl.ptA (Snd.P4b.lrR ν) rL) (FR.Impl.ptA (Snd.P4b.ncR ν) r4)) :=
  fun rL r4 _ _ => evalL4I_eq ν rL r4

/-! ## The kind-free template fields (S-E12e's open question) -/

/-- **`implN4`'s kind-free template fields are its base's** (`slotW` is `slotWI`; `withRS4` only
changes `rsWeight`, which no kept key reads): with a base meeting `ImplT`, `ImplTF keys41` holds. -/
theorem implTF_implN4 {base : NodeKind → OpImpl} (hT : ∀ ν, ImplT (base ν))
    (tS : NodeKind → Array F → Array F) (ν : NodeKind) : ImplTF keys41 (implN4 base tS ν) :=
  fun k hk => by
    have h := (hT ν).toF keys41 k hk
    cases k
    case shiftMask => exact absurd hk Bool.false_ne_true
    all_goals (simp only [KeyImpl, implN4, Impl.withRS4] at h ⊢; try first | exact h | exact fun _ => trivial)

theorem implTF_implN4F {base : NodeKind → OpImpl} (hT : ∀ ν, ImplT (base ν)) (ν : NodeKind) :
    ImplTF keys41 (implN4F base ν) :=
  fun k hk => by
    have h := (hT ν).toF keys41 k hk
    cases k
    case shiftMask => exact absurd hk Bool.false_ne_true
    all_goals (simp only [KeyImpl, implN4F, implN4T, implN4, Impl.withRS4] at h ⊢; try first | exact h | exact fun _ => trivial)

/-- At the 3.x base `implC` (`implCWith_implT`). -/
theorem implTF_implN4F_C (fin : Finals) (lRows : List Row) (κs₀ : F) (ν : NodeKind) :
    ImplTF keys41 (implN4F (fun _ => Impl.implC fin lRows κs₀) ν) :=
  implTF_implN4F (fun _ => Impl.implCWith_implT _ _) ν

/-- **`implN4F`'s `shiftMask` meets prototype 0's route at index `ι`** (`routeOk_node`). -/
theorem routeOk_implN4F (base : NodeKind → OpImpl) (ι : Kind) :
    RouteOk (protoR 0) (implN4F base (nodeOf ι)) ι :=
  routeOk_node (impl := implN4F base (nodeOf ι)) ι (by dsimp only [implN4F, implN4T, implN4])

/-! ## Controls -/

/-- (+) Row `0` is slot 0's first declared bit (cell `lBase·128 + 299`), row `nJ` slot 1's first;
(−) the two are not the same cell. -/
theorem cellL_ctl (κ : NodeKind) : cellL κ 0 = κ.lBase * 128 + 299 ∧
    cellL κ nJ = κ.lBase * 128 + 2 ^ 14 + 299 ∧ cellL κ 0 ≠ cellL κ nJ := by
  simp only [cellL, nJ]; omega

/-- (+) `lRows4 N4` has `5 · 8,220` rows, each `b · (1 − b) = 0` (C empty); (−) not `N2`'s count. -/
theorem lRows4_ctl : (lRows4 .N4).length = 5 * 8220 ∧ (lRows4 .N2).length ≠ 5 * 8220 ∧
    ∀ r ∈ lRows4 .N4, r.c = [] := by
  refine ⟨by rw [lRows4_eq]; simp; rfl, by rw [lRows4_eq]; simp; decide, fun r hr => ?_⟩
  rw [lRows4_eq] at hr
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr
  rfl

/-- (+) `implN4F`'s `evalM`/`evalL` are the 4.1 node's, its `shiftMask` S-CN4's; (−) its L source
differs between kinds (`N4`: 5 slots of 8,220 entries in A, `N2`: 3). -/
theorem implN4F_ctl (base : NodeKind → OpImpl) (ν : NodeKind) :
    (implN4F base ν).evalM = evalMT4 planOf4 ν ∧ (implN4F base ν).evalL = evalL4I ν ∧
      (implN4F base ν).shiftMask = shiftMask4I ν ∧
      (srcL4 .N4).ea.length = 5 * 8220 ∧ (srcL4 .N2).ea.length = 3 * 8220 := by
  refine ⟨by dsimp only [implN4F], by dsimp only [implN4F], by dsimp only [implN4F, implN4T, implN4],
    ?_, ?_⟩ <;>
  · simp only [srcL4, Snd.P4b.ESrc.ofRows, Eval.entriesOf, lRows4_eq, zipIdx_range_map,
      List.flatMap_map, rowL, Lin.cell, List.map_cons, List.map_nil, List.length_flatMap,
      List.length_cons, List.length_nil, List.map_const', List.length_range, List.sum_replicate]
    rfl

end NI4F
end FR
