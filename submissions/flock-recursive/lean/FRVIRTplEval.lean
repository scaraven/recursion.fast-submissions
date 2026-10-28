-- New for `flock-recursive` (BLUEPRINT A.11, §4.4, stage S-E3; track L-circ).
import FRVIRTplExt
import FRVIREval
import Mathlib.Data.Nat.Size

/-!
# The templated matrix MLEs (`evalM`, `evalMK`, `evalL`) and `tpl_mle`

BLUEPRINT §4.4, A.11. Region M's rows are indexed: slot `σ`'s skeleton row `j` at `σ·2^20 + j`, and
instance `inst` of template `X` at `σ·2^20 + rowBase_X + inst·2^a + j`, its local `k` at cell
`cellBase_X + inst·2^b + k` (`slotIRows`). The MLE of a matrix `Σ_{x,y} eq(τ,x) eq(σ,y) M[x][y]`
is the sparse sum over its entries (`FRVIREval.sparse_eq`); here the sparse sum over an instance's
entries is put in **closed form** (`tpl_mle`):

  `eq(τ_hi, ⌊rowBase/2^a⌋ + inst) · ( eq(σ_hi, ⌊cellBase/2^b⌋ + inst) · LOC + ONE · E(one)
     + Σ_{(i,u) ∈ IT} u · E(ins_i) )`

where `LOC = Σ_{(j, loc k, c)} eq(τ_lo, j) c eq(σ_lo, k)`, `ONE`, `IT` are computed **once per
template** (A.11's local class), and `E(ℓ) = Σ_{(cell, c) ∈ ℓ} c eq(σ, cell)` reads the instance's
input forms (the shared and irregular classes). The skeleton's rows stay sparse. Everything is
over a commutative ring `R` with the coefficients mapped by `ι : F →+* R`: `R = F` is `evalM`,
`R = K` (`τ` mapped) is `evalMK`.
-/

namespace FR
namespace TEval
open Circ Tpl Finset

variable {R : Type*} [CommRing R] (ι : F →+* R)

/-! ## `eq` at an index -/

/-- `eq(t, x)` over the first `n` coordinates of `t`. -/
def eqN (n : ℕ) (t : ℕ → R) (x : ℕ) : R := ∏ l ∈ range n, if x.testBit l then t l else 1 - t l

/-- `eq(t, x)` on the cube, `0` off it (the sparse sum's guard). -/
def gN (n : ℕ) (t : ℕ → R) (x : ℕ) : R := if x < 2 ^ n then eqN n t x else 0

/-- **The split**: `eq(t, H·2^A + j) = eq(t_lo, j) · eq(t_hi, H)`. -/
theorem eqN_split {A n : ℕ} (hA : A ≤ n) (t : ℕ → R) (H : ℕ) {j : ℕ} (hj : j < 2 ^ A) :
    eqN n t (2 ^ A * H + j) = eqN A t j * eqN (n - A) (fun l => t (A + l)) H := by
  unfold eqN
  rw [show n = A + (n - A) by omega, Finset.prod_range_add, show A + (n - A) - A = n - A by omega]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    simp only [Nat.testBit_two_pow_mul_add _ hj, Finset.mem_range.1 hl, if_true]
  · refine Finset.prod_congr rfl fun l _ => ?_
    simp only [Nat.testBit_two_pow_mul_add _ hj, show ¬ A + l < A by omega, if_false,
      Nat.add_sub_cancel_left]

theorem gN_split {A n : ℕ} (hA : A ≤ n) (t : ℕ → R) (H : ℕ) {j : ℕ} (hj : j < 2 ^ A) :
    gN n t (2 ^ A * H + j) = eqN A t j * gN (n - A) (fun l => t (A + l)) H := by
  unfold gN
  have : 2 ^ A * H + j < 2 ^ n ↔ H < 2 ^ (n - A) := by
    rw [show 2 ^ n = 2 ^ A * 2 ^ (n - A) by rw [← pow_add]; congr 1; omega]
    constructor
    · intro h; by_contra h'; push_neg at h'
      have := Nat.mul_le_mul_left (2 ^ A) h'; omega
    · intro h; have := Nat.mul_le_mul_left (2 ^ A) (Nat.succ_le_of_lt h); rw [Nat.mul_succ] at this; omega
  by_cases h : H < 2 ^ (n - A)
  · rw [if_pos (this.2 h), if_pos h, eqN_split hA t H hj]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h, mul_zero]

/-! ## Matrices, forms, rows -/

/-- The three matrices. -/
inductive Mat where
  | a | b | c

def Mat.r : Mat → Row → Lin
  | .a, r => r.a | .b, r => r.b | .c, r => r.c

def Mat.t : Mat → RowT → LinT
  | .a, r => r.a | .b, r => r.b | .c, r => r.c

theorem Mat.r_inst (s : Mat) (one : Lin) (ins : List Lin) (cb : ℕ) (r : RowT) :
    s.r (instRow one ins cb r) = instLin one ins cb (s.t r) := by cases s <;> rfl

/-- `Σ_{(cell, c)} ι c · eq(σ, cell)`. -/
def linE (m : ℕ) (σ : ℕ → R) (l : Lin) : R := (l.map fun t => ι t.2 * gN m σ t.1).sum

/-- **The sparse value of indexed rows** (the specification's sparse sum, `rowsVal_eq`). -/
def rowsVal (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (rows : List (ℕ × Row)) : R :=
  (rows.map fun p => gN n τ p.1 * linE ι m σ (s.r p.2)).sum

/-- An instantiated form's value: wire by wire. -/
def wireE (m : ℕ) (σ : ℕ → R) (one : Lin) (ins : List Lin) (cb : ℕ) : Wire → R
  | .one => linE ι m σ one
  | .inp i => linE ι m σ (ins.getD i [])
  | .loc k => gN m σ (cb + k)

theorem linE_smul (m : ℕ) (σ : ℕ → R) (c : F) (l : Lin) :
    linE ι m σ (l.smul c) = ι c * linE ι m σ l := by
  simp only [linE, Lin.smul, List.map_map, Function.comp_def, map_mul, mul_assoc, List.sum_map_mul_left]

theorem linE_instLin (m : ℕ) (σ : ℕ → R) (one : Lin) (ins : List Lin) (cb : ℕ) (l : LinT) :
    linE ι m σ (instLin one ins cb l) = (l.map fun t => ι t.2 * wireE ι m σ one ins cb t.1).sum := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    obtain ⟨w, c⟩ := t
    have e : instLin one ins cb ((w, c) :: l) = (match w with
      | .one => one.smul c | .inp i => (ins.getD i []).smul c | .loc k => [(cb + k, c)]) ++
        instLin one ins cb l := rfl
    rw [e, linE, List.map_append, List.sum_append, ← linE, ← linE, ih, List.map_cons, List.sum_cons]
    congr 1
    cases w with
    | one => exact linE_smul ι m σ c one
    | inp i => exact linE_smul ι m σ c _
    | loc k => simp [linE, wireE]

/-! ## One instance in closed form (`tpl_mle`) -/

/-- The template's terms with the row factor: `(wire, eq(τ_lo, j) · ι c)`. -/
@[specialize]
def ttOf (s : Mat) (T : Tpl) (eτ : ℕ → R) : List (Wire × R) :=
  T.rows.zipIdx.flatMap fun p => (s.t p.1).map fun t => (t.1, eτ p.2 * ι t.2)

/-- The local part `LOC`. -/
@[specialize]
def locSum (eσ : ℕ → R) (tt : List (Wire × R)) : R :=
  (tt.map fun p => match p.1 with | .loc k => p.2 * eσ k | _ => 0).sum
/-- The `one` part. -/
@[specialize]
def oneSum (tt : List (Wire × R)) : R := (tt.map fun p => match p.1 with | .one => p.2 | _ => 0).sum
/-- The input terms. -/
@[specialize]
def inpList (tt : List (Wire × R)) : List (ℕ × R) :=
  tt.filterMap fun p => match p.1 with | .inp i => some (i, p.2) | _ => none

/-- **The closed form of one instance**: `Hτ · (Hσ · LOC + ONE · E(one) + Σ_IT u · E(ins_i))`. -/
def instClosed (m : ℕ) (σ : ℕ → R) (one : Lin) (ins : List Lin) (Hτ Hσ loc onew : R)
    (it : List (ℕ × R)) : R :=
  Hτ * (Hσ * loc + onew * linE ι m σ one + (it.map fun p => p.2 * linE ι m σ (ins.getD p.1 [])).sum)

theorem partition (m : ℕ) (σ : ℕ → R) (one : Lin) (ins : List Lin) (cb : ℕ) (eσ : ℕ → R) (Hσ : R)
    (tt : List (Wire × R)) (hloc : ∀ p ∈ tt, ∀ k, p.1 = .loc k → gN m σ (cb + k) = eσ k * Hσ) :
    (tt.map fun p => p.2 * wireE ι m σ one ins cb p.1).sum =
      Hσ * locSum eσ tt + oneSum tt * linE ι m σ one +
        ((inpList tt).map fun p => p.2 * linE ι m σ (ins.getD p.1 [])).sum := by
  induction tt with
  | nil => simp [locSum, oneSum, inpList]
  | cons p tt ih =>
    rw [List.map_cons, List.sum_cons, ih fun q hq => hloc q (List.mem_cons_of_mem _ hq)]
    obtain ⟨w, u⟩ := p
    cases w with
    | one => simp [locSum, oneSum, inpList, wireE]; ring
    | inp i => simp [locSum, oneSum, inpList, wireE]; ring
    | loc k =>
      have := hloc _ (List.mem_cons_self ..) k rfl
      simp only [wireE] at this ⊢
      simp [locSum, oneSum, inpList, this]; ring

/-- A template row index is below `2^rbits`. -/
theorem lt_rbits (T : Tpl) {j : ℕ} (hj : j < T.rows.length) : j < 2 ^ T.rbits := by
  unfold Tpl.rbits
  exact lt_of_le_of_lt (show j ≤ T.rows.length - 1 by omega) (Nat.lt_size_self _)

theorem le_foldl_max (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons x l ih => exact le_trans (le_max_left _ _) (ih _)

theorem mem_le_foldl_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) (a : ℕ) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y l ih =>
    rcases List.mem_cons.1 hx with rfl | h
    · exact le_trans (le_max_right _ _) (le_foldl_max _ _)
    · exact ih h _

theorem mlStep_ge (a : ℕ) (t : Wire × F) : a ≤ mlStep a t := by
  obtain ⟨w, c⟩ := t; cases w <;> simp [mlStep]

theorem foldl_ml_ge (l : LinT) (a : ℕ) : a ≤ l.foldl mlStep a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons t l ih => exact le_trans (mlStep_ge a t) (ih _)

theorem maxLoc_ge {l : LinT} {k : ℕ} {c : F} (h : (Wire.loc k, c) ∈ l) : k ≤ l.maxLoc := by
  unfold LinT.maxLoc
  suffices ∀ a, k ≤ l.foldl mlStep a from this 0
  induction l with
  | nil => simp at h
  | cons t l ih =>
    intro a
    rcases List.mem_cons.1 h with rfl | h'
    · exact le_trans (by simp [mlStep]) (foldl_ml_ge l _)
    · exact ih h' _

/-- A referenced local is below `2^cbits`. -/
theorem lt_cbits (T : Tpl) (s : Mat) {r : RowT} (hr : r ∈ T.rows) {k : ℕ} {c : F}
    (h : (Wire.loc k, c) ∈ s.t r) : k < 2 ^ T.cbits := by
  unfold Tpl.cbits
  refine lt_of_le_of_lt (le_trans ?_ (le_max_left _ _)) (Nat.lt_size_self _)
  have hk : k ≤ max r.a.maxLoc (max r.b.maxLoc r.c.maxLoc) := by
    cases s <;> simp only [Mat.t] at h <;> have := maxLoc_ge h <;> omega
  unfold Tpl.maxLoc
  exact le_trans hk (mem_le_foldl_max (l := T.rows.map fun r => max r.a.maxLoc
    (max r.b.maxLoc r.c.maxLoc)) (List.mem_map.2 ⟨r, hr, rfl⟩) 0)

theorem zipIdx_mem {α : Type*} {l : List α} {p : α × ℕ} (h : p ∈ l.zipIdx) :
    p.1 ∈ l ∧ p.2 < l.length := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  simp only [List.getElem_zipIdx, List.length_zipIdx] at hi ⊢
  exact ⟨List.getElem_mem _, by simpa using hi⟩

/-- The rows of instance `(inst, ins)` of `T` at row base `X` (a multiple of `2^rbits`). -/
def instIRows (T : Tpl) (one : Lin) (ins : List Lin) (X cb : ℕ) : List (ℕ × Row) :=
  T.rows.zipIdx.map fun p => (X + p.2, instRow one ins cb p.1)

theorem sum_flatMap_map {α β : Type*} (l : List α) (f : α → List β) (g : β → R) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- **`tpl_mle`**: an instance's sparse value is its closed form, when its row base is
`2^A · Xh` and its cell base `2^B · Ch` (A.11's alignment), `A = rbits`, `B = cbits`. -/
theorem tpl_mle (s : Mat) {n m : ℕ} (τ σ : ℕ → R) (T : Tpl) (one : Lin) (ins : List Lin)
    (Xh Ch : ℕ) (hA : T.rbits ≤ n) (hB : T.cbits ≤ m) (eτ eσ : ℕ → R)
    (heτ : ∀ j < T.rows.length, eτ j = eqN T.rbits τ j)
    (heσ : ∀ k < 2 ^ T.cbits, eσ k = eqN T.cbits σ k) :
    rowsVal ι s n m τ σ (instIRows T one ins (2 ^ T.rbits * Xh) (2 ^ T.cbits * Ch)) =
      instClosed ι m σ one ins (gN (n - T.rbits) (fun l => τ (T.rbits + l)) Xh)
        (gN (m - T.cbits) (fun l => σ (T.cbits + l)) Ch) (locSum eσ (ttOf ι s T eτ))
        (oneSum (ttOf ι s T eτ)) (inpList (ttOf ι s T eτ)) := by
  set Hτ := gN (n - T.rbits) (fun l => τ (T.rbits + l)) Xh
  set Hσ := gN (m - T.cbits) (fun l => σ (T.cbits + l)) Ch
  set cb := 2 ^ T.cbits * Ch
  have hloc : ∀ p ∈ ttOf ι s T eτ, ∀ k, p.1 = .loc k → gN m σ (cb + k) = eσ k * Hσ := by
    intro p hp k hk
    simp only [ttOf, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨q, hq, ⟨w, c⟩, hwc, rfl⟩ := hp
    simp only at hk; subst hk
    have hk' := lt_cbits T s (zipIdx_mem hq).1 hwc
    rw [gN_split hB _ _ hk', heσ k hk']
  have hrow : ∀ p ∈ T.rows.zipIdx,
      gN n τ (2 ^ T.rbits * Xh + p.2) * linE ι m σ (s.r (instRow one ins cb p.1)) =
      Hτ * ((s.t p.1).map fun t => eτ p.2 * ι t.2 * wireE ι m σ one ins cb t.1).sum := by
    intro p hp
    have hj := (zipIdx_mem hp).2
    rw [gN_split hA _ _ (lt_rbits T hj), Mat.r_inst, linE_instLin, ← heτ _ hj, mul_comm (eτ _),
      mul_assoc, ← List.sum_map_mul_left]
    simp only [mul_assoc]; rfl
  unfold instClosed
  rw [← partition ι m σ one ins cb eσ Hσ _ hloc, rowsVal, instIRows, List.map_map, ttOf,
    sum_flatMap_map]
  simp only [Function.comp_def]
  rw [List.map_congr_left hrow, List.sum_map_mul_left]
  simp only [List.map_map, Function.comp_def]

/-! ## The slot: skeleton rows, then the instances -/

/-- A key's row base in a layout. -/
def _root_.FR.Circ.TLay.rb (L : TLay) (k : TKey) : ℕ :=
  match L.find? (·.1 == k) with
  | some (_, r, _, _) => r
  | none => 0

/-- Instance `t`'s indexed rows in a slot at row offset `off`. -/
def tinIRows (L : TLay) (one : Lin) (off : ℕ) (t : TKey × ℕ × List Lin) : List (ℕ × Row) :=
  instIRows (tplOf t.1) one t.2.2 (off + L.rb t.1 + t.2.1 * 2 ^ (tplOf t.1).rbits) (L.cb t.1 t.2.1)

/-- **A slot's indexed rows**: skeleton row `j` at `off + j`, then every instance's. -/
def slotIRows (L : TLay) (one : Lin) (off : ℕ) (cs : CS) : List (ℕ × Row) :=
  cs.rowList.zipIdx.map (fun p => (off + p.2, p.1)) ++ cs.tins.flatMap (tinIRows L one off)

theorem rowsVal_append (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (a b : List (ℕ × Row)) :
    rowsVal ι s n m τ σ (a ++ b) = rowsVal ι s n m τ σ a + rowsVal ι s n m τ σ b := by
  simp [rowsVal]

theorem rowsVal_flatMap {α : Type*} (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (l : List α)
    (f : α → List (ℕ × Row)) :
    rowsVal ι s n m τ σ (l.flatMap f) = (l.map fun a => rowsVal ι s n m τ σ (f a)).sum := by
  simp only [rowsVal, sum_flatMap_map]

/-! ## The implementation -/

/-- `eq(t, x)` over `n` coordinates by a list product (`eqNL_eq`). -/
@[specialize]
def eqNL (n : ℕ) (t : ℕ → R) (x : ℕ) : R :=
  ((List.range n).map fun l => if x.testBit l then t l else 1 - t l).prod

theorem eqNL_eq (n : ℕ) (t : ℕ → R) (x : ℕ) : eqNL n t x = eqN n t x := by
  unfold eqNL eqN
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

/-- `gN` by `eqNL`. -/
@[specialize]
def gNL (n : ℕ) (t : ℕ → R) (x : ℕ) : R := if x < 2 ^ n then eqNL n t x else 0

/-- The table `eq(t_lo, ·)` over the first `A` coordinates. -/
@[specialize]
def loTab (A : ℕ) (t : ℕ → R) : Array R := eqTable ((List.range A).map t)

theorem loTab_getD (A : ℕ) (t : ℕ → R) {j : ℕ} (hj : j < 2 ^ A) :
    (loTab A t).getD j 0 = eqN A t j := by
  have h := Impl.eqTable_getD ((List.range A).map t) (i := j) (by simpa using hj)
  rw [loTab, h, Impl.eqAtR, eqN, List.length_map, List.length_range, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [ptOf, List.getD_eq_getElem?_getD]

/-- **`eq(σ, ·)` by two tables** (`s` low coordinates, `m − s` high): one product per cell. -/
@[specialize]
def splitAt (lo hi : Array R) (p x : ℕ) : R := lo.getD (x % p) 0 * hi.getD (x / p) 0

/-- The two tables are built once (a closure over them). -/
@[specialize]
def splitE (m s : ℕ) (t : ℕ → R) : ℕ → R :=
  splitAt (loTab s t) (loTab (m - s) fun l => t (s + l)) (2 ^ s)

theorem splitE_eq {m s : ℕ} (hs : s ≤ m) (t : ℕ → R) : splitE m s t = gN m t := by
  funext x
  have hx : x = 2 ^ s * (x / 2 ^ s) + x % 2 ^ s := (Nat.div_add_mod x _).symm
  have hlt : x % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
  simp only [splitE, splitAt]
  rw [loTab_getD s t hlt]
  conv_rhs => rw [hx, gN_split hs _ _ hlt]
  congr 1
  unfold gN
  split_ifs with h
  · rw [loTab_getD _ _ h]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none]; · rfl
    simp [loTab, eqTable_size]; omega

/-- `Σ_{x ∈ l} f x` by a fold (no intermediate list). -/
@[specialize]
def sumL {α : Type*} (f : α → R) (l : List α) : R := l.foldl (fun a x => a + f x) 0

theorem sumL_eq {α : Type*} (f : α → R) (l : List α) : sumL f l = (l.map f).sum := by
  unfold sumL
  suffices ∀ a, l.foldl (fun a x => a + f x) a = a + (l.map f).sum by simpa using this 0
  induction l with
  | nil => simp
  | cons x l ih => intro a; simp [ih, add_assoc]

/-- `ι c · g x`, with no product when `c = 1`. -/
@[specialize]
def cmul (c : F) (g : R) : R := if c == 1 then g else ι c * g

theorem cmul_eq (c : F) (g : R) : cmul ι c g = ι c * g := by
  unfold cmul; split_ifs with h
  · rw [beq_iff_eq.1 h, map_one, one_mul]
  · rfl

/-- `linE` with an eq function. -/
@[specialize]
def linEI (g : ℕ → R) (l : Lin) : R := sumL (fun t => cmul ι t.2 (g t.1)) l

/-- The sparse value with eq functions (the skeleton's evaluation). -/
@[specialize]
def rowsValI (s : Mat) (gt gs : ℕ → R) (rows : List (ℕ × Row)) : R :=
  sumL (fun p => gt p.1 * linEI ι gs (s.r p.2)) rows

/-- **One key's precomputation** (once per evaluation, A.11's `O(|tpl|)`). -/
structure Prep (R : Type*) where
  A : ℕ
  B : ℕ
  loc : R
  one : R
  it : List (ℕ × R)

/-- `a[j]` (`0` past the end), as a function of `j` closing over the table. -/
@[specialize]
def getD0 (a : Array R) (j : ℕ) : R := a.getD j 0

@[specialize]
def prepOf (s : Mat) (τ σ : ℕ → R) (k : TKey) : Prep R :=
  let T := tplOf k
  let tt := ttOf ι s T (getD0 (loTab T.rbits τ))
  ⟨T.rbits, T.cbits, locSum (getD0 (loTab T.cbits σ)) tt, oneSum tt, inpList tt⟩

/-- An instance's value: the closed form when aligned, else its rows' sparse value. -/
@[specialize]
def instVal (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (gt gs : ℕ → R) (L : TLay) (one : Lin) (off : ℕ)
    (p : Prep R) (t : TKey × ℕ × List Lin) : R :=
  let A := p.A; let B := p.B
  let X := off + L.rb t.1 + t.2.1 * 2 ^ A
  let cb := L.cb t.1 t.2.1
  if A ≤ n ∧ B ≤ m ∧ X % 2 ^ A = 0 ∧ cb % 2 ^ B = 0 then
    gNL (n - A) (fun l => τ (A + l)) (X / 2 ^ A) *
      (gNL (m - B) (fun l => σ (B + l)) (cb / 2 ^ B) * p.loc + p.one * linEI ι gs one +
        sumL (fun q => q.2 * linEI ι gs (t.2.2.getD q.1 [])) p.it)
  else rowsValI ι s gt gs (tinIRows L one off t)

/-- The cache of `prepOf` over the keys present. -/
@[specialize]
def prepCache (s : Mat) (τ σ : ℕ → R) (ks : List TKey) : List (TKey × Prep R) :=
  ks.map fun k => (k, prepOf ι s τ σ k)

@[specialize]
def prepFind (s : Mat) (τ σ : ℕ → R) (c : List (TKey × Prep R)) (k : TKey) : Prep R :=
  match c.find? (·.1 == k) with
  | some p => p.2
  | none => prepOf ι s τ σ k

theorem prepFind_eq (s : Mat) (τ σ : ℕ → R) (ks : List TKey) (k : TKey) :
    prepFind ι s τ σ (prepCache ι s τ σ ks) k = prepOf ι s τ σ k := by
  unfold prepFind
  split
  · rename_i p hp
    have h1 := List.find?_some hp
    obtain ⟨k', -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hp)
    simp only [beq_iff_eq] at h1; rw [h1]
  · rfl

/-- **A slot's matrix value** (templated): the skeleton sparse, every instance in closed form. -/
@[specialize]
def slotVal (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (gt gs : ℕ → R) (L : TLay) (one : Lin) (off : ℕ)
    (cs : CS) : R :=
  let c := prepCache ι s τ σ ((keyCounts cs.tins).map (·.1))
  rowsValI ι s gt gs (cs.rowList.zipIdx.map fun p => (off + p.2, p.1)) +
    sumL (fun t => instVal ι s n m τ σ gt gs L one off (prepFind ι s τ σ c t.1) t) cs.tins

theorem linEI_eq (m : ℕ) (σ : ℕ → R) : linEI ι (gN m σ) = linE ι m σ := by
  funext l; simp only [linEI, linE, cmul_eq, sumL_eq]

theorem rowsValI_eq (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (rows : List (ℕ × Row)) :
    rowsValI ι s (gN n τ) (gN m σ) rows = rowsVal ι s n m τ σ rows := by
  simp only [rowsValI, rowsVal, linEI_eq, sumL_eq]

theorem heτ (k : TKey) {τ : ℕ → R} : ∀ j < (tplOf k).rows.length,
    getD0 (loTab (tplOf k).rbits τ) j = eqN (tplOf k).rbits τ j := by
  intro j hj; unfold getD0; exact loTab_getD (tplOf k).rbits τ (lt_rbits _ hj)

theorem heσ (k : TKey) {σ : ℕ → R} : ∀ j < 2 ^ (tplOf k).cbits,
    getD0 (loTab (tplOf k).cbits σ) j = eqN (tplOf k).cbits σ j := by
  intro j hj; unfold getD0; exact loTab_getD (tplOf k).cbits σ hj

theorem gNL_eq (n : ℕ) (t : ℕ → R) : gNL n t = gN n t := by
  funext x; simp [gNL, gN, eqNL_eq]

/-- **`slotVal_eq`**: the templated value is the sparse value of the slot's indexed rows. -/
theorem slotVal_eq (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (L : TLay) (one : Lin) (off : ℕ) (cs : CS) :
    slotVal ι s n m τ σ (gN n τ) (gN m σ) L one off cs = rowsVal ι s n m τ σ (slotIRows L one off cs) := by
  unfold slotVal slotIRows
  rw [rowsVal_append, rowsVal_flatMap, rowsValI_eq]
  simp only [sumL_eq]
  congr 2
  refine List.map_congr_left fun t _ => ?_
  rw [prepFind_eq]
  unfold instVal
  simp only []
  split_ifs with h
  · simp only [prepOf] at h ⊢
    obtain ⟨hA, hB, hX, hc⟩ := h
    obtain ⟨Xh, hXh⟩ := Nat.dvd_of_mod_eq_zero hX
    obtain ⟨Ch, hCh⟩ := Nat.dvd_of_mod_eq_zero hc
    unfold tinIRows
    rw [hXh, hCh, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
      tpl_mle ι s τ σ (tplOf t.1) one t.2.2 _ _ hA hB (getD0 (loTab (tplOf t.1).rbits τ))
        (getD0 (loTab (tplOf t.1).cbits σ)) (heτ t.1) (heσ t.1)]
    simp only [instClosed, gNL_eq, linEI_eq, sumL_eq]
  · exact rowsValI_eq ι s n m τ σ _

/-! ## Bridges to the sparse sums of `FRVIREval` (F) and `FRVerifierImpl` (K) -/

/-- The entries of indexed rows `(row, cell, coefficient)`. -/
def entriesI (s : Mat) (rows : List (ℕ × Row)) : Eval.Entries :=
  rows.flatMap fun p => (s.r p.2).map fun t => (p.1, t.1, t.2)

theorem eqAt_eqN (n : ℕ) (a : Array F) (x : ℕ) :
    Eval.eqAt (Eval.ptOf n a) x = eqN n (fun l => a.getD l 0) x := by
  rw [Eval.eqAt, eqN, ← Fin.prod_univ_eq_prod_range]; rfl

theorem rowsVal_sparse {R : Type*} [CommRing R] (ι : F →+* R) (s : Mat) (a b : ℕ) (τ σ : ℕ → R)
    (rows : List (ℕ × Row)) :
    rowsVal ι s a b τ σ rows = ((entriesI s rows).map fun e =>
      if e.1 < 2 ^ a ∧ e.2.1 < 2 ^ b then ι e.2.2 * eqN a τ e.1 * eqN b σ e.2.1 else 0).sum := by
  rw [entriesI, sum_flatMap_map, rowsVal]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [linE, ← List.sum_map_mul_left, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply, gN]
  by_cases h1 : p.1 < 2 ^ a <;> by_cases h2 : t.1 < 2 ^ b <;> simp [h1, h2] <;> ring

/-- **F**: the templated value is `FRVIREval.sparseEval` of the indexed rows' entries. -/
theorem rowsVal_F (s : Mat) (a b : ℕ) (τ σ : Array F) (rows : List (ℕ × Row)) :
    rowsVal (RingHom.id F) s a b (fun l => τ.getD l 0) (fun l => σ.getD l 0) rows =
      Eval.sparseEval (entriesI s rows) (Eval.ptOf a τ) (Eval.ptOf b σ) := by
  rw [rowsVal_sparse, Eval.sparseEval]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  simp only [eqAt_eqN, RingHom.id_apply]

theorem eqN_map {R : Type*} [CommRing R] (ι : F →+* R) (n : ℕ) (t : ℕ → F) (x : ℕ) :
    eqN n (fun l => ι (t l)) x = ι (eqN n t x) := by
  simp only [eqN, map_prod, apply_ite, map_sub, map_one]

/-- **K**: the templated value is S-F2's sparse sum over `K` (`sparseEvalK`'s body). -/
theorem rowsVal_K (s : Mat) (a b : ℕ) (τ : Array F) (σ : Array K) (rows : List (ℕ × Row)) :
    rowsVal K.ofFRingHom s a b (fun l => K.ofF (τ.getD l 0)) (fun l => σ.getD l 0) rows =
      ((entriesI s rows).map fun e => if e.1 < 2 ^ a ∧ e.2.1 < 2 ^ b then
        K.ofF (e.2.2 * Eval.eqAt (Eval.ptOf a τ) e.1) *
          Impl.eqAtR (fun l : Fin b => σ.getD l 0) e.2.1 else 0).sum := by
  rw [rowsVal_sparse]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  have h1 := eqN_map K.ofFRingHom a (fun l => τ.getD l 0) e.1
  have h2 : Impl.eqAtR (fun l : Fin b => σ.getD l 0) e.2.1 = eqN b (fun l => σ.getD l 0) e.2.1 := by
    rw [Impl.eqAtR, eqN, ← Fin.prod_univ_eq_prod_range]
  have h1' : eqN a (fun l => K.ofF (τ.getD l 0)) e.1 = K.ofF (eqN a (fun l => τ.getD l 0) e.1) := h1
  have hm : ∀ x y : F, K.ofF (x * y) = K.ofF x * K.ofF y := fun x y => map_mul K.ofFRingHom x y
  split_ifs
  · rw [eqAt_eqN, h2, h1', hm]; rfl
  · rfl

/-! ## The node -/

/-- Slot `σ`'s selector forms. -/
def slotP (σ : ℕ) : Params := muxP Layout.oneCell (Layout.selCells σ)

/-- Slot `σ`'s layout (the two-pass compile's first pass). -/
def slotLay (fin : Finals) (σ : ℕ) : TLay := layOf (slotP σ) (Layout.slotBase σ) (gen fin .mux).ops

/-- **Slot `σ`'s compiled program with the templates** (`compileT (gen fin .mux)`). -/
def slotCST (fin : Finals) (σ : ℕ) : CS :=
  compileT (slotLay fin σ) (slotP σ) (Layout.slotBase σ) (gen fin .mux).ops

/-- The node's plan: both slots' layouts and compiled programs (computed once). -/
structure Plan where
  lay : ℕ → TLay
  cs : ℕ → CS

def planOf (fin : Finals) : Plan :=
  let l0 := slotLay fin 0; let l1 := slotLay fin 1
  let c0 := compileT l0 (slotP 0) (Layout.slotBase 0) (gen fin .mux).ops
  let c1 := compileT l1 (slotP 1) (Layout.slotBase 1) (gen fin .mux).ops
  ⟨fun σ => if σ = 0 then l0 else l1, fun σ => if σ = 0 then c0 else c1⟩

/-- **The node's indexed M rows**: slot `σ`'s at offset `σ · 2^20`. -/
def nodeIRows (pl : Plan) : List (ℕ × Row) :=
  slotIRows (pl.lay 0) (Lin.cell Layout.oneCell) 0 (pl.cs 0) ++
    slotIRows (pl.lay 1) (Lin.cell Layout.oneCell) Layout.slotM (pl.cs 1)

/-- The node's value of matrix `s` (templated), over `R`. -/
@[specialize]
def nodeVal {R : Type*} [CommRing R] (ι : F →+* R) (s : Mat) (τ σ : ℕ → R) (pl : Plan) : R :=
  let gt := splitAt (loTab 11 τ) (loTab 10 fun l => τ (11 + l)) 2048
  let gs := splitAt (loTab 12 σ) (loTab 11 fun l => σ (12 + l)) 4096
  slotVal ι s 21 23 τ σ gt gs (pl.lay 0) (Lin.cell Layout.oneCell) 0 (pl.cs 0) +
    slotVal ι s 21 23 τ σ gt gs (pl.lay 1) (Lin.cell Layout.oneCell) Layout.slotM (pl.cs 1)

theorem nodeVal_eq {R : Type*} [CommRing R] (ι : F →+* R) (s : Mat) (τ σ : ℕ → R) (pl : Plan) :
    nodeVal ι s τ σ pl = rowsVal ι s 21 23 τ σ (nodeIRows pl) := by
  have h1 : splitAt (loTab 11 τ) (loTab 10 fun l => τ (11 + l)) 2048 = gN 21 τ :=
    splitE_eq (m := 21) (s := 11) (by norm_num) τ
  have h2 : splitAt (loTab 12 σ) (loTab 11 fun l => σ (12 + l)) 4096 = gN 23 σ :=
    splitE_eq (m := 23) (s := 12) (by norm_num) σ
  simp only [nodeVal, h1, h2, slotVal_eq, nodeIRows, rowsVal_append]

/-- **`evalM`, templated** (A.11): the node's three M matrices at `(τ, σ)`. -/
def evalMT (pl : Plan) (τ σ : Array F) : F × F × F :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  (nodeVal (RingHom.id F) .a t u pl, nodeVal (RingHom.id F) .b t u pl, nodeVal (RingHom.id F) .c t u pl)

/-- **`evalM`'s specification**: the MLEs of the node's M matrices (`FRVIREval.matMLE`). -/
noncomputable def evalMS (pl : Plan) (τ σ : Array F) : F × F × F :=
  (Eval.matMLE (entriesI .a (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
   Eval.matMLE (entriesI .b (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ),
   Eval.matMLE (entriesI .c (nodeIRows pl)) (Eval.ptOf 21 τ) (Eval.ptOf 23 σ))

/-- **`evalM_eq`** (A.11: the sum of the templates' `tpl_mle` and the skeleton's `sparse_eq`). -/
theorem evalMT_eq (pl : Plan) (τ σ : Array F) : evalMT pl τ σ = evalMS pl τ σ := by
  simp only [evalMT, evalMS, nodeVal_eq, rowsVal_F, Eval.sparse_eq]

/-- **`evalMK`, templated**: the M matrices at an F row point and a K column point. -/
def evalMKT (pl : Plan) (τ : Array F) (σ : Array K) : K × K × K :=
  let t := fun l => K.ofF (τ.getD l 0); let u := fun l => σ.getD l 0
  (nodeVal K.ofFRingHom .a t u pl, nodeVal K.ofFRingHom .b t u pl, nodeVal K.ofFRingHom .c t u pl)

/-- `evalMKT` is the sparse sum over `K` (`FRVerifierImpl.sparseEvalK`'s body). -/
theorem evalMKT_eq (pl : Plan) (τ : Array F) (σ : Array K) :
    evalMKT pl τ σ = (((entriesI .a (nodeIRows pl)).map fun e => if e.1 < 2 ^ 21 ∧ e.2.1 < 2 ^ 23 then
        K.ofF (e.2.2 * Eval.eqAt (Eval.ptOf 21 τ) e.1) *
          Impl.eqAtR (fun l : Fin 23 => σ.getD l 0) e.2.1 else 0).sum,
      ((entriesI .b (nodeIRows pl)).map fun e => if e.1 < 2 ^ 21 ∧ e.2.1 < 2 ^ 23 then
        K.ofF (e.2.2 * Eval.eqAt (Eval.ptOf 21 τ) e.1) *
          Impl.eqAtR (fun l : Fin 23 => σ.getD l 0) e.2.1 else 0).sum,
      ((entriesI .c (nodeIRows pl)).map fun e => if e.1 < 2 ^ 21 ∧ e.2.1 < 2 ^ 23 then
        K.ofF (e.2.2 * Eval.eqAt (Eval.ptOf 21 τ) e.1) *
          Impl.eqAtR (fun l : Fin 23 => σ.getD l 0) e.2.1 else 0).sum) := by
  simp only [evalMKT, nodeVal_eq, rowsVal_K]

end TEval
end FR
