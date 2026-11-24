-- New for lvm2 (roll 8 = B1, B1-K; B-DES §1.3–§1.4, B1-P1P2 §3): the kernels of `Φ_Q`'s executable evaluation and
-- the compiled evaluator's form. Ideas from B1-W's probe evaluator (v2/v3:
-- grouped one-bit factors, the carry automaton, level tables), re-cut so that every part has a closed semantic
-- statement (L-A proves them in wave L).
import LvmWiringKT
import LvmFieldCorrect

-- (GOLF2: 56 declarations that `certified` does not use moved verbatim to `LvmE2VWidthsFOff`, outside its import closure.)

/-!
# The kernels and the compiled evaluator

`Φ_Q(o, x, y)` at a point `pt = κ ++ r_x ++ r_y` (2 + 20 + 21 coordinates) is a sum over terms; a term is
`w · eq(κ, o) · Σ_{jf < 2^l} eq(r_x, x0 + jf) · eq(r_y, f(jf))`. The evaluator never visits an instance. It
computes, once per point:

* **tables** (`TRec`): `eq` tables over bit ranges of `r_x` and `r_y` (`eqTab`), `eq(κ, ·)` (4 entries), and the
  **kernel values** (`KF`): products of one-bit factors (K1: a paired bit `1 + r_x,i + r_y,j` in characteristic
  2, a fixed bit `eq(r_x,i, b)`), the successor polynomial of a shifted field (K2, `succVal`), the limb factor
  `Σ_{m<3} eq(r_y,{e,e+1}, m)·y^m` of a merged `E` cell (`limbVal`);
* **the atom sum** (`evalRuns`): an atom is a weight and one `(table, index)` key per level; the sum
  `Σ_a w_a · Π_λ T[key_λ(a)]` is evaluated on the atoms in array order, factoring each maximal run of equal keys
  (`evalRuns`), so a sorted array costs one product per distinct prefix;
* **carry-automaton passes** (K3, B-DES §1.4, `Pass`): `Σ_s v_s Σ_{j < 2^n} eq(r_x,A, j) · eq(r_y, s + R·j)`
  for initial states `s` whose values `v_s` are atom sums; the automaton reads `y`'s bits low to high with the
  carry as its state, in characteristic 2 at about 1.5 products per live state and step (`autoStep`).

Statements (wave X: stated; L-A proves them): `eqTab_get`, `kfVal_pair`, `succVal_eq`, `limbVal_eq`,
`evalRuns_eq`, `runAuto_eq`, `evalC_eq`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lvm.Typed.K

open Lvm.Loop

/-! ## The value ring (S2GT-W)

The executable evaluator below runs over `FE`. Its correctness proofs run over any **value ring** `𝔽`: a commutative
ring of characteristic two, with `E3`'s weights mapped in (`KRing.ofE`) where the weights enter. Each executable
function has a proof-side twin `…G` over `𝔽`; the executable ones are their `FE` instances (`evalC_eqG`). S2GT
evaluates `Φ_Q` at an `E2` point through the twins over `E3 ⊗ E2`. -/

/-- **The weights' map** of a value ring: `E3 → 𝔽`, a ring map. -/
class KRing (𝔽 : Type) [CommRing 𝔽] where
  /-- The weights' map. -/
  ofE : FE →+* 𝔽

instance : KRing FE := ⟨RingHom.id FE⟩

variable {𝔽 : Type} [CommRing 𝔽] [CharP 𝔽 2]

/-- `eq(r, x) = Π_i (x_i ? r_i : 1 - r_i)` over a value ring (the twin of `eqW`). -/
def eqWG : List 𝔽 → ℕ → 𝔽
  | [], _ => 1
  | r :: rs, x => (if x % 2 = 1 then r else 1 - r) * eqWG rs (x / 2)

/-! ## The point -/

/-- The point, split: `κ` (2), `r_x` (`xVars`), `r_y` (`yVars`). -/
structure Pt where
  /-- The selector coordinates. -/
  kap : Array FE
  /-- The slot coordinates. -/
  rx : Array FE
  /-- The word coordinates. -/
  ry : Array FE
  deriving Inhabited

/-- The proof-side twin of `Pt` over a value ring (S2GT-W). -/
structure PtG (𝔽 : Type) where
  /-- The selector coordinates. -/
  kap : Array 𝔽
  /-- The slot coordinates. -/
  rx : Array 𝔽
  /-- The word coordinates. -/
  ry : Array 𝔽
  deriving Inhabited

/-- The point of `Φ_Q`'s coordinates `o ++ x ++ y`. -/
def Pt.ofList (pt : List FE) : Pt :=
  ⟨(pt.take 2).toArray, ((pt.drop 2).take xVars).toArray, ((pt.drop (2 + xVars)).take yVars).toArray⟩

/-- The proof-side twin of `Pt.ofList` over a value ring (S2GT-W). -/
def PtG.ofList (pt : List 𝔽) : PtG 𝔽 :=
  ⟨(pt.take 2).toArray, ((pt.drop 2).take xVars).toArray, ((pt.drop (2 + xVars)).take yVars).toArray⟩

/-- One factor of `eq`: `r` at bit `1`, `1 − r` at bit `0`. -/
@[inline] def eq1 (r : FE) (b : Bool) : FE := if b then r else 1 - r

/-- The proof-side twin of `eq1` over a value ring (S2GT-W). -/
@[inline] def eq1G (r : 𝔽) (b : Bool) : 𝔽 := if b then r else 1 - r

/-- `FK`'s product, inlined (B1-K2: `FK.mul`'s body, so that the hot loops pay no calls). -/
@[inline] def fkMulI (a b : FK) : FK :=
  let p := FK.clmul64 a.val b.val
  ⟨FK.reduce p.lo p.hi⟩

/-- `FE`'s product, inlined (`FE.mul`'s body over `fkMulI`): at a call site the product's cell is not
allocated when its value is consumed at once (≈ 150 ns against 173 [measured, micro-bench]). -/
@[inline] def mulI (x y : FE) : FE :=
  let m0 := fkMulI x.c₀ y.c₀
  let m1 := fkMulI x.c₁ y.c₁
  let m2 := fkMulI x.c₂ y.c₂
  let m01 := fkMulI (x.c₀ + x.c₁) (y.c₀ + y.c₁)
  let m02 := fkMulI (x.c₀ + x.c₂) (y.c₀ + y.c₂)
  let m12 := fkMulI (x.c₁ + x.c₂) (y.c₁ + y.c₂)
  ⟨m0 + m12 + m1 + m2, m01 + m0 + m12, m02 + m0 + m1⟩

/-- **The inlined product is the product.** -/
theorem mulI_eq (x y : FE) : mulI x y = x * y := rfl

/-- **The `eq` table over `r[lo, lo + n)`**: entry `v` is `Π_{k<n} eq1 r[lo+k] (bit k of v)`; built by
doubling from the top bit (one product per entry). -/
def eqTab (r : Array FE) (lo n : ℕ) : Array FE := Id.run do
  let mut t : Array FE := #[1]
  for i in [0:n] do
    let a := r.getD (lo + n - 1 - i) 0
    let mut nt : Array FE := Array.mkEmpty (2 * t.size)
    for v in t do
      let hi := mulI v a
      nt := nt.push (v - hi)
      nt := nt.push hi
    t := nt
  return t

/-- The proof-side twin of `eqTab` over a value ring (S2GT-W). -/
def eqTabG (r : Array 𝔽) (lo n : ℕ) : Array 𝔽 := Id.run do
  let mut t : Array 𝔽 := #[1]
  for i in [0:n] do
    let a := r.getD (lo + n - 1 - i) 0
    let mut nt : Array 𝔽 := Array.mkEmpty (2 * t.size)
    for v in t do
      let hi := v * a
      nt := nt.push (v - hi)
      nt := nt.push hi
    t := nt
  return t

/-- **The `eq` table over the coordinates `r[bits]`** (any bit list): entry `v` is
`Π_k eq1 r[bits[k]] (bit k of v)`. -/
def eqTabB (r : Array FE) (bits : List ℕ) : Array FE := Id.run do
  let ba := bits.toArray
  let n := ba.size
  let mut t : Array FE := #[1]
  for i in [0:n] do
    let a := r.getD (ba.getD (n - 1 - i) 0) 0
    let mut nt : Array FE := Array.mkEmpty (2 * t.size)
    for v in t do
      let hi := mulI v a
      nt := nt.push (v - hi)
      nt := nt.push hi
    t := nt
  return t

/-- The proof-side twin of `eqTabB` over a value ring (S2GT-W). -/
def eqTabBG (r : Array 𝔽) (bits : List ℕ) : Array 𝔽 := Id.run do
  let ba := bits.toArray
  let n := ba.size
  let mut t : Array 𝔽 := #[1]
  for i in [0:n] do
    let a := r.getD (ba.getD (n - 1 - i) 0) 0
    let mut nt : Array 𝔽 := Array.mkEmpty (2 * t.size)
    for v in t do
      let hi := v * a
      nt := nt.push (v - hi)
      nt := nt.push hi
    t := nt
  return t

/-- The bits `bits` of `v` from position `k` on, packed. -/
def pextGo (v : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | k, b :: bs => (if v.testBit b then 1 <<< k else 0) + pextGo v (k + 1) bs

/-- The bits `bits` of `v`, packed (`pext`). -/
def pext (v : ℕ) (bits : List ℕ) : ℕ := pextGo v 0 bits

/-- A table represents `eqW L`: the right size and the right entries. -/
def tab_Rep (t : Array 𝔽) (L : List 𝔽) : Prop :=
  t.size = 2 ^ L.length ∧ ∀ x < 2 ^ L.length, t.getD x 0 = eqWG L x

/-- One doubling step, as the loops elaborate it. -/
def tab_dbl (t : Array 𝔽) (a : 𝔽) : Array 𝔽 :=
  Array.foldl (fun b v => (b.push (v - v * a)).push (v * a)) (Array.mkEmpty (2 * t.size)) t

theorem tab_dbl_list (l : List 𝔽) (a : 𝔽) :
    (l.foldl (fun b v => (b.push (v - v * a)).push (v * a)) (#[] : Array 𝔽)).size = 2 * l.length ∧
    ∀ x < 2 * l.length, (l.foldl (fun b v => (b.push (v - v * a)).push (v * a)) (#[] : Array 𝔽)).getD x 0 =
      (if x % 2 = 1 then a else 1 - a) * l.getD (x / 2) 0 := by
  induction l using List.reverseRecOn with
  | nil => simp only [List.foldl_nil, List.size_toArray, List.length_nil, mul_zero, not_lt_zero, Array.getD_eq_getD_getElem?, not_false_eq_true, getElem?_neg, Option.getD_none, List.getD_eq_getElem?_getD, implies_true, and_self]
  | append_singleton l v ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, Array.size_push, ih1, List.length_append,
      List.length_singleton]
    refine ⟨by ring, fun x hx => ?_⟩
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_push, ih1] at ih2 ⊢
    by_cases h1 : x < 2 * l.length
    · have := ih2 x h1
      simp only [show ¬ x = 2 * l.length + 1 from by (clear * - h1; omega), show ¬ x = 2 * l.length from by (clear * - h1; omega), ↓reduceIte, this]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by (clear * - h1; omega) : x / 2 < l.length)]
    · by_cases h2 : x = 2 * l.length
      · subst h2
        simp only [show ¬ 2 * l.length = 2 * l.length + 1 from by (clear * -; (clear * - 𝔽 l; omega)), ↓reduceIte]
        have : 2 * l.length / 2 = l.length := Nat.mul_div_right _ (by decide)
        simp only [Option.getD_some, Nat.mul_mod_right, zero_ne_one, ↓reduceIte, this, List.getD_eq_getElem?_getD, List.length_append, List.length_cons, List.length_nil, zero_add, lt_add_iff_pos_right, Order.lt_one_iff, getElem?_pos, Std.le_refl, List.getElem_append_right, tsub_self, List.getElem_cons_zero]
        ring
      · have h3 : x = 2 * l.length + 1 := by (clear * - hx h1 h2; omega)
        subst h3
        have : (2 * l.length + 1) / 2 = l.length := by
          rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt (by decide : 1 < 2), Nat.zero_add]
        simp only [Nat.add_left_cancel_iff, ↓reduceIte, Option.getD_some, Nat.mul_add_mod_self_left, Nat.mod_succ, this, List.getD_eq_getElem?_getD, List.length_append, List.length_cons, List.length_nil, zero_add, lt_add_iff_pos_right, Order.lt_one_iff, getElem?_pos, Std.le_refl, List.getElem_append_right, tsub_self, List.getElem_cons_zero]
        ring

theorem tab_dbl_rep (t : Array 𝔽) (L : List 𝔽) (a : 𝔽) (h : tab_Rep t L) : tab_Rep (tab_dbl t a) (a :: L) := by
  obtain ⟨h1, h2⟩ := h
  have e : tab_dbl t a = t.toList.foldl (fun b v => (b.push (v - v * a)).push (v * a)) (#[] : Array 𝔽) := by
    simp only [tab_dbl, Array.mkEmpty_eq, Array.foldl_toList]
  obtain ⟨d1, d2⟩ := tab_dbl_list t.toList a
  simp only [Array.length_toList] at d1 d2
  rw [e]
  refine ⟨by rw [d1, h1, List.length_cons, pow_succ]; ring, fun x hx => ?_⟩
  have hx' : x < 2 * t.size := by rw [h1]; simp only [List.length_cons, pow_succ] at hx; (clear * - hx; omega)
  rw [d2 x hx', eqWG, List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?,
    h2 _ (by simp only [List.length_cons, pow_succ] at hx; (clear * - h1 hx'; omega))]

theorem tab_loop_rep (g : ℕ → 𝔽) (k : ℕ) :
    tab_Rep ((List.range' 0 k).foldl (fun t i ↦ tab_dbl t (g i)) #[1]) ((List.range k).map g).reverse := by
  induction k with
  | zero => exact ⟨by simp only [List.range'_zero, List.foldl_nil, List.size_toArray, List.length_cons, List.length_nil, zero_add, List.range_zero, List.map_nil, List.reverse_nil, pow_zero], fun x hx => by simp only [List.range_zero, List.map_nil, List.reverse_nil, List.length_nil, pow_zero, Order.lt_one_iff] at hx; subst hx; simp only [List.range'_zero, List.foldl_nil, Array.getD_eq_getD_getElem?, List.size_toArray, List.length_cons, List.length_nil, zero_add, Order.lt_one_iff, getElem?_pos, List.getElem_toArray, List.getElem_cons_zero, Option.getD_some, List.range_zero, List.map_nil, List.reverse_nil, eqWG]⟩
  | succ k ih =>
    rw [List.range'_1_concat, List.foldl_append, List.range_succ]
    simpa only [zero_add, List.foldl_cons, List.foldl_nil, List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] using tab_dbl_rep _ _ (g k) ih

theorem tab_eqTab_eq (r : Array 𝔽) (lo n : ℕ) :
    eqTabG r lo n = (List.range' 0 n).foldl (fun t i ↦ tab_dbl t (r.getD (lo + n - 1 - i) 0)) #[1] := by
  unfold eqTabG
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Array.forIn_pure_yield_eq_foldl,
    List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  rfl

theorem tab_eqTabB_eq (r : Array 𝔽) (bits : List ℕ) :
    eqTabBG r bits = (List.range' 0 bits.length).foldl
      (fun t i ↦ tab_dbl t (r.getD (bits.toArray.getD (bits.length - 1 - i) 0) 0)) #[1] := by
  unfold eqTabBG
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Array.forIn_pure_yield_eq_foldl,
    List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, List.size_toArray]
  rfl

theorem tab_rev_range (n : ℕ) (g : ℕ → 𝔽) (c : ℕ → 𝔽) (h : ∀ j < n, g (n - 1 - j) = c j) :
    ((List.range n).map g).reverse = (List.range n).map c := by
  apply List.ext_getElem (by simp only [List.length_reverse, List.length_map, List.length_range])
  intro j h1 h2
  simp only [List.length_reverse, List.length_map, List.length_range] at h1
  simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
  exact h j h1

/-- **The bit-list table is `eqW`** at the packed bits (statement). Owner L-A. -/
theorem eqTabB_get (r : Array 𝔽) (bits : List ℕ) (v : ℕ) (hv : v < 2 ^ bits.length) :
    (eqTabBG r bits).getD v 0 = eqWG (bits.map fun b ↦ r.getD b 0) v := by
  have h := tab_loop_rep (fun i ↦ r.getD (bits.toArray.getD (bits.length - 1 - i) 0) 0) bits.length
  have e : bits.map (fun b ↦ r.getD b 0) = (List.range bits.length).map fun j ↦ r.getD (bits.getD j 0) 0 := by
    apply List.ext_getElem (by simp only [Array.getD_eq_getD_getElem?, List.length_map, List.getD_eq_getElem?_getD, List.length_range])
    intro j h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1 : j < bits.length)]
  rw [tab_rev_range _ _ (fun j ↦ r.getD (bits.getD j 0) 0) (fun j hj ↦ by
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
    rw [show bits.length - 1 - (bits.length - 1 - j) = j by (clear * - hj; omega)])] at h
  rw [tab_eqTabB_eq, e]
  exact h.2 v (by simpa only [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, List.length_map, List.length_range] using hv)

/-- The coordinates `r[lo, lo + n)` as a list. -/
def sub (r : Array 𝔽) (lo n : ℕ) : List 𝔽 := (List.range n).map fun k ↦ r.getD (lo + k) 0

/-- **The `eq` table is `eqW`** on the range. Owner L-A. -/
theorem eqTab_get (r : Array 𝔽) (lo n v : ℕ) (hv : v < 2 ^ n) :
    (eqTabG r lo n).getD v 0 = eqWG (sub r lo n) v := by
  have h := tab_loop_rep (fun i ↦ r.getD (lo + n - 1 - i) 0) n
  rw [tab_rev_range n _ (fun k ↦ r.getD (lo + k) 0) (fun j hj ↦ congrArg (fun i ↦ r.getD i 0) (by clear * - hj; omega))] at h
  rw [tab_eqTab_eq]
  exact h.2 v (by simpa only [Array.getD_eq_getD_getElem?, List.length_map, List.length_range] using hv)

/-! ## Kernel factors -/

/-- **A kernel factor** (its `x` bits are summed over, its `y` bits are read): -/
inductive KF where
  /-- K1, a paired bit: `Σ_b eq(r_x,i, b)·eq(r_y,j, b)`. -/
  | pair (i j : ℕ)
  /-- A fixed iteration bit: `eq(r_x,i, b)`. -/
  | fixX (i : ℕ) (b : Bool)
  /-- K2, the successor polynomial of an iteration field: `Σ_{v < 2^n − 1} eq(r_x,xs, v + 1)·eq(r_y,ys, v)`. -/
  | succ (xs ys : List ℕ)
  /-- A merged `E` cell's limbs: `Σ_{m<3} eq(r_y,{e,e+1}, m)·y^m`. -/
  | limb (e : ℕ)
  /-- A geometric `y` bit (a run of words `y + z·2^q` with weights `c^z`): `Σ_b eq(r_y,j, b)·c^b`. -/
  | ypow (j : ℕ) (c : FK)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- The successor polynomial over `x` and `y` coordinates (low bit first): from the top bit,
`E_k = eq(x[k:], y[k:])` and `S_k = x_k·(1 − y_k)·E_{k+1} + (1 − x_k)·y_k·S_{k+1}` (`v + 1` at bit `k`: no carry
when `v_k = 0`, a carry when `v_k = 1`) (`LvmShift.shiftRec`, the
roles of `x` and `y` exchanged). -/
def succVal (xs ys : List FE) : FE := Id.run do
  let n := xs.length
  let xa := xs.toArray
  let ya := ys.toArray
  let mut e : FE := 1
  let mut s : FE := 0
  for i in [0:n] do
    let k := n - 1 - i
    let a := xa.getD k 0
    let b := ya.getD k 0
    let ab := a * b
    s := (a - ab) * e + (b - ab) * s
    e := (1 - a - b + ab + ab) * e
  return s

/-- The proof-side twin of `succVal` over a value ring (S2GT-W). -/
def succValG (xs ys : List 𝔽) : 𝔽 := Id.run do
  let n := xs.length
  let xa := xs.toArray
  let ya := ys.toArray
  let mut e : 𝔽 := 1
  let mut s : 𝔽 := 0
  for i in [0:n] do
    let k := n - 1 - i
    let a := xa.getD k 0
    let b := ya.getD k 0
    let ab := a * b
    s := (a - ab) * e + (b - ab) * s
    e := (1 - a - b + ab + ab) * e
  return s

/-- The `eq` sum `Σ_{v < 2^n} eq(xs, v)·eq(ys, v)` (helper for `succVal_eq`). -/
def succ_E (xs ys : List 𝔽) : 𝔽 :=
  ((List.range (2 ^ xs.length)).map fun v ↦ eqWG xs v * eqWG ys v).sum

/-- The successor sum `Σ_{v < 2^n - 1} eq(xs, v + 1)·eq(ys, v)` (helper for `succVal_eq`). -/
def succ_S (xs ys : List 𝔽) : 𝔽 :=
  ((List.range (2 ^ xs.length - 1)).map fun v ↦ eqWG xs (v + 1) * eqWG ys v).sum

/-- One step of `succVal`'s loop. -/
def succ_step (a b : 𝔽) (p : 𝔽 × 𝔽) : 𝔽 × 𝔽 :=
  ((1 - a - b + a * b + a * b) * p.1, (a - a * b) * p.1 + (b - a * b) * p.2)

theorem succ_eqW_even (r : 𝔽) (rs : List 𝔽) (w : ℕ) : eqWG (r :: rs) (2 * w) = (1 - r) * eqWG rs w := by
  have h1 : ¬ (2 * w % 2 = 1) := by rw [Nat.mul_mod_right]; decide
  rw [eqWG, show 2 * w / 2 = w from Nat.mul_div_right w (by decide)]
  simp only [h1, ↓reduceIte]

theorem succ_eqW_odd (r : 𝔽) (rs : List 𝔽) (w : ℕ) : eqWG (r :: rs) (2 * w + 1) = r * eqWG rs w := by
  have h1 : (2 * w + 1) % 2 = 1 := by rw [Nat.add_comm, Nat.add_mul_mod_self_left]
  rw [eqWG, show (2 * w + 1) / 2 = w by rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt (by decide : 1 < 2), Nat.zero_add]]
  simp only [h1, ↓reduceIte]

theorem succ_sum_two (f : ℕ → 𝔽) (M : ℕ) :
    ((List.range (2 * M)).map f).sum =
      ((List.range M).map fun w ↦ f (2 * w)).sum + ((List.range M).map fun w ↦ f (2 * w + 1)).sum := by
  induction M with
  | zero => simp only [mul_zero, List.range_zero, List.map_nil, List.sum_nil, add_zero]
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by (clear * -; ring1), List.range_succ, List.range_succ, List.range_succ]
    simp only [List.map_append, List.sum_append, ih, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    ring

theorem succ_sum_two_one (f : ℕ → 𝔽) (M : ℕ) :
    ((List.range (2 * M + 1)).map f).sum =
      ((List.range (M + 1)).map fun w ↦ f (2 * w)).sum + ((List.range M).map fun w ↦ f (2 * w + 1)).sum := by
  rw [List.range_succ, List.range_succ]
  simp only [List.map_append, List.sum_append, succ_sum_two, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  ring

theorem succ_E_nil : succ_E ([] : List 𝔽) [] = 1 := by
  simp only [succ_E, eqWG, mul_one, List.length_nil, pow_zero, List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem succ_S_nil : succ_S ([] : List 𝔽) [] = 0 := by
  simp only [succ_S, List.length_nil, pow_zero, tsub_self, List.range_zero, List.map_nil, List.sum_nil]

theorem succ_E_cons (x y : 𝔽) (xs ys : List 𝔽) :
    succ_E (x :: xs) (y :: ys) = (x * y + (1 - x) * (1 - y)) * succ_E xs ys := by
  unfold succ_E
  rw [List.length_cons, pow_succ, mul_comm, succ_sum_two]
  simp only [succ_eqW_even, succ_eqW_odd]
  rw [show (fun w ↦ (1 - x) * eqWG xs w * ((1 - y) * eqWG ys w)) =
      fun w ↦ ((1 - x) * (1 - y)) * (eqWG xs w * eqWG ys w) from funext fun w ↦ by ring,
    show (fun w ↦ x * eqWG xs w * (y * eqWG ys w)) =
      fun w ↦ (x * y) * (eqWG xs w * eqWG ys w) from funext fun w ↦ by ring,
    List.sum_map_mul_left, List.sum_map_mul_left]
  ring

theorem succ_S_cons (x y : 𝔽) (xs ys : List 𝔽) :
    succ_S (x :: xs) (y :: ys) = x * (1 - y) * succ_E xs ys + (1 - x) * y * succ_S xs ys := by
  unfold succ_S succ_E
  have h1 : 1 ≤ 2 ^ xs.length := Nat.one_le_two_pow
  rw [List.length_cons, show 2 ^ (xs.length + 1) - 1 = 2 * (2 ^ xs.length - 1) + 1 by
    rw [pow_succ]; (clear * - 𝔽 xs h1; omega), succ_sum_two_one, show 2 ^ xs.length - 1 + 1 = 2 ^ xs.length by (clear * - 𝔽 xs h1; omega)]
  simp only [succ_eqW_even, succ_eqW_odd, show ∀ w : ℕ, 2 * w + 1 + 1 = 2 * (w + 1) from fun w ↦ by (clear * -; ring1)]
  rw [show (fun w ↦ x * eqWG xs w * ((1 - y) * eqWG ys w)) =
      fun w ↦ (x * (1 - y)) * (eqWG xs w * eqWG ys w) from funext fun w ↦ by ring,
    show (fun w ↦ (1 - x) * eqWG xs (w + 1) * (y * eqWG ys w)) =
      fun w ↦ ((1 - x) * y) * (eqWG xs (w + 1) * eqWG ys w) from funext fun w ↦ by ring,
    List.sum_map_mul_left, List.sum_map_mul_left]

theorem succ_fold (xs ys : List 𝔽) (h : xs.length = ys.length) (i : ℕ) (hi : i ≤ xs.length) :
    List.foldl (fun (p : 𝔽 × 𝔽) (j : ℕ) ↦
        succ_step (xs.toArray.getD (xs.length - 1 - j) 0) (ys.toArray.getD (xs.length - 1 - j) 0) p)
      (1, 0) (List.range i) =
      (succ_E (xs.drop (xs.length - i)) (ys.drop (xs.length - i)),
        succ_S (xs.drop (xs.length - i)) (ys.drop (xs.length - i))) := by
  induction i with
  | zero =>
    rw [List.range_zero, List.foldl_nil, Nat.sub_zero, List.drop_length, h, List.drop_length, succ_E_nil,
      succ_S_nil]
  | succ i ih =>
    rw [List.range_succ, List.foldl_append, ih (by (clear * - h hi; omega)), List.foldl_cons, List.foldl_nil]
    have hk : xs.length - 1 - i < xs.length := by (clear * - h hi; omega)
    have hk' : xs.length - 1 - i < ys.length := by (clear * - h hk; omega)
    rw [show xs.length - (i + 1) = xs.length - 1 - i by (clear * - h hi; omega), List.drop_eq_getElem_cons hk,
      List.drop_eq_getElem_cons hk', show xs.length - 1 - i + 1 = xs.length - i by (clear * - h hi; omega),
      succ_E_cons, succ_S_cons]
    have ha : xs.toArray.getD (xs.length - 1 - i) 0 = xs[xs.length - 1 - i] := by simp only [Array.getD, List.size_toArray, hk, ↓reduceDIte, Array.getInternal_eq_getElem, List.getElem_toArray]
    have hb : ys.toArray.getD (xs.length - 1 - i) 0 = ys[xs.length - 1 - i] := by simp only [Array.getD, List.size_toArray, hk', ↓reduceDIte, Array.getInternal_eq_getElem, List.getElem_toArray]
    rw [ha, hb, succ_step]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> ring

/-- **The successor polynomial** (statement). Owner L-A. -/
theorem succVal_eq (xs ys : List 𝔽) (h : xs.length = ys.length) :
    succValG xs ys = ((List.range (2 ^ xs.length - 1)).map fun v ↦ eqWG xs (v + 1) * eqWG ys v).sum := by
  simp only [succValG, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, pure_bind]
  rw [show (xs.length - 0 + 1 - 1) / 1 = xs.length by (clear * - 𝔽 xs ys h; omega), ← List.range_eq_range']
  have hf := congrArg Prod.snd (succ_fold xs ys h xs.length le_rfl)
  simp only [Nat.sub_self, List.drop_zero] at hf
  exact hf

/-- The limb factor `Σ_{m<3} eq((a, b), m)·y^m`. -/
def limbVal (a b : FE) : FE :=
  let ab := a * b
  (1 - a - b + ab) + (a - ab) * FE.y + (b - ab) * (FE.y * FE.y)

section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- The proof-side twin of `limbVal` over a value ring (S2GT-W). -/
def limbValG (a b : 𝔽) : 𝔽 :=
  let ab := a * b
  (1 - a - b + ab) + (a - ab) * KRing.ofE FE.y + (b - ab) * (KRing.ofE FE.y * KRing.ofE FE.y)

/-- **A factor's value** at the point. -/
def kfVal (P : Pt) : KF → FE
  | .pair i j => 1 - P.rx.getD i 0 - P.ry.getD j 0
  | .fixX i b => eq1 (P.rx.getD i 0) b
  | .succ xs ys => succVal (xs.map fun i ↦ P.rx.getD i 0) (ys.map fun j ↦ P.ry.getD j 0)
  | .limb e => limbVal (P.ry.getD e 0) (P.ry.getD (e + 1) 0)
  | .ypow j c => let r := P.ry.getD j 0; (1 - r) + FE.smulBase c r

/-- The proof-side twin of `kfVal` over a value ring (S2GT-W). -/
def kfValG (P : PtG 𝔽) : KF → 𝔽
  | .pair i j => 1 - P.rx.getD i 0 - P.ry.getD j 0
  | .fixX i b => eq1G (P.rx.getD i 0) b
  | .succ xs ys => succValG (xs.map fun i ↦ P.rx.getD i 0) (ys.map fun j ↦ P.ry.getD j 0)
  | .limb e => limbValG (P.ry.getD e 0) (P.ry.getD (e + 1) 0)
  | .ypow j c => let r := P.ry.getD j 0; (1 - r) + KRing.ofE (FE.ofK c) * r

/-- A kernel's value: the product of its factors. -/
def kerVal (P : Pt) (fs : List KF) : FE := fs.foldl (fun acc f ↦ acc * kfVal P f) 1

/-- The proof-side twin of `kerVal` over a value ring (S2GT-W). -/
def kerValG (P : PtG 𝔽) (fs : List KF) : 𝔽 := fs.foldl (fun acc f ↦ acc * kfValG P f) 1

end L1

/-! ## Tables -/

/-- **A table recipe**, computed once per point. -/
inductive TRec where
  /-- The constant table `[1]` (a trivial level). -/
  | one
  /-- `eq` over `r_x[bits]`. -/
  | eqx (bits : List ℕ)
  /-- `eq` over `r_y[bits]`. -/
  | eqy (bits : List ℕ)
  /-- `κ`'s selector masks: entry `m < 16` is `Σ_{o ∈ m} eq(κ, o)` (an atom of several matrices at once). -/
  | kap
  /-- Kernel values. -/
  | ker (ks : Array (List KF))
  /-- Products of entries of the other (non-`prod`) tables: entry `i` is `Π_{k ∈ rows[i]} T[k]` (the memoised
  `x` and `y` keys). -/
  | prod (rows : Array (List (ℕ × ℕ)))
  deriving Inhabited

/-- `y·a` (`y³ = y + 1`): `c₂ + (c₀ + c₂)·y + c₁·y²`, one base-field addition. -/
@[inline] def mulY (a : FE) : FE := ⟨a.c₂, a.c₀ + a.c₂, a.c₁⟩

/-- `a·b`, cheaply when `b` is `c·y^m` (`c ∈ K`, `m < 3`: a weight `ofK k` or a limb's `y^m`): three
base-field products and `m` shifts. -/
@[inline] def fmul (a b : FE) : FE :=
  if b.c₁ == 0 && b.c₂ == 0 then FE.smulBase b.c₀ a
  else if b.c₀ == 0 && b.c₂ == 0 then mulY (FE.smulBase b.c₁ a)
  else if b.c₀ == 0 && b.c₁ == 0 then mulY (mulY (FE.smulBase b.c₂ a))
  else a * b

/-- The selector masks' table. -/
def kapTab (κ : Array FE) : Array FE :=
  let e := eqTab κ 0 2
  (Array.range 16).map fun m ↦ (List.range 4).foldl (fun acc o ↦ if m.testBit o then acc + e.getD o 0 else acc) 0

/-- The proof-side twin of `kapTab` over a value ring (S2GT-W). -/
def kapTabG (κ : Array 𝔽) : Array 𝔽 :=
  let e := eqTabG κ 0 2
  (Array.range 16).map fun m ↦ (List.range 4).foldl (fun acc o ↦ if m.testBit o then acc + e.getD o 0 else acc) 0

/-- A table's entries at the point (`prod` tables are filled by `tabsAt`). -/
def TRec.eval (P : Pt) : TRec → Array FE
  | .one => #[1]
  | .eqx bits => eqTabB P.rx bits
  | .eqy bits => eqTabB P.ry bits
  | .kap => kapTab P.kap
  | .ker ks => ks.map (kerVal P)
  | .prod _ => #[]

/-- The proof-side twin of `TRec.eval` over a value ring (S2GT-W). -/
def TRec.evalG [KRing 𝔽] (P : PtG 𝔽) : TRec → Array 𝔽
  | .one => #[1]
  | .eqx bits => eqTabBG P.rx bits
  | .eqy bits => eqTabBG P.ry bits
  | .kap => kapTabG P.kap
  | .ker ks => ks.map (kerValG P)
  | .prod _ => #[]

/-- The value of key `k` in the tables. -/
@[inline] def keyVal (T : Array (Array FE)) (k : ℕ × ℕ) : FE := (T.getD k.1 #[]).getD k.2 0

/-- The proof-side twin of `keyVal` over a value ring (S2GT-W). -/
@[inline] def keyValG (T : Array (Array 𝔽)) (k : ℕ × ℕ) : 𝔽 := (T.getD k.1 #[]).getD k.2 0

/-- A product of keys (one key: no product). -/
def prodKeys (T : Array (Array FE)) : List (ℕ × ℕ) → FE
  | [] => 1
  | k :: ks => ks.foldl (fun acc k' ↦ acc * keyVal T k') (keyVal T k)

/-- The proof-side twin of `prodKeys` over a value ring (S2GT-W). -/
def prodKeysG (T : Array (Array 𝔽)) : List (ℕ × ℕ) → 𝔽
  | [] => 1
  | k :: ks => ks.foldl (fun acc k' ↦ acc * keyValG T k') (keyValG T k)

/-- **The level tables** of `r[lo, lo + n)`: `levels[k]` is the `eq` table over `r[lo + k, lo + n)` (one doubling
pass from the top bit builds all of them; one product per entry of the last). -/
def eqLevels (r : Array FE) (lo n : ℕ) : Array (Array FE) := Id.run do
  let mut t : Array FE := #[1]
  let mut lv : Array (Array FE) := #[t]
  for i in [0:n] do
    let a := r.getD (lo + n - 1 - i) 0
    let mut nt : Array FE := Array.mkEmpty (2 * t.size)
    for v in t do
      let hi := mulI v a
      nt := nt.push (v - hi)
      nt := nt.push hi
    t := nt
    lv := lv.push t
  return lv.reverse

/-- The proof-side twin of `eqLevels` over a value ring (S2GT-W). -/
def eqLevelsG (r : Array 𝔽) (lo n : ℕ) : Array (Array 𝔽) := Id.run do
  let mut t : Array 𝔽 := #[1]
  let mut lv : Array (Array 𝔽) := #[t]
  for i in [0:n] do
    let a := r.getD (lo + n - 1 - i) 0
    let mut nt : Array 𝔽 := Array.mkEmpty (2 * t.size)
    for v in t do
      let hi := v * a
      nt := nt.push (v - hi)
      nt := nt.push hi
    t := nt
    lv := lv.push t
  return lv.reverse

/-- **A sub-table by marginalisation** (no product): the `eq` table over the sorted `bits ⊆ [lo, lo + n)`, from the
level table starting at its first bit, the other bits summed out. Output `v` sums the source entries whose kept
bits spell `v` (both enumerated in increasing order by the subset successor `((x ||| ¬mask) + 1) &&& mask`), one
pass, the sums in place (B1-K2; `sumOut` once per missing bit copied every intermediate table). -/
def margTab (lv : Array (Array FE)) (lo n : ℕ) (bits : List ℕ) : Array FE := Id.run do
  match bits.head? with
  | none => return #[1]
  | some b0 =>
    let k := b0 - lo
    let t := lv.getD k #[]
    let kept := bits.foldl (fun acc b ↦ acc ||| 2 ^ (b - lo - k)) 0
    let miss := (2 ^ (n - k) - 1) ^^^ kept
    let nIn := 2 ^ (n - k - bits.length)
    let mut out : Array FE := Array.mkEmpty (2 ^ bits.length)
    let mut x := 0
    for _ in [0:2 ^ bits.length] do
      let mut acc : FE := 0
      let mut m := 0
      for _ in [0:nIn] do
        acc := acc + t.getD (x ||| m) 0
        m := ((m ||| kept) + 1) &&& miss
      out := out.push acc
      x := ((x ||| miss) + 1) &&& kept
    return out

/-- The proof-side twin of `margTab` over a value ring (S2GT-W). -/
def margTabG (lv : Array (Array 𝔽)) (lo n : ℕ) (bits : List ℕ) : Array 𝔽 := Id.run do
  match bits.head? with
  | none => return #[1]
  | some b0 =>
    let k := b0 - lo
    let t := lv.getD k #[]
    let kept := bits.foldl (fun acc b ↦ acc ||| 2 ^ (b - lo - k)) 0
    let miss := (2 ^ (n - k) - 1) ^^^ kept
    let nIn := 2 ^ (n - k - bits.length)
    let mut out : Array 𝔽 := Array.mkEmpty (2 ^ bits.length)
    let mut x := 0
    for _ in [0:2 ^ bits.length] do
      let mut acc : 𝔽 := 0
      let mut m := 0
      for _ in [0:nIn] do
        acc := acc + t.getD (x ||| m) 0
        m := ((m ||| kept) + 1) &&& miss
      out := out.push acc
      x := ((x ||| miss) + 1) &&& kept
    return out

/-- A group's sub-table: a level table, else by marginalisation or by doubling, whichever is cheaper (a product
costs about twenty marginalisation reads, B1-K2). `bits` is sorted, distinct and inside the group (the compiler's
groups: `rangeKeys`, `mkPass`), as `margTab` needs. -/
def subTab (r : Array FE) (lv : Array (Array FE)) (lo n : ℕ) (bits : List ℕ) : Array FE :=
  match bits.head? with
  | none => #[1]
  | some b0 =>
    let k := b0 - lo
    if bits == (List.range (n - k)).map (b0 + ·) then lv.getD k #[]
    else if 20 * 2 ^ bits.length ≤ 2 ^ (n - k) then eqTabB r bits
    else margTab lv lo n bits

/-- The proof-side twin of `subTab` over a value ring (S2GT-W). -/
def subTabG (r : Array 𝔽) (lv : Array (Array 𝔽)) (lo n : ℕ) (bits : List ℕ) : Array 𝔽 :=
  match bits.head? with
  | none => #[1]
  | some b0 =>
    let k := b0 - lo
    if bits == (List.range (n - k)).map (b0 + ·) then lv.getD k #[]
    else if 20 * 2 ^ bits.length ≤ 2 ^ (n - k) then eqTabBG r bits
    else margTabG lv lo n bits

theorem tab_eqLevels_eq (r : Array 𝔽) (lo n : ℕ) :
    eqLevelsG r lo n = ((List.range' 0 n).foldl (fun s i ↦ (tab_dbl s.1 (r.getD (lo + n - 1 - i) 0),
      s.2.push (tab_dbl s.1 (r.getD (lo + n - 1 - i) 0)))) ((#[1] : Array 𝔽), #[#[1]])).2.reverse := by
  unfold eqLevelsG
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Array.forIn_pure_yield_eq_foldl,
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  rfl

theorem tab_lv_loop (g : ℕ → 𝔽) (k : ℕ) :
    (List.range' 0 k).foldl (fun s i ↦ (tab_dbl s.1 (g i), s.2.push (tab_dbl s.1 (g i))))
      ((#[1] : Array 𝔽), #[#[1]]) =
    ((List.range' 0 k).foldl (fun t i ↦ tab_dbl t (g i)) #[1],
      ((List.range (k + 1)).map fun j ↦ (List.range' 0 j).foldl (fun t i ↦ tab_dbl t (g i)) #[1]).toArray) := by
  induction k with
  | zero => simp only [List.range'_zero, List.foldl_nil, zero_add, List.range_one, List.map_cons, List.map_nil]
  | succ k ih =>
    rw [List.range'_1_concat, List.foldl_append, ih, List.range_succ (n := k + 1), List.map_append]
    simp only [zero_add, List.foldl_cons, List.push_toArray, List.foldl_nil, List.foldl_append, List.map_cons, List.range'_1_concat, List.map_nil]

theorem tab_eqLevels_rep (r : Array 𝔽) (lo n k : ℕ) (hk : k ≤ n) :
    tab_Rep ((eqLevelsG r lo n).getD k #[]) (sub r (lo + k) (n - k)) := by
  rw [tab_eqLevels_eq, tab_lv_loop]
  have e : ((((List.range (n + 1)).map fun j ↦ (List.range' 0 j).foldl
      (fun t i ↦ tab_dbl t (r.getD (lo + n - 1 - i) 0)) #[1]).toArray).reverse).getD k #[] =
      (List.range' 0 (n - k)).foldl (fun t i ↦ tab_dbl t (r.getD (lo + n - 1 - i) 0)) #[1] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_reverse (by simp only [Array.getD_eq_getD_getElem?, List.size_toArray, List.length_map, List.length_range, Order.lt_add_one_iff]; (clear * - hk; omega))]
    simp only [List.size_toArray, List.length_map, List.length_range, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range (by (clear * - n k hk; omega) : n + 1 - 1 - k < n + 1), Option.map_some, Option.getD_some]
    congr 2
  rw [e]
  have h := tab_loop_rep (fun i ↦ r.getD (lo + n - 1 - i) 0) (n - k)
  rwa [tab_rev_range _ _ (fun j ↦ r.getD (lo + k + j) 0) (fun j hj ↦ congrArg (fun i ↦ r.getD i 0) (by clear * - hk hj; omega))] at h

theorem tab_eqW_append (a b : List 𝔽) (u v : ℕ) (hu : u < 2 ^ a.length) :
    eqWG (a ++ b) (u + 2 ^ a.length * v) = eqWG a u * eqWG b v := by
  induction a generalizing u with
  | nil => simp only [List.length_nil, pow_zero, Order.lt_one_iff] at hu; subst hu; simp only [List.nil_append, List.length_nil, pow_zero, one_mul, zero_add, eqWG]
  | cons x a ih =>
    simp only [List.cons_append, eqWG, List.length_cons]
    have e : u + 2 ^ (a.length + 1) * v = u + 2 * (2 ^ a.length * v) := by rw [pow_succ]; ring
    have h1 : (u + 2 * (2 ^ a.length * v)) % 2 = u % 2 := Nat.add_mul_mod_self_left _ _ _
    have h2 : (u + 2 * (2 ^ a.length * v)) / 2 = u / 2 + 2 ^ a.length * v := Nat.add_mul_div_left _ _ (by decide)
    rw [e, h1, h2, ih (u / 2) (by rw [List.length_cons, pow_succ] at hu; (clear * - hu h1; omega))]
    ring

theorem tab_bits_filter (bits : List ℕ) (b0 N : ℕ) (hs : bits.Pairwise (· < ·))
    (hb : ∀ b ∈ bits, b0 ≤ b ∧ b < b0 + N) :
    ((List.range N).filter (fun i ↦ bits.contains (b0 + i))).map (b0 + ·) = bits := by
  have hp : (((List.range N).filter (fun i ↦ bits.contains (b0 + i))).map (b0 + ·)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range.filter _).imp (fun h ↦ by (clear * - h; omega))
  apply List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 ↦ by (clear * - h1 h2; omega)) hp hs
  apply (List.perm_ext_iff_of_nodup (hp.imp (fun h ↦ ne_of_lt h)) (hs.imp (fun h ↦ ne_of_lt h))).2
  intro x
  simp only [List.mem_map, List.mem_filter, List.mem_range, List.contains_iff_mem]
  constructor
  · rintro ⟨i, ⟨_, hi⟩, rfl⟩; exact hi
  · intro hx
    have := hb x hx
    exact ⟨x - b0, ⟨by (clear * - this; omega), by rwa [show b0 + (x - b0) = x by (clear * - this; omega)]⟩, by (clear * - this; omega)⟩

/-- A bit pattern (bit `i` = entry `i`), as a number. -/
def marg_val : List Bool → ℕ
  | [] => 0
  | b :: ms => b.toNat + 2 * marg_val ms

/-- Deposit the bits of `v` (low to high) into the set positions of a bit pattern. -/
def marg_dep : List Bool → ℕ → ℕ
  | [], _ => 0
  | true :: ms, v => v % 2 + 2 * marg_dep ms (v / 2)
  | false :: ms, v => 0 + 2 * marg_dep ms v

/-- The entries of `L` at the set positions of a bit pattern. -/
def marg_filt : List Bool → List 𝔽 → List 𝔽
  | true :: ms, a :: L => a :: marg_filt ms L
  | false :: ms, _ :: L => marg_filt ms L
  | _, _ => []

theorem marg_tb_zero (a x : ℕ) (ha : a ≤ 1) : (a + 2 * x).testBit 0 = decide (a = 1) := by
  rw [Nat.testBit_zero]; congr 1; apply propext; (clear * - a x ha; omega)

theorem marg_tb_succ (a x i : ℕ) (ha : a ≤ 1) : (a + 2 * x).testBit (i + 1) = x.testBit i := by
  rw [Nat.testBit_add_one]; congr 1; (clear * - a x ha; omega)

theorem marg_or2 (a b x y : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) :
    (a + 2 * x) ||| (b + 2 * y) = (a ||| b) + 2 * (x ||| y) := by
  have hab : a ||| b ≤ 1 := by interval_cases a <;> interval_cases b <;> decide
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_or, marg_tb_zero _ _ ha, marg_tb_zero _ _ hb, marg_tb_zero _ _ hab]
    interval_cases a <;> interval_cases b <;> decide
  | succ i => rw [Nat.testBit_or, marg_tb_succ _ _ _ ha, marg_tb_succ _ _ _ hb, marg_tb_succ _ _ _ hab, Nat.testBit_or]

theorem marg_and2 (a b x y : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) :
    (a + 2 * x) &&& (b + 2 * y) = (a &&& b) + 2 * (x &&& y) := by
  have hab : a &&& b ≤ 1 := by interval_cases a <;> interval_cases b <;> decide
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_and, marg_tb_zero _ _ ha, marg_tb_zero _ _ hb, marg_tb_zero _ _ hab]
    interval_cases a <;> interval_cases b <;> decide
  | succ i => rw [Nat.testBit_and, marg_tb_succ _ _ _ ha, marg_tb_succ _ _ _ hb, marg_tb_succ _ _ _ hab, Nat.testBit_and]

theorem marg_dep_and (ms : List Bool) (w : ℕ) :
    (marg_dep ms w ||| marg_val (ms.map not)) &&& marg_val ms = marg_dep ms w := by
  induction ms generalizing w with
  | nil => simp only [marg_dep, List.map_nil, marg_val, Nat.or_self, Nat.and_self]
  | cons b ms ih =>
    cases b
    · simp only [marg_dep, marg_val, List.map_cons, Bool.not_false, Bool.toNat_true, Bool.toNat_false]
      rw [marg_or2 _ _ _ _ (by (clear * -; decide)) (by (clear * -; decide)), marg_and2 _ _ _ _ (by simp only [Nat.zero_or, Std.le_refl]) (by (clear * -; decide)), ih]
      simp only [Nat.zero_or, Nat.and_zero, zero_add]
    · simp only [marg_dep, marg_val, List.map_cons, Bool.not_true, Bool.toNat_true, Bool.toNat_false]
      rw [marg_or2 _ _ _ _ (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))) (by decide), marg_and2 _ _ _ _ (by simp only [Nat.or_zero]; exact (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))) (by decide), ih]
      simp only [Nat.or_zero, Nat.and_one_is_mod, dvd_refl, Nat.mod_mod_of_dvd, Nat.add_left_cancel_iff]

theorem marg_succ (ms : List Bool) (v : ℕ) (hv : v + 1 < 2 ^ ms.count true) :
    ((marg_dep ms v ||| marg_val (ms.map not)) + 1) &&& marg_val ms = marg_dep ms (v + 1) := by
  induction ms generalizing v with
  | nil => simp only [List.nodup_nil, List.count_nil, pow_zero, Order.lt_one_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false] at hv
  | cons b ms ih =>
    cases b
    · simp only [List.count_cons, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hv
      simp only [marg_dep, marg_val, List.map_cons, Bool.not_false, Bool.toNat_true, Bool.toNat_false]
      rw [marg_or2 _ _ _ _ (by (clear * -; decide)) (by (clear * -; decide)), Nat.zero_or,
        show 1 + 2 * (marg_dep ms v ||| marg_val (ms.map not)) + 1 =
          0 + 2 * ((marg_dep ms v ||| marg_val (ms.map not)) + 1) by ring,
        marg_and2 _ _ _ _ (by (clear * -; decide)) (by (clear * -; decide)), ih _ hv]
      simp only [Nat.and_self, zero_add]
    · simp only [List.count_cons, BEq.rfl, ↓reduceIte] at hv
      simp only [marg_dep, marg_val, List.map_cons, Bool.not_true, Bool.toNat_true, Bool.toNat_false]
      rw [marg_or2 _ _ _ _ (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))) (by decide), Nat.or_zero]
      rcases Nat.mod_two_eq_zero_or_one v with h | h
      · rw [h, show 0 + 2 * (marg_dep ms (v / 2) ||| marg_val (ms.map not)) + 1 =
          1 + 2 * (marg_dep ms (v / 2) ||| marg_val (ms.map not)) by ring,
          marg_and2 _ _ _ _ (by (clear * -; decide)) (by (clear * -; decide)), marg_dep_and,
          show (v + 1) % 2 = 1 by rw [Nat.add_mod, h], show (v + 1) / 2 = v / 2 by (clear * - h; omega)]
        rfl
      · rw [h, show 1 + 2 * (marg_dep ms (v / 2) ||| marg_val (ms.map not)) + 1 =
          0 + 2 * ((marg_dep ms (v / 2) ||| marg_val (ms.map not)) + 1) by ring,
          marg_and2 _ _ _ _ (by (clear * -; decide)) (by (clear * -; decide)), ih _ (by rw [pow_succ] at hv; (clear * - hv h; omega)),
          show (v + 1) % 2 = 0 by rw [Nat.add_mod, h], show (v + 1) / 2 = v / 2 + 1 by (clear * - h; omega)]
        rfl

theorem marg_dep_lt (ms : List Bool) (v : ℕ) : marg_dep ms v < 2 ^ ms.length := by
  induction ms generalizing v with
  | nil => simp only [marg_dep, List.length_nil, pow_zero, Order.lt_one_iff]
  | cons b ms ih =>
    have := ih (v / 2); have := ih v
    cases b <;> simp only [marg_dep, List.length_cons, pow_succ] <;> omega

theorem marg_sum_two (f : ℕ → 𝔽) (N : ℕ) :
    ∑ u ∈ Finset.range (2 * N), f u = ∑ w ∈ Finset.range N, (f (2 * w) + f (2 * w + 1)) := by
  induction N with
  | zero => simp only [mul_zero, Finset.range_zero, Finset.sum_empty]
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

theorem marg_sum (ms : List Bool) (L : List 𝔽) (hl : L.length = ms.length) (v : ℕ) :
    ∑ u ∈ Finset.range (2 ^ (ms.map not).count true),
      eqWG L (marg_dep ms v ||| marg_dep (ms.map not) u) = eqWG (marg_filt ms L) v := by
  induction ms generalizing L v with
  | nil =>
    cases L with
    | nil => simp only [List.map_nil, List.nodup_nil, List.count_nil, pow_zero, Finset.range_one, eqWG, Finset.sum_const, Finset.card_singleton, one_smul, marg_filt]
    | cons _ _ => simp only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at hl
  | cons b ms ih =>
    cases L with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at hl
    | cons a L =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      cases b
      · simp only [List.map_cons, Bool.not_false, List.count_cons, BEq.rfl, ↓reduceIte, marg_filt]
        rw [pow_succ, mul_comm, marg_sum_two, ← ih L hl v]
        apply Finset.sum_congr rfl
        intro w _
        simp only [marg_dep]
        rw [marg_or2 _ _ _ _ (by decide) (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))), marg_or2 _ _ _ _ (by decide) (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))]
        simp only [eqWG, Nat.zero_or, Nat.mul_mod_right, Nat.mul_div_right _ (by (clear * -; decide) : 0 < 2),
          show (2 * w + 1) % 2 = 1 by rw [Nat.add_comm, Nat.add_mul_mod_self_left], show (2 * w + 1) / 2 = w by rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt (by decide : 1 < 2), Nat.zero_add]]
        rw [show (1 + 2 * (marg_dep ms v ||| marg_dep (ms.map not) w)) % 2 = 1 from Nat.add_mul_mod_self_left 1 2 _,
          show (1 + 2 * (marg_dep ms v ||| marg_dep (ms.map not) w)) / 2 =
            marg_dep ms v ||| marg_dep (ms.map not) w by
            rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt (by decide : 1 < 2), Nat.zero_add],
          show (0 + 2 * (marg_dep ms v ||| marg_dep (ms.map not) w)) % 2 = 0 from Nat.add_mul_mod_self_left 0 2 _,
          show (0 + 2 * (marg_dep ms v ||| marg_dep (ms.map not) w)) / 2 =
            marg_dep ms v ||| marg_dep (ms.map not) w by rw [Nat.zero_add, Nat.mul_div_right _ (by decide : 0 < 2)]]
        simp only [show (0 : ℕ) ≠ 1 by (clear * -; decide), ↓reduceIte]
        ring
      · simp only [List.map_cons, Bool.not_true, List.count_cons, beq_iff_eq, Bool.false_eq_true,
          ↓reduceIte, Nat.add_zero, marg_filt]
        rw [eqWG, ← ih L hl (v / 2), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        simp only [marg_dep]
        rw [marg_or2 _ _ _ _ (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))) (by decide), Nat.or_zero, eqWG,
          show (v % 2 + 2 * (marg_dep ms (v / 2) ||| marg_dep (ms.map not) u)) % 2 = v % 2 by
            rw [Nat.add_mul_mod_self_left, Nat.mod_mod],
          show (v % 2 + 2 * (marg_dep ms (v / 2) ||| marg_dep (ms.map not) u)) / 2 =
            marg_dep ms (v / 2) ||| marg_dep (ms.map not) u by
            rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt (Nat.mod_lt _ (by decide)), Nat.zero_add]]

theorem marg_inner (F : ℕ → 𝔽) (sx d : ℕ → ℕ) (M : ℕ) (h : ∀ u, u + 1 < M → sx (d u) = d (u + 1))
    (N s j : ℕ) (a : 𝔽) (hN : j + N ≤ M) :
    ((List.range' s N).foldl (fun b _ ↦ (b.1 + F b.2, sx b.2)) (a, d j)).1 =
      a + ∑ u ∈ Finset.range N, F (d (j + u)) := by
  induction N generalizing s j a with
  | zero => simp only [List.range'_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ N ih =>
    rw [List.range'_succ, List.foldl_cons]
    cases N with
    | zero => simp only [List.range'_zero, List.foldl_nil, zero_add, Finset.range_one, Finset.sum_singleton, add_zero]
    | succ N =>
      rw [h j (by (clear * - hN; omega)), ih (s + 1) (j + 1) _ (by (clear * - hN; omega)), Finset.sum_range_succ' _ (N + 1)]
      have e : ∀ u, j + 1 + u = j + (u + 1) := fun u ↦ by (clear * -; (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done))
      simp only [e, Nat.add_zero]
      ring

theorem marg_outer (G : ℕ → 𝔽) (sx d : ℕ → ℕ) (M : ℕ) (h : ∀ u, u + 1 < M → sx (d u) = d (u + 1))
    (N s j : ℕ) (arr : Array 𝔽) (hN : j + N ≤ M) :
    ((List.range' s N).foldl (fun b _ ↦ (b.1.push (G b.2), sx b.2)) (arr, d j)).1.toList =
      arr.toList ++ (List.range N).map fun u ↦ G (d (j + u)) := by
  induction N generalizing s j arr with
  | zero => simp only [List.range'_zero, List.foldl_nil, List.range_zero, List.map_nil, List.append_nil]
  | succ N ih =>
    rw [List.range'_succ, List.foldl_cons]
    cases N with
    | zero => simp only [List.range'_zero, List.foldl_nil, Array.toList_push, zero_add, List.range_one, List.map_cons, add_zero, List.map_nil]
    | succ N =>
      rw [h j (by (clear * - hN; omega)), ih (s + 1) (j + 1) _ (by (clear * - hN; omega))]
      simp only [Array.toList_push, List.append_assoc, List.singleton_append]
      rw [List.range_succ_eq_map (n := N + 1), List.map_cons, List.map_map, Nat.add_zero]
      congr 2
      apply List.map_congr_left
      intro u _
      simp only [Function.comp_apply, Nat.succ_eq_add_one]
      congr 2
      (clear * -; (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done))

theorem marg_tb_val (ms : List Bool) (i : ℕ) : (marg_val ms).testBit i = ms.getD i false := by
  induction ms generalizing i with
  | nil => simp only [marg_val, Nat.zero_testBit, List.getD_eq_getElem?_getD, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none]
  | cons b ms ih =>
    cases i with
    | zero => rw [marg_val, marg_tb_zero _ _ (by cases b <;> simp only [Bool.toNat_false, zero_le, Bool.toNat_true, Std.le_refl])]; cases b <;> simp only [Bool.toNat_false, zero_ne_one, decide_false, List.getD_eq_getElem?_getD, List.length_cons, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, getElem?_pos, List.getElem_cons_zero, Option.getD_some, Bool.toNat_true, decide_true]
    | succ i => rw [marg_val, marg_tb_succ _ _ _ (by cases b <;> simp only [Bool.toNat_false, zero_le, Bool.toNat_true, Std.le_refl]), ih]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]

theorem marg_tb_fold (l : List ℕ) (f : ℕ → ℕ) (a i : ℕ) :
    (l.foldl (fun acc b ↦ acc ||| 2 ^ f b) a).testBit i = (a.testBit i || l.any fun b ↦ decide (f b = i)) := by
  induction l generalizing a with
  | nil => simp only [List.foldl_nil, List.any_nil, Bool.or_false]
  | cons b l ih => rw [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_two_pow, List.any_cons, Bool.or_assoc]

theorem marg_val_compl (ms : List Bool) :
    (2 ^ ms.length - 1) ^^^ marg_val ms = marg_val (ms.map not) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, marg_tb_val, marg_tb_val]
  by_cases hi : i < ms.length
  · simp only [hi, decide_true, List.getD_eq_getElem?_getD, getElem?_pos, Option.getD_some, Bool.true_bne, List.length_map, List.getElem_map]
  · simp only [hi, decide_false, List.getD_eq_getElem?_getD, not_false_eq_true, getElem?_neg, Option.getD_none, bne_self_eq_false, List.length_map]

theorem marg_count_not (ms : List Bool) : (ms.map not).count true + ms.count true = ms.length := by
  induction ms with
  | nil => simp only [List.map_nil, List.nodup_nil, List.count_nil, add_zero, List.length_nil]
  | cons b ms ih => cases b <;> simp only [List.map_cons, Bool.not_false, List.count_cons_self, ne_eq, Bool.false_eq_true, not_false_eq_true, List.count_cons_of_ne, List.length_cons, Bool.not_true] <;> (clear * - ms ih; omega)

theorem marg_filt_map (l : List ℕ) (f : ℕ → Bool) (g : ℕ → 𝔽) :
    marg_filt (l.map f) (l.map g) = (l.filter f).map g := by
  induction l with
  | nil => simp only [List.map_nil, marg_filt, List.filter_nil]
  | cons x l ih => cases hf : f x <;> simp only [List.map_cons, hf, marg_filt, ih, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.filter_cons_of_pos]

theorem marg_dep_zero (ms : List Bool) : marg_dep ms 0 = 0 := by
  induction ms with
  | nil => rfl
  | cons b ms ih => cases b <;> simp only [marg_dep, ih, mul_zero, add_zero, Nat.zero_mod, Nat.zero_div]

theorem marg_filt_length (ms : List Bool) (L : List 𝔽) (hl : L.length = ms.length) :
    (marg_filt ms L).length = ms.count true := by
  induction ms generalizing L with
  | nil => cases L <;> simp_all only [List.length_nil, marg_filt, List.nodup_nil, List.count_nil, List.length_cons, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false]
  | cons b ms ih =>
    cases L with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false] at hl
    | cons a L => cases b <;> simp_all only [List.length_cons, Nat.add_right_cancel_iff, marg_filt, ne_eq, Bool.false_eq_true, not_false_eq_true, List.count_cons_of_ne, List.count_cons_self, Nat.add_left_cancel_iff]

theorem marg_body (t : Array 𝔽) (ms : List Bool) (L : List 𝔽) (hrep : tab_Rep t L)
    (hl : L.length = ms.length) (N M cap : ℕ) (hN : N = 2 ^ ms.count true)
    (hM : M = 2 ^ (ms.map not).count true) :
    tab_Rep ((List.range' 0 N).foldl (fun b _ ↦ (b.1.push ((List.range' 0 M).foldl
      (fun b' _ ↦ (b'.1 + t.getD (b.2 ||| b'.2) 0, ((b'.2 ||| marg_val ms) + 1) &&& marg_val (ms.map not)))
        ((0 : 𝔽), 0)).1, ((b.2 ||| marg_val (ms.map not)) + 1) &&& marg_val ms))
      (Array.mkEmpty cap, 0)).1 (marg_filt ms L) := by
  subst hN hM
  have hout := marg_outer (fun x ↦ ((List.range' 0 (2 ^ (ms.map not).count true)).foldl
      (fun b' _ ↦ (b'.1 + t.getD (x ||| b'.2) 0, ((b'.2 ||| marg_val ms) + 1) &&& marg_val (ms.map not)))
        ((0 : 𝔽), 0)).1) (fun x ↦ ((x ||| marg_val (ms.map not)) + 1) &&& marg_val ms) (marg_dep ms)
    (2 ^ ms.count true) (fun u hu ↦ marg_succ ms u hu) (2 ^ ms.count true) 0 0 (Array.mkEmpty cap) (by (clear * -; (clear * - ms; omega)))
  have he : (Array.mkEmpty cap : Array 𝔽).toList = [] := rfl
  rw [marg_dep_zero, he, List.nil_append] at hout
  have hfl := marg_filt_length ms L hl
  refine ⟨?_, fun v hv ↦ ?_⟩
  · rw [← Array.length_toList, hout, hfl]; simp only [zero_add, Array.getD_eq_getD_getElem?, List.length_map, List.length_range]
  · rw [hfl] at hv
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hout]
    simp only [List.getElem?_map, List.getElem?_range hv,
      Option.map_some, Option.getD_some, Nat.zero_add]
    have hin := marg_inner (fun m ↦ t.getD (marg_dep ms v ||| m) 0)
      (fun m ↦ ((m ||| marg_val ms) + 1) &&& marg_val (ms.map not)) (marg_dep (ms.map not))
      (2 ^ (ms.map not).count true)
      (fun u hu ↦ by simpa only [List.map_map, Function.comp_def, Bool.not_not, List.map_id_fun', id_eq] using marg_succ (ms.map not) u hu)
      (2 ^ (ms.map not).count true) 0 0 0 (by (clear * -; (clear * - ms; omega)))
    rw [marg_dep_zero] at hin
    rw [hin, zero_add, ← marg_sum ms L hl v]
    apply Finset.sum_congr rfl
    intro u _
    simp only [Nat.zero_add]
    apply hrep.2
    rw [hl]
    exact Nat.or_lt_two_pow (marg_dep_lt ms v) (by simpa only [List.length_map] using marg_dep_lt (ms.map not) u)

theorem marg_count_map (l : List ℕ) (f : ℕ → Bool) : (l.map f).count true = (l.filter f).length := by
  induction l with
  | nil => simp only [List.map_nil, List.nodup_nil, List.count_nil, List.filter_nil, List.length_nil]
  | cons x l ih => cases hf : f x <;> simp only [List.map_cons, hf, ne_eq, Bool.false_eq_true, not_false_eq_true, List.count_cons_of_ne, ih, List.filter_cons_of_neg, List.count_cons_self, List.filter_cons_of_pos, List.length_cons, Nat.add_left_cancel_iff]

theorem marg_kept (bits : List ℕ) (b0 c K : ℕ) (hc : c = b0) (hb : ∀ b ∈ bits, b0 ≤ b ∧ b < b0 + K) :
    bits.foldl (fun acc b ↦ acc ||| 2 ^ (b - c)) 0 =
      marg_val ((List.range K).map fun i ↦ bits.contains (b0 + i)) := by
  subst hc
  apply Nat.eq_of_testBit_eq
  intro i
  rw [marg_tb_fold, marg_tb_val, Nat.zero_testBit, Bool.false_or]
  by_cases hi : i < K
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.getD_some]
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, decide_eq_true_eq, List.contains_iff_mem]
    constructor
    · rintro ⟨b, hb', rfl⟩; rwa [show c + (b - c) = b by have := hb b hb'; (clear * - this; omega)]
    · intro h; exact ⟨c + i, h, by (clear * -; (clear * - c i; omega))⟩
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (by simpa only [List.length_range] using (by (clear * - hi; omega) : K ≤ i) : (List.range K).length ≤ i), Option.map_none,
      Option.getD_none]
    apply Bool.eq_false_iff.2
    simp only [ne_eq, List.any_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro b hb' he
    have := hb b hb'
    (clear * - hi he this; omega)

theorem tab_margTab_rep (r : Array 𝔽) (lo n b0 : ℕ) (bs : List ℕ) (hs : (b0 :: bs).Pairwise (· < ·))
    (hb : ∀ b ∈ b0 :: bs, lo ≤ b ∧ b < lo + n) :
    tab_Rep (margTabG (eqLevelsG r lo n) lo n (b0 :: bs)) ((b0 :: bs).map fun b ↦ r.getD b 0) := by
  have h0 := hb b0 List.mem_cons_self
  have hk : lo + (b0 - lo) = b0 := by (clear * - h0; omega)
  have hb' : ∀ b ∈ b0 :: bs, b0 ≤ b ∧ b < b0 + (n - (b0 - lo)) := fun b hb'' ↦ by
    have := hb b hb''
    refine ⟨?_, by (clear * - h0 hk this; omega)⟩
    rcases List.mem_cons.1 hb'' with rfl | hb'''
    · exact le_rfl
    · exact le_of_lt (List.rel_of_pairwise_cons hs hb''')
  have hbits := tab_bits_filter (b0 :: bs) b0 (n - (b0 - lo)) hs hb'
  have hrep := tab_eqLevels_rep r lo n (b0 - lo) (by (clear * - h0 hk; omega))
  rw [hk] at hrep
  have hkept := marg_kept (b0 :: bs) b0 (lo + (b0 - lo)) (n - (b0 - lo)) hk hb'
  set ms := (List.range (n - (b0 - lo))).map fun i ↦ (b0 :: bs).contains (b0 + i) with hms
  have hlen : ms.length = n - (b0 - lo) := by simp only [hms, List.contains_eq_mem, List.mem_cons, Nat.add_eq_left, Bool.decide_or, List.length_map, List.length_range]
  have hcnt : ms.count true = (b0 :: bs).length := by
    rw [hms, marg_count_map]
    conv_rhs => rw [← hbits]
    rw [List.length_map]
  have hmiss : (2 ^ (n - (b0 - lo)) - 1) ^^^ marg_val ms = marg_val (ms.map not) := by
    rw [← hlen]; exact marg_val_compl ms
  have hcn := marg_count_not ms
  have hL : sub r b0 (n - (b0 - lo)) = (List.range (n - (b0 - lo))).map fun j ↦ r.getD (b0 + j) 0 := rfl
  have hres : (b0 :: bs).map (fun b ↦ r.getD b 0) = marg_filt ms (sub r b0 (n - (b0 - lo))) := by
    rw [hL, hms, marg_filt_map]
    conv_lhs => rw [← hbits]
    rw [List.map_map]
    rfl
  unfold margTabG
  simp only [Id.run, List.head?_cons, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Nat.sub_sub]
  rw [hkept, hmiss, hres]
  exact marg_body _ ms _ hrep (by simp only [hL, Array.getD_eq_getD_getElem?, List.length_map, List.length_range, hlen]) _ _ _ (by rw [hcnt]) (by rw [Nat.sub_add_eq, ← hcnt, ← hlen]; congr 1; (clear * - hlen hcnt hcn; omega))

theorem tab_subTab_get (r : Array 𝔽) (lo n : ℕ) (bits : List ℕ) (hs : bits.Pairwise (· < ·))
    (hb : ∀ b ∈ bits, lo ≤ b ∧ b < lo + n) (v : ℕ) (hv : v < 2 ^ bits.length) :
    (subTabG r (eqLevelsG r lo n) lo n bits).getD v 0 = eqWG (bits.map fun b ↦ r.getD b 0) v := by
  cases bits with
  | nil => simp only [List.length_nil, pow_zero, Order.lt_one_iff] at hv; subst hv; simp only [subTabG, List.head?_nil, Array.getD_eq_getD_getElem?, List.size_toArray, List.length_cons, List.length_nil, zero_add, Order.lt_one_iff, getElem?_pos, List.getElem_toArray, List.getElem_cons_zero, Option.getD_some, List.map_nil, eqWG]
  | cons b0 bs =>
    have h0 := hb b0 List.mem_cons_self
    simp only [subTabG, List.head?_cons]
    split_ifs with h1 h2
    · have h1' := beq_iff_eq.1 h1
      have hlen : (b0 :: bs).length = n - (b0 - lo) := by rw [h1']; simp only [List.length_map, List.length_range]
      have hrep := tab_eqLevels_rep r lo n (b0 - lo) (by (clear * - h0; omega))
      have e : (b0 :: bs).map (fun b ↦ r.getD b 0) = sub r (lo + (b0 - lo)) (n - (b0 - lo)) := by
        rw [h1', List.map_map, show lo + (b0 - lo) = b0 by (clear * - h0; omega)]
        rfl
      rw [e]
      exact hrep.2 v (by simpa only [sub, Array.getD_eq_getD_getElem?, ← hlen, List.length_cons, List.length_map, List.length_range] using hv)
    · exact eqTabB_get r _ v hv
    · exact (tab_margTab_rep r lo n b0 bs hs hb).2 v (by simpa only [Array.getD_eq_getD_getElem?, List.map_cons, List.length_cons, List.length_map] using hv)

theorem tab_kapTab_get (κ : Array 𝔽) (m : ℕ) (hm : m < 16) :
    (kapTabG κ).getD m 0 = ((List.range 4).map fun o ↦ if m.testBit o then eqWG (sub κ 0 2) o else 0).sum := by
  simp only [kapTabG, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hm, ↓reduceIte,
    Option.map_some, Option.getD_some]
  have e : ∀ o < 4, (eqTabG κ 0 2)[o]?.getD 0 = eqWG (sub κ 0 2) o := fun o ho ↦ by
    rw [← Array.getD_eq_getD_getElem?]; exact eqTab_get κ 0 2 o (by simpa only [Nat.reducePow] using ho)
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, e 0 (by (clear * -; decide)), e 1 (by (clear * -; decide)), e 2 (by (clear * -; decide)), e 3 (by (clear * -; decide))]
  generalize m.testBit 0 = b0
  generalize m.testBit 1 = b1
  generalize m.testBit 2 = b2
  generalize m.testBit 3 = b3
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add, add_zero, add_assoc]

/-- The group of a bit list on a side of `N` bits cut at `cut`: `[0, cut)` or `[cut, N)`. -/
def groupOf (N cut : ℕ) (bits : List ℕ) : ℕ × ℕ := if bits.all (· < cut) then (0, cut) else (cut, N - cut)

/-- The tables at the point: the level tables of the four groups (`r_x` cut at 10, `r_y` at 11), every `eq`
table from its group's levels by marginalisation, the other tables, then the `prod` tables over them. -/
def tabsAt (P : Pt) (rs : Array TRec) : Array (Array FE) :=
  let lx0 := eqLevels P.rx 0 10
  let lx1 := eqLevels P.rx 10 (xVars - 10)
  let ly0 := eqLevels P.ry 0 11
  let ly1 := eqLevels P.ry 11 (yVars - 11)
  let T0 := rs.map fun r ↦ match r with
    | .eqx bits =>
      let (lo, n) := groupOf xVars 10 bits
      subTab P.rx (if lo == 0 then lx0 else lx1) lo n bits
    | .eqy bits =>
      let (lo, n) := groupOf yVars 11 bits
      subTab P.ry (if lo == 0 then ly0 else ly1) lo n bits
    | r => TRec.eval P r
  rs.mapIdx fun i r ↦ match r with
    | .prod rows => rows.map (prodKeys T0)
    | _ => T0.getD i #[]

section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- The proof-side twin of `tabsAt` over a value ring (S2GT-W). -/
def tabsAtG (P : PtG 𝔽) (rs : Array TRec) : Array (Array 𝔽) :=
  let lx0 := eqLevelsG P.rx 0 10
  let lx1 := eqLevelsG P.rx 10 (xVars - 10)
  let ly0 := eqLevelsG P.ry 0 11
  let ly1 := eqLevelsG P.ry 11 (yVars - 11)
  let T0 := rs.map fun r ↦ match r with
    | .eqx bits =>
      let (lo, n) := groupOf xVars 10 bits
      subTabG P.rx (if lo == 0 then lx0 else lx1) lo n bits
    | .eqy bits =>
      let (lo, n) := groupOf yVars 11 bits
      subTabG P.ry (if lo == 0 then ly0 else ly1) lo n bits
    | r => TRec.evalG P r
  rs.mapIdx fun i r ↦ match r with
    | .prod rows => rows.map (prodKeysG T0)
    | _ => T0.getD i #[]

theorem tab_tabsAt_one (P : PtG 𝔽) (rs : Array TRec) (i : ℕ) (hi : i < rs.size) (h : rs[i] = .one) :
    (tabsAtG P rs).getD i #[] = #[1] := by
  simp only [tabsAtG, beq_iff_eq, TRec.evalG, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_mapIdx, Array.getElem?_eq_getElem hi, h, Option.map_some, Option.getD_some]

theorem tab_tabsAt_kap (P : PtG 𝔽) (rs : Array TRec) (i : ℕ) (hi : i < rs.size) (h : rs[i] = .kap) :
    (tabsAtG P rs).getD i #[] = kapTabG P.kap := by
  simp only [tabsAtG, beq_iff_eq, TRec.evalG, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_mapIdx, Array.getElem?_eq_getElem hi, h, Option.map_some, Option.getD_some]

theorem tab_tabsAt_ker (P : PtG 𝔽) (rs : Array TRec) (i : ℕ) (hi : i < rs.size) (ks : Array (List KF))
    (h : rs[i] = .ker ks) :
    (tabsAtG P rs).getD i #[] = ks.map (kerValG P) := by
  simp only [tabsAtG, beq_iff_eq, TRec.evalG, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_mapIdx, Array.getElem?_eq_getElem hi, h, Option.map_some, Option.getD_some]

theorem tab_tabsAt_eqx (P : PtG 𝔽) (rs : Array TRec) (i : ℕ) (hi : i < rs.size) (bits : List ℕ) (h : rs[i] = .eqx bits)
    (hs : bits.Pairwise (· < ·)) (hg : (∀ b ∈ bits, b < 10) ∨ (∀ b ∈ bits, 10 ≤ b ∧ b < xVars))
    (v : ℕ) (hv : v < 2 ^ bits.length) :
    ((tabsAtG P rs).getD i #[]).getD v 0 = eqWG (bits.map fun b ↦ P.rx.getD b 0) v := by
  have e : (tabsAtG P rs).getD i #[] = (let (lo, n) := groupOf xVars 10 bits
      subTabG P.rx (if lo == 0 then eqLevelsG P.rx 0 10 else eqLevelsG P.rx 10 (xVars - 10)) lo n bits) := by
    simp only [tabsAtG, beq_iff_eq, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_mapIdx, Array.getElem?_eq_getElem hi, h, Option.map_some, Option.getD_some]
  rw [e]
  unfold groupOf
  by_cases hall : bits.all (· < 10) = true
  · simp only [hall, ↓reduceIte, beq_self_eq_true]
    apply tab_subTab_get _ _ _ _ hs _ v hv
    intro b hb
    have := List.all_eq_true.1 hall b hb
    simp only [decide_eq_true_eq] at this; (clear * - this; omega)
  · simp only [hall, Bool.false_eq_true, ↓reduceIte]
    simp only [show ((10 : ℕ) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    apply tab_subTab_get _ _ _ _ hs _ v hv
    rcases hg with hg | hg
    · exact absurd (List.all_eq_true.2 (fun b hb ↦ by simpa only [decide_eq_true_eq] using hg b hb)) hall
    · intro b hb; have := hg b hb; (clear * - this; omega)

theorem tab_tabsAt_eqy (P : PtG 𝔽) (rs : Array TRec) (i : ℕ) (hi : i < rs.size) (bits : List ℕ) (h : rs[i] = .eqy bits)
    (hs : bits.Pairwise (· < ·)) (hg : (∀ b ∈ bits, b < 11) ∨ (∀ b ∈ bits, 11 ≤ b ∧ b < yVars))
    (v : ℕ) (hv : v < 2 ^ bits.length) :
    ((tabsAtG P rs).getD i #[]).getD v 0 = eqWG (bits.map fun b ↦ P.ry.getD b 0) v := by
  have e : (tabsAtG P rs).getD i #[] = (let (lo, n) := groupOf yVars 11 bits
      subTabG P.ry (if lo == 0 then eqLevelsG P.ry 0 11 else eqLevelsG P.ry 11 (yVars - 11)) lo n bits) := by
    simp only [tabsAtG, beq_iff_eq, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_mapIdx, Array.getElem?_eq_getElem hi, h, Option.map_some, Option.getD_some]
  rw [e]
  unfold groupOf
  by_cases hall : bits.all (· < 11) = true
  · simp only [hall, ↓reduceIte, beq_self_eq_true]
    apply tab_subTab_get _ _ _ _ hs _ v hv
    intro b hb
    have := List.all_eq_true.1 hall b hb
    simp only [decide_eq_true_eq] at this; (clear * - this; omega)
  · simp only [hall, Bool.false_eq_true, ↓reduceIte]
    simp only [show ((11 : ℕ) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    apply tab_subTab_get _ _ _ _ hs _ v hv
    rcases hg with hg | hg
    · exact absurd (List.all_eq_true.2 (fun b hb ↦ by simpa only [decide_eq_true_eq] using hg b hb)) hall
    · intro b hb; have := hg b hb; (clear * - this; omega)

/-! ## The atom sum -/

/-- **An atom**: a weight and one key `(table, index)` per level (table `0` is the trivial one). -/
structure Atom where
  /-- The keys, one per level. -/
  keys : Array (ℕ × ℕ)
  /-- The weight. -/
  w : FE
  deriving Inhabited

/-- **An atom's value**: `w · Π_λ T[key_λ]`. -/
def atomVal (T : Array (Array 𝔽)) (a : Atom) : 𝔽 := a.keys.foldl (fun acc k ↦ acc * keyValG T k) (KRing.ofE a.w)

theorem runs_fmul (a b : FE) : fmul a b = a * b := by
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  unfold fmul
  split_ifs with h1 h2 h3
  · simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    show FE.smulBase _ _ = FE.mul _ _
    simp only [FE.smulBase, FE.mul, FE.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> (ring_nf; try simp only [CharTwo.two_eq_zero, mul_zero, add_zero])
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    show mulY (FE.smulBase _ _) = FE.mul _ _
    simp only [mulY, FE.smulBase, FE.mul, FE.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> (ring_nf; try simp only [CharTwo.two_eq_zero, mul_zero, add_zero])
  · simp only [Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    show mulY (mulY (FE.smulBase _ _)) = FE.mul _ _
    simp only [mulY, FE.smulBase, FE.mul, FE.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> (ring_nf; try simp only [CharTwo.two_eq_zero, mul_zero, add_zero])
  · rfl

/-- An atom's value from level `d` on. -/
def runs_valFrom (T : Array (Array 𝔽)) (d : ℕ) (a : Atom) : 𝔽 :=
  (a.keys.toList.drop d).foldl (fun acc k ↦ acc * keyValG T k) (KRing.ofE a.w)

theorem runs_foldl_mul (T : Array (Array 𝔽)) (l : List (ℕ × ℕ)) (c x : 𝔽) :
    l.foldl (fun acc k ↦ acc * keyValG T k) (c * x) = l.foldl (fun acc k ↦ acc * keyValG T k) c * x := by
  induction l generalizing c with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldl_cons]
    rw [mul_right_comm c x]
    exact ih _

theorem runs_getD_toList (a : Atom) (d : ℕ) (h : d < a.keys.toList.length) :
    a.keys.getD d (0, 0) = a.keys.toList[d] := by
  simp only [Array.length_toList] at h
  simp only [Array.getD_eq_getD_getElem?, h, getElem?_pos, Option.getD_some, Array.getElem_toList]

theorem runs_valFrom_succ (T : Array (Array 𝔽)) (d : ℕ) (a : Atom) (h : d < a.keys.size) :
    runs_valFrom T d a = keyValG T (a.keys.getD d (0, 0)) * runs_valFrom T (d + 1) a := by
  have h' : d < a.keys.toList.length := by simpa only [Array.length_toList] using h
  unfold runs_valFrom
  rw [List.drop_eq_getElem_cons h', List.foldl_cons, runs_foldl_mul, mul_comm, runs_getD_toList a d h']

theorem runs_getD_mem (as : Array Atom) (t : ℕ) (h : t < as.size) : as.getD t default ∈ as := by
  simp only [Array.getD_eq_getD_getElem?, h, getElem?_pos, Option.getD_some, Array.getElem_mem]

theorem runs_foldl_add (l : List ℕ) (g : ℕ → 𝔽) (c : 𝔽) :
    l.foldl (fun acc i ↦ acc + g i) c = c + (l.map g).sum := by
  induction l generalizing c with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons x l ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

/-! ## The atom sum as flat code -/

/-- **Flat code** of an atom sum (a post-order walk of the sorted atoms' key trie, built once): instruction `k`
is `op[k]`: `0` open a sum; `1` close it, multiplying by key `(ta, ix)` (none if `ta = 0`), into the enclosing
sum; `2` a leaf: key `(ta, ix)` times weight `ws[wi]` (`wi = 0`: no weight) into the enclosing sum; `3` close a
sum and emit it with state `ix` (a pass's initial state). -/
structure Code where
  /-- The operations. -/
  op : Array ℕ
  /-- Their tables. -/
  ta : Array ℕ
  /-- Their indices. -/
  ix : Array ℕ
  /-- Their weights' indices. -/
  wi : Array ℕ
  /-- The weights (`ws[0] = 1`). -/
  ws : Array FE
  deriving Inhabited

/-- The code under construction. -/
def Code.emit (c : Code) (o t i w : ℕ) : Code := ⟨c.op.push o, c.ta.push t, c.ix.push i, c.wi.push w, c.ws⟩

/-- **Run flat code**: the value of the outer sum, and the emitted `(state, sum)` pairs. -/
def runCode (T : Array (Array FE)) (c : Code) : FE × Array (ℕ × FE) := Id.run do
  -- `top`: the open sum; `st`: the enclosing ones
  let mut top : FE := 0
  let mut st : Array FE := #[]
  let mut em : Array (ℕ × FE) := #[]
  for k in [0:c.op.size] do
    let o := c.op.getD k 0
    if o == 2 then
      let v := (T.getD (c.ta.getD k 0) #[]).getD (c.ix.getD k 0) 0
      let w := c.wi.getD k 0
      top := top + (if w == 0 then v else fmul v (c.ws.getD w 1))
    else if o == 0 then
      st := st.push top
      top := 0
    else
      let s := top
      top := st.back?.getD 0
      st := st.pop
      if o == 3 then em := em.push (c.ix.getD k 0, s)
      else
        let t := c.ta.getD k 0
        top := top + (if t == 0 then s else
          let e := (T.getD t #[]).getD (c.ix.getD k 0) 0
          if s == 1 then e else fmul e s)
  return (top, em)

/-- The proof-side twin of `runCode` over a value ring (S2GT-W). -/
def runCodeG (T : Array (Array 𝔽)) (c : Code) : 𝔽 × Array (ℕ × 𝔽) := Id.run do
  -- `top`: the open sum; `st`: the enclosing ones
  let mut top : 𝔽 := 0
  let mut st : Array 𝔽 := #[]
  let mut em : Array (ℕ × 𝔽) := #[]
  for k in [0:c.op.size] do
    let o := c.op.getD k 0
    if o == 2 then
      let v := (T.getD (c.ta.getD k 0) #[]).getD (c.ix.getD k 0) 0
      let w := c.wi.getD k 0
      top := top + (if w == 0 then v else v * KRing.ofE (c.ws.getD w 1))
    else if o == 0 then
      st := st.push top
      top := 0
    else
      let s := top
      top := st.back?.getD 0
      st := st.pop
      if o == 3 then em := em.push (c.ix.getD k 0, s)
      else
        let t := c.ta.getD k 0
        top := top + (if t == 0 then s else
          let e := (T.getD t #[]).getD (c.ix.getD k 0) 0
          if s == 1 then e else e * s)
  return (top, em)

/-! ## Field facts -/

theorem code_mulY (a : FE) : mulY a = ⟨0, 1, 0⟩ * a := by
  apply FE.toExt3_injective
  rw [FE.toExt3_mul, FE.toExt3_eq, FE.toExt3_eq ⟨0, 1, 0⟩, FE.toExt3_eq a]
  simp only [mulY, FK.toBF64_add, FK.toBF64_zero, FK.toBF64_one, map_add, map_zero, map_one]
  linear_combination (-(algebraMap BF64 BF64.Ext3 (FK.toBF64 a.c₂))) * BF64.ext3Gen_pow_three

theorem code_beq_iff (a b : FE) : (a == b) = true ↔ a = b := by
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  change (a0 == b0 && a1 == b1 && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, FE.mk.injEq, and_assoc]

instance k_lawfulBEq_FE : LawfulBEq FE where
  eq_of_beq h := (code_beq_iff _ _).1 h
  rfl {a} := (code_beq_iff a a).2 rfl

theorem code_term (T : Array (Array 𝔽)) (k : ℕ × ℕ) (s : 𝔽) (hk : k.1 = 0 → keyValG T k = 1) :
    (if (k.1 == 0) = true then s else if (s == 1) = true then keyValG T k else keyValG T k * s) =
      keyValG T k * s := by
  split_ifs with h1 h2
  · rw [hk (by simpa only [beq_iff_eq] using h1), one_mul]
  · rw [beq_iff_eq.1 h2, mul_one]
  · rfl

/-! ## Loops -/

theorem code_forIn_list {α β : Type} (l : List α) (init : β) (B : α → β → Id (ForInStep β))
    (F : β → α → β) (hB : ∀ a b, B a b = pure (ForInStep.yield (F b a))) :
    forIn l init B = pure (l.foldl F init) := by
  have : B = fun a b ↦ pure (ForInStep.yield (F b a)) := funext fun a ↦ funext fun b ↦ hB a b
  subst this
  simp only [List.forIn_pure_yield_eq_foldl]

/-! ## Flat code as a list of instructions -/

/-- The four instruction arrays have one length. -/
def code_Al (c : Code) : Prop := c.ta.size = c.op.size ∧ c.ix.size = c.op.size ∧ c.wi.size = c.op.size

/-- The instructions `(op, ta, ix, wi)`. -/
def code_instrs (c : Code) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range c.op.size).map fun k ↦ (c.op.getD k 0, c.ta.getD k 0, c.ix.getD k 0, c.wi.getD k 0)

/-- One instruction of `runCode` (weights `W`). -/
def code_step (T : Array (Array 𝔽)) (W : Array FE) (s : 𝔽 × Array 𝔽 × Array (ℕ × 𝔽))
    (q : ℕ × ℕ × ℕ × ℕ) : 𝔽 × Array 𝔽 × Array (ℕ × 𝔽) :=
  if q.1 == 2 then
    (s.1 + if q.2.2.2 == 0 then (T.getD q.2.1 #[]).getD q.2.2.1 0
      else (T.getD q.2.1 #[]).getD q.2.2.1 0 * KRing.ofE (W.getD q.2.2.2 1), s.2.1, s.2.2)
  else if q.1 == 0 then (0, s.2.1.push s.1, s.2.2)
  else if q.1 == 3 then (s.2.1.back?.getD 0, s.2.1.pop, s.2.2.push (q.2.2.1, s.1))
  else
    (s.2.1.back?.getD 0 + if q.2.1 == 0 then s.1 else
      if s.1 == 1 then (T.getD q.2.1 #[]).getD q.2.2.1 0 else (T.getD q.2.1 #[]).getD q.2.2.1 0 * s.1,
      s.2.1.pop, s.2.2)

theorem code_runCode (T : Array (Array 𝔽)) (c : Code) :
    runCodeG T c = (((code_instrs c).foldl (code_step T c.ws) (0, #[], #[])).1,
      ((code_instrs c).foldl (code_step T c.ws) (0, #[], #[])).2.2) := by
  unfold runCodeG
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', code_forIn_list _ _ _
    (fun s k ↦ code_step T c.ws s (c.op.getD k 0, c.ta.getD k 0, c.ix.getD k 0, c.wi.getD k 0))
    (by
      intro k s
      simp only [code_step]
      by_cases h2 : (c.op.getD k 0 == 2) = true
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]
        by_cases h0 : (c.op.getD k 0 == 0) = true
        · rw [if_pos h0, if_pos h0]
        · rw [if_neg h0, if_neg h0]
          by_cases h3 : (c.op.getD k 0 == 3) = true
          · rw [if_pos h3, if_pos h3]
          · rw [if_neg h3, if_neg h3])]
  simp only [Array.getD_eq_getD_getElem?, Std.Legacy.Range.size, tsub_zero, add_tsub_cancel_right, Nat.div_one, bind_pure_comp, map_pure, code_instrs, List.range_eq_range', List.foldl_map]
  rfl

theorem code_emit (c : Code) (o t i w : ℕ) (hc : code_Al c) :
    code_Al (c.emit o t i w) ∧ code_instrs (c.emit o t i w) = code_instrs c ++ [(o, t, i, w)] ∧
      (c.emit o t i w).ws = c.ws := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨⟨by simp only [Code.emit, Array.size_push, h1, Nat.add_left_cancel_iff], by simp only [Code.emit, Array.size_push, h2, Nat.add_left_cancel_iff], by simp only [Code.emit, Array.size_push, h3, Nat.add_left_cancel_iff]⟩, ?_, rfl⟩
  simp only [code_instrs, Code.emit, Array.size_push, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro k hk
    have hk' : k < c.op.size := List.mem_range.1 hk
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hk'.ne, ↓reduceIte, h1, h2, h3]
  · have e : ∀ (a : Array ℕ) (x : ℕ), a.size = c.op.size → (a.push x).getD c.op.size 0 = x := by
      intro a x h; rw [← h]; simp only [Array.getD_eq_getD_getElem?, Array.size_push, lt_add_iff_pos_right, Order.lt_one_iff, getElem?_pos, Array.getElem_push_eq, Option.getD_some]
    rw [e _ _ h1, e _ _ h2, e _ _ h3, e c.op o rfl]

/-! ## Appended code blocks -/

/-- `c'` is `c` with a block appended that adds `E` to the open sum (weights may be appended too). -/
def code_Spec (T : Array (Array 𝔽)) (c c' : Code) (E : 𝔽) : Prop :=
  code_Al c' ∧ (∃ R, c'.ws = c.ws ++ R) ∧ ∃ L, code_instrs c' = code_instrs c ++ L ∧
    ∀ (R : Array FE) top st em, L.foldl (code_step T (c'.ws ++ R)) (top, st, em) = (top + E, st, em)

theorem code_Spec_zero (T : Array (Array 𝔽)) (c : Code) (hc : code_Al c) : code_Spec T c c 0 :=
  ⟨hc, ⟨#[], by simp only [Array.append_empty]⟩, [], by simp only [List.append_nil], by simp only [List.foldl_nil, add_zero, implies_true]⟩

theorem code_Spec_trans (T : Array (Array 𝔽)) (c c1 c2 : Code) (E1 E2 : 𝔽)
    (h1 : code_Spec T c c1 E1) (h2 : code_Spec T c1 c2 E2) : code_Spec T c c2 (E1 + E2) := by
  obtain ⟨-, ⟨R1, hR1⟩, L1, hL1, hf1⟩ := h1
  obtain ⟨hA, ⟨R2, hR2⟩, L2, hL2, hf2⟩ := h2
  refine ⟨hA, ⟨R1 ++ R2, by rw [hR2, hR1, Array.append_assoc]⟩, L1 ++ L2, by rw [hL2, hL1, List.append_assoc],
    fun R top st em ↦ ?_⟩
  rw [List.foldl_append]
  have : c2.ws ++ R = c1.ws ++ (R2 ++ R) := by rw [hR2, Array.append_assoc]
  rw [this, hf1, ← this, hf2, add_assoc]

/-- A leaf: key `k` times weight `w` (none if `w = 0`). -/
def code_leaf (c : Code) (k : ℕ × ℕ) (w : FE) : Code :=
  if !(w == 0) then
    if w == 1 then c.emit 2 k.1 k.2 0 else { c.emit 2 k.1 k.2 c.ws.size with ws := c.ws.push w }
  else c

theorem code_Spec_leaf (T : Array (Array 𝔽)) (c : Code) (k : ℕ × ℕ) (w : FE) (hc : code_Al c)
    (hw : 0 < c.ws.size) : code_Spec T c (code_leaf c k w) (keyValG T k * KRing.ofE w) := by
  obtain ⟨hA, hI, hW⟩ := code_emit c 2 k.1 k.2 0 hc
  obtain ⟨hA', hI', hW'⟩ := code_emit c 2 k.1 k.2 c.ws.size hc
  unfold code_leaf
  split_ifs with h0 h1
  · rw [(code_beq_iff _ _).1 h1, map_one, mul_one]
    refine ⟨hA, ⟨#[], by simp only [hW, Array.append_empty]⟩, _, hI, fun R top st em ↦ ?_⟩
    simp only [List.foldl_cons, code_step, BEq.rfl, ↓reduceIte, Array.getD_eq_getD_getElem?, List.foldl_nil, keyValG]
  · refine ⟨hA', ⟨#[w], Array.push_eq_append⟩, _, hI', fun R top st em ↦ ?_⟩
    have hne : (c.ws.size == 0) = false := beq_eq_false_iff_ne.2 (by (clear * - hw; omega))
    have hg : (c.ws.push w ++ R).getD c.ws.size 1 = w := by
      simp only [Array.getD_eq_getD_getElem?, Array.size_push, lt_add_iff_pos_right, Order.lt_one_iff, Array.getElem?_append_left, getElem?_pos, Array.getElem_push_eq, Option.getD_some]
    simp only [List.foldl_cons, List.foldl_nil, code_step, beq_self_eq_true, ite_true, hne,
      Bool.false_eq_true, ite_false, hg]
    rfl
  · have : w = 0 := by simpa only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq, Decidable.not_not] using h0
    rw [this, map_zero, mul_zero]
    exact code_Spec_zero T c hc

/-- An open sum, a block adding `E`, and a close by key `(t, ix)` (`t ≠ 0`). -/
theorem code_Spec_wrap (T : Array (Array 𝔽)) (c c2 : Code) (E : 𝔽) (t ix : ℕ) (hc : code_Al c)
    (ht : t ≠ 0) (h : code_Spec T (c.emit 0 0 0 0) c2 E) :
    code_Spec T c (c2.emit 1 t ix 0) (keyValG T (t, ix) * E) := by
  obtain ⟨hA0, hI0, hW0⟩ := code_emit c 0 0 0 0 hc
  obtain ⟨hA2, ⟨R2, hR2⟩, L2, hL2, hf2⟩ := h
  obtain ⟨hA3, hI3, hW3⟩ := code_emit c2 1 t ix 0 hA2
  refine ⟨hA3, ⟨R2, by rw [hW3, hR2, hW0]⟩, [(0, 0, 0, 0)] ++ L2 ++ [(1, t, ix, 0)],
    by rw [hI3, hL2, hI0]; simp only [List.append_assoc], fun R top st em ↦ ?_⟩
  rw [hW3, List.foldl_append, List.foldl_append]
  have h1 : List.foldl (code_step T (c2.ws ++ R)) (top, st, em) [(0, 0, 0, 0)] = (0, st.push top, em) := by
    simp only [List.foldl_cons, code_step, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, List.foldl_nil]
  rw [h1, hf2, zero_add]
  have ht' : (t == 0) = false := by simpa only [beq_eq_false_iff_ne, ne_eq] using ht
  simp only [List.foldl_cons, List.foldl_nil, code_step]
  simp only [show ((1 : ℕ) == 2) = false from rfl, show ((1 : ℕ) == 0) = false from rfl,
    show ((1 : ℕ) == 3) = false from rfl, Bool.false_eq_true, ite_false, Array.back?_push,
    Option.getD_some, Array.pop_push, ht']
  congr 1
  have := code_term T (t, ix) E (fun h ↦ absurd h ht)
  simp only [ht', Bool.false_eq_true, ite_false] at this
  rw [← this]; rfl

/-! ## `genCode` -/

/-! ## The atom code -/

theorem code_key (as : Array Atom) (i m : ℕ) :
    (as.getD i default).keys.getD m (0, 0) = (0, 0) ∨
      ∃ a ∈ as, ∃ h : m < a.keys.size, (as.getD i default).keys.getD m (0, 0) = a.keys[m] := by
  by_cases hi : i < as.size
  · have ha : as.getD i default = as[i] := by simp only [Array.getD_eq_getD_getElem?, hi, getElem?_pos, Option.getD_some]
    rw [ha]
    by_cases hm : m < as[i].keys.size
    · exact Or.inr ⟨as[i], Array.getElem_mem hi, hm, by simp only [Array.getD_eq_getD_getElem?, hm, getElem?_pos, Option.getD_some]⟩
    · exact Or.inl (by simp only [Array.getD_eq_getD_getElem?, hm, not_false_eq_true, getElem?_neg, Option.getD_none])
  · have ha : as.getD i default = default := by simp only [Array.getD_eq_getD_getElem?, hi, not_false_eq_true, getElem?_neg, Option.getD_none]
    rw [ha]
    exact Or.inl rfl

theorem code_atom0 : code_Al (⟨#[], #[], #[], #[], #[1]⟩ : Code) := ⟨rfl, rfl, rfl⟩

/-! ## Greedy code (B1-K2)

`atomCode` follows the fixed level order of the keys. `atomCodeG` chooses the level per node of the key trie: the
one with the fewest distinct nontrivial keys among the node's atoms, so that a node's products are few and its
children share. At P20 this is 122 k products against 165 k. The code's semantics (`runCode`) is unchanged. -/

/-- Lexicographic order on keys. -/
@[inline] def keyLt (a b : ℕ × ℕ) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- Atom `i`'s key at level `L`. -/
@[inline] def keyAt (as : Array Atom) (L i : ℕ) : ℕ × ℕ := (as.getD i default).keys.getD L (0, 0)

/-- The atoms `ix` sorted by their key at level `L` (ties by index: a strict order, so that `qsort` does not
degrade on the many equal keys). -/
def sortAt (as : Array Atom) (L : ℕ) (ix : Array ℕ) : Array ℕ :=
  ix.qsort fun i j ↦ let a := keyAt as L i; let b := keyAt as L j; keyLt a b || (a == b && i < j)

/-- The runs of equal level-`L` keys of the sorted `ix`: `(key, members)`. -/
def runsAt (as : Array Atom) (L : ℕ) (ix : Array ℕ) : Array ((ℕ × ℕ) × Array ℕ) := Id.run do
  let mut out : Array ((ℕ × ℕ) × Array ℕ) := #[]
  let mut cur : Array ℕ := #[]
  let mut k : ℕ × ℕ := keyAt as L (ix.getD 0 0)
  for i in ix do
    let k' := keyAt as L i
    if k' != k && !cur.isEmpty then
      out := out.push (k, cur)
      cur := #[]
    k := k'
    cur := cur.push i
  if !cur.isEmpty then out := out.push (k, cur)
  return out

/-- The level of `levels` with the fewest distinct nontrivial keys among `ix` (the first on ties), and its runs. -/
def bestLevel (as : Array Atom) (ix : Array ℕ) (levels : List ℕ) : ℕ × Array ((ℕ × ℕ) × Array ℕ) :=
  levels.foldl (fun (acc : ℕ × Array ((ℕ × ℕ) × Array ℕ) × ℕ) L ↦
    let rs := runsAt as L (sortAt as L ix)
    let c := (rs.filter fun r ↦ r.1.1 != 0).size
    if acc.2.2 ≤ c then acc else (L, rs, c)) (0, #[], ix.size + 1) |> fun r ↦ (r.1, r.2.1)

/-- **The greedy code** of the atoms `ix` over the remaining `levels`: per node the level of `bestLevel`; a run with a
trivial key is transparent, else a closed sum; at the last level, one leaf per run with its weights summed. -/
def genG (as : Array Atom) : ℕ → Array ℕ → List ℕ → Code → Code
  | 0, _, _, c => c
  | fuel + 1, ix, levels, c0 =>
    match levels with
    | [] =>
      -- no level left (atoms without keys): one leaf of the trivial key with the weights summed
      let w := ix.foldl (fun acc i ↦ acc + (as.getD i default).w) 0
      if w == 0 then c0 else if w == 1 then c0.emit 2 0 0 0 else { c0.emit 2 0 0 c0.ws.size with ws := c0.ws.push w }
    | [L] => Id.run do
      let mut c := c0
      for (k, g) in runsAt as L (sortAt as L ix) do
        let w := g.foldl (fun acc i ↦ acc + (as.getD i default).w) 0
        if !(w == 0) then
          if w == 1 then c := c.emit 2 k.1 k.2 0
          else c := { c.emit 2 k.1 k.2 c.ws.size with ws := c.ws.push w }
      return c
    | _ => Id.run do
      let (L, rs) := bestLevel as ix levels
      let rest := levels.erase L
      let mut c := c0
      for (k, g) in rs do
        if k.1 == 0 then
          c := genG as fuel g rest c
        else
          c := genG as fuel g rest (c.emit 0 0 0 0)
          c := c.emit 1 k.1 k.2 0
      return c

/-- The greedy code of an atom sum. -/
def atomCodeG (as : Array Atom) (D : ℕ) : Code :=
  genG as (D + 1) (Array.range as.size) (List.range D) ⟨#[], #[], #[], #[], #[1]⟩

/-- The greedy code of a pass's initial states: per run of equal level-0 keys (the state), its sum, emitted. -/
def initCodeG (as : Array Atom) (D : ℕ) : Code := Id.run do
  let mut c : Code := ⟨#[], #[], #[], #[], #[1]⟩
  for (k, g) in runsAt as 0 (sortAt as 0 (Array.range as.size)) do
    c := genG as (D + 1) g ((List.range D).erase 0) (c.emit 0 0 0 0)
    c := c.emit 3 0 k.2 0
  return c

open private Array.qpartition.loop from Init.Data.Array.QSort.Basic
open private Array.qsort.sort from Init.Data.Array.QSort.Basic

/-! ## `Array.qsort`: permutation, size and sortedness -/

/-- `w` is `v` with the positions in `[lo, hi]` permuted among themselves. -/
def greedy_qs_R {α : Type} {n : ℕ} (lo hi : ℕ) (v w : Vector α n) : Prop :=
  w.toList.Perm v.toList ∧ (∀ j (hj : j < n), (j < lo ∨ hi < j) → w[j] = v[j]) ∧
    (∀ j (hj : j < n), lo ≤ j → j ≤ hi → ∃ j', ∃ hj' : j' < n, lo ≤ j' ∧ j' ≤ hi ∧ w[j] = v[j'])

theorem greedy_qs_R_refl {α : Type} {n : ℕ} (lo hi : ℕ) (v : Vector α n) : greedy_qs_R lo hi v v :=
  ⟨List.Perm.refl _, fun _ _ _ ↦ rfl, fun j hj h1 h2 ↦ ⟨j, hj, h1, h2, rfl⟩⟩

theorem greedy_qs_R_trans {α : Type} {n : ℕ} {lo hi : ℕ} {u v w : Vector α n} (h₁ : greedy_qs_R lo hi u v)
    (h₂ : greedy_qs_R lo hi v w) : greedy_qs_R lo hi u w := by
  obtain ⟨p1, f1, m1⟩ := h₁
  obtain ⟨p2, f2, m2⟩ := h₂
  refine ⟨p2.trans p1, fun j hj h ↦ (f2 j hj h).trans (f1 j hj h), fun j hj h1 h2 ↦ ?_⟩
  obtain ⟨j', hj', a1, a2, e⟩ := m2 j hj h1 h2
  obtain ⟨j'', hj'', b1, b2, e'⟩ := m1 j' hj' a1 a2
  exact ⟨j'', hj'', b1, b2, e.trans e'⟩

theorem greedy_qs_R_mono {α : Type} {n : ℕ} {lo hi lo' hi' : ℕ} {v w : Vector α n} (h : greedy_qs_R lo' hi' v w)
    (hl : lo ≤ lo') (hh : hi' ≤ hi) : greedy_qs_R lo hi v w := by
  obtain ⟨p, f, m⟩ := h
  refine ⟨p, fun j hj h ↦ f j hj (by (clear * - hl hh h; omega)), fun j hj h1 h2 ↦ ?_⟩
  by_cases hin : lo' ≤ j ∧ j ≤ hi'
  · obtain ⟨j', hj', a1, a2, e⟩ := m j hj hin.1 hin.2
    exact ⟨j', hj', by (clear * - hl a1; omega), by (clear * - hh a2; omega), e⟩
  · exact ⟨j, hj, h1, h2, f j hj (by (clear * - hin; omega))⟩

theorem greedy_qs_R_swap {α : Type} {n : ℕ} {lo hi : ℕ} (v : Vector α n) (i k : ℕ) (hi' : i < n) (hk : k < n)
    (h1 : lo ≤ i) (h2 : i ≤ hi) (h3 : lo ≤ k) (h4 : k ≤ hi) : greedy_qs_R lo hi v (v.swap i k hi' hk) := by
  refine ⟨(Vector.swap_perm hi' hk).toList, fun j hj h ↦ ?_, fun j hj a1 a2 ↦ ?_⟩
  · rw [Vector.getElem_swap]
    split_ifs <;> first | rfl | omega
  · rw [Vector.getElem_swap]
    split_ifs
    · exact ⟨k, hk, h3, h4, rfl⟩
    · exact ⟨i, hi', h1, h2, rfl⟩
    · exact ⟨j, hj, a1, a2, rfl⟩

/-- The postcondition of a partition of `[lo, hi]` of `as`. -/
def greedy_qs_part {α : Type} {n : ℕ} (lt : α → α → Bool) (lo hi : ℕ) (hhi : hi < n) (as : Vector α n)
    (r : {m // lo ≤ m ∧ m ≤ hi} × Vector α n) : Prop :=
  greedy_qs_R lo hi as r.2 ∧
    (∀ j (hj : j < n), lo ≤ j → j < r.1.1 →
      lt r.2[j] (r.2[r.1.1]'(Nat.lt_of_le_of_lt r.1.2.2 hhi)) = true) ∧
    (∀ j (hj : j < n), r.1.1 < j → j ≤ hi →
      lt r.2[j] (r.2[r.1.1]'(Nat.lt_of_le_of_lt r.1.2.2 hhi)) = false)

theorem greedy_qs_part_of_R {α : Type} {n : ℕ} {lt : α → α → Bool} {lo hi : ℕ} {hhi : hi < n}
    {u v : Vector α n} {r : {m // lo ≤ m ∧ m ≤ hi} × Vector α n} (h : greedy_qs_R lo hi u v)
    (hp : greedy_qs_part lt lo hi hhi v r) : greedy_qs_part lt lo hi hhi u r :=
  ⟨greedy_qs_R_trans h hp.1, hp.2⟩

theorem greedy_qs_loop_part {α : Type} {n : ℕ} (lt : α → α → Bool) (lo hi : ℕ) (hhi : hi < n) (pivot : α)
    (as : Vector α n) (i k : ℕ) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) (hpiv : as[hi] = pivot)
    (h1 : ∀ j (hj : j < n), lo ≤ j → j < i → lt as[j] pivot = true)
    (h2 : ∀ j (hj : j < n), i ≤ j → j < k → lt as[j] pivot = false) :
    greedy_qs_part lt lo hi hhi as (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w) := by
  rw [Array.qpartition.loop.eq_def]
  by_cases h : k < hi
  · rw [dite_eq_left h]
    by_cases hl : lt as[k] pivot = true
    · rw [ite_eq_left hl]
      refine greedy_qs_part_of_R (greedy_qs_R_swap as i k (by (clear * - i n lo hi hhi k ik h; omega)) (by (clear * - k n lo hi hhi i h; omega)) ilo (by (clear * - i hi n lo k ik h; omega)) (by (clear * - lo k n hi i ilo ik; omega)) (by (clear * - w; omega)))
        (greedy_qs_loop_part lt lo hi hhi pivot _ (i + 1) (k + 1) _ _ _ ?_ ?_ ?_)
      · rw [Vector.getElem_swap]; split_ifs <;> omega
      · intro j hj a1 a2
        rw [Vector.getElem_swap]
        split_ifs with e1 e2
        · exact hl
        · (clear * - lt α n as i lo hi hhi k ik h pivot j a2 e1 e2; omega)
        · exact h1 j hj a1 (by (clear * - j i n lo hi k ik a2 e1 e2; omega))
      · intro j hj a1 a2
        rw [Vector.getElem_swap]
        split_ifs with e1 e2
        · (clear * - lt α n as k lo hi hhi i h pivot j a1 e1; omega)
        · exact h2 i (by (clear * - i n lo hi hhi k h j a1 e2; omega)) le_rfl (by (clear * - i k n lo hi j a1 e2; omega))
        · exact h2 j hj (by (clear * - i j n lo hi k a1; omega)) (by (clear * - j k n lo hi i a2 e2; omega))
    · rw [ite_eq_right hl]
      refine greedy_qs_loop_part lt lo hi hhi pivot as i (k + 1) _ _ _ hpiv h1 ?_
      intro j hj a1 a2
      by_cases e : j = k
      · subst e; simpa only [Bool.not_eq_true] using hl
      · exact h2 j hj a1 (by (clear * - j k n lo hi i a2 e; omega))
  · rw [dite_eq_right h]
    have hk : k = hi := by (clear * - k hi n lo i w h; omega)
    refine ⟨greedy_qs_R_swap as i hi (by (clear * - i n lo hi hhi k ik w h; omega)) hhi ilo (by (clear * - i hi n lo k ik w h; omega)) (by (clear * - lo hi n i k ilo ik w h; omega)) le_rfl, ?_, ?_⟩
    · intro j hj a1 a2
      dsimp only at a2
      simp only [Vector.getElem_swap, ite_true]
      rw [ite_eq_right (by (clear * - j i n lo hi k a2; omega)), ite_eq_right (by (clear * - j hi n lo i k ik w h a2; omega)), hpiv]
      exact h1 j hj a1 a2
    · intro j hj a1 a2
      dsimp only at a1
      simp only [Vector.getElem_swap, ite_true]
      rw [ite_eq_right (by (clear * - j i n lo hi k a1; omega)), hpiv]
      split_ifs with e
      · exact h2 i (by (clear * - i n lo hi k j hj a1; omega)) le_rfl (by (clear * - i k n lo hi w h j a1 e; omega))
      · exact h2 j hj (by (clear * - i j n lo hi k a1; omega)) (by (clear * - j k n lo hi i w h a2 e; omega))
termination_by hi - k
decreasing_by all_goals omega

theorem greedy_qs_loop_lt_hi {α : Type} {n : ℕ} (lt : α → α → Bool) (lo hi : ℕ) (hhi : hi < n) (pivot : α)
    (as : Vector α n) (i k : ℕ) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi)
    (h : i < k ∨ ∃ j, ∃ hj : j < n, k ≤ j ∧ j < hi ∧ lt as[j] pivot = false) :
    (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).1.1 < hi := by
  rw [Array.qpartition.loop.eq_def]
  by_cases hk : k < hi
  · rw [dite_eq_left hk]
    by_cases hl : lt as[k] pivot = true
    · rw [ite_eq_left hl]
      refine greedy_qs_loop_lt_hi lt lo hi hhi pivot _ (i + 1) (k + 1) _ _ _ ?_
      rcases h with h | ⟨j, hj, a1, a2, a3⟩
      · exact Or.inl (by (clear * - i k n lo hi h; omega))
      · right
        have hjk : j ≠ k := by rintro rfl; simp only [hl, Bool.true_eq_false] at a3
        refine ⟨j, hj, by (clear * - k j n lo hi i a1 hjk; omega), a2, ?_⟩
        rw [Vector.getElem_swap, ite_eq_right (by (clear * - j i n lo hi k ik a1 hjk; omega)), ite_eq_right hjk]
        exact a3
    · rw [ite_eq_right hl]
      exact greedy_qs_loop_lt_hi lt lo hi hhi pivot as i (k + 1) _ _ _ (Or.inl (by (clear * - i k n lo hi ik; omega)))
  · rw [dite_eq_right hk]
    show i < hi
    rcases h with h | ⟨j, hj, a1, a2, a3⟩ <;> omega
termination_by hi - k
decreasing_by all_goals omega

theorem greedy_qs_R_ite_swap {α : Type} {n : ℕ} {lo hi : ℕ} {v w : Vector α n} (h : greedy_qs_R lo hi v w) (c : Prop)
    [Decidable c] (i k : ℕ) (hi' : i < n) (hk : k < n) (h1 : lo ≤ i) (h2 : i ≤ hi) (h3 : lo ≤ k)
    (h4 : k ≤ hi) : greedy_qs_R lo hi v (if c then w.swap i k hi' hk else w) := by
  split_ifs
  · exact greedy_qs_R_trans h (greedy_qs_R_swap w i k hi' hk h1 h2 h3 h4)
  · exact h

theorem greedy_qs_ite_swap_not_lt {α : Type} {n : ℕ} (lt : α → α → Bool)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) (v : Vector α n) (a b : ℕ) (ha : a < n)
    (hb : b < n) (hab : a ≠ b) :
    lt (if lt v[a] v[b] = true then v.swap a b ha hb else v)[a]
      (if lt v[a] v[b] = true then v.swap a b ha hb else v)[b] = false := by
  by_cases hc : lt v[a] v[b] = true
  · simp only [hc, ite_true, Vector.getElem_swap]
    rw [ite_eq_right (Ne.symm hab)]
    exact hasymm _ _ hc
  · rw [ite_eq_right hc]
    simpa only [Bool.not_eq_true] using hc

theorem greedy_qs_qpartition_part {α : Type} {n : ℕ} (lt : α → α → Bool) (as : Vector α n) (lo hi : ℕ)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    greedy_qs_part lt lo hi hhi as (Array.qpartition as lt lo hi w hlo hhi) := by
  unfold Array.qpartition
  dsimp only
  refine greedy_qs_part_of_R ?_ (greedy_qs_loop_part lt lo hi hhi _ _ lo lo _ _ _ rfl
    (fun j _ a b ↦ absurd b (by (clear * - a b; omega))) (fun j _ a b ↦ absurd b (by (clear * - a b; omega))))
  refine greedy_qs_R_ite_swap (greedy_qs_R_ite_swap (greedy_qs_R_ite_swap (greedy_qs_R_refl lo hi as) _ _ _ _ _ ?_ ?_ ?_ ?_)
    _ _ _ _ _ ?_ ?_ ?_ ?_) _ _ _ _ _ ?_ ?_ ?_ ?_ <;> omega

theorem greedy_qs_qpartition_lt_hi {α : Type} {n : ℕ} (lt : α → α → Bool)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) (as : Vector α n) (lo hi : ℕ)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (h : lo < hi) :
    (Array.qpartition as lt lo hi w hlo hhi).1.1 < hi := by
  unfold Array.qpartition
  dsimp only
  apply greedy_qs_loop_lt_hi
  right
  exact ⟨(lo + hi) / 2, by (clear * - hhi h; omega), by (clear * - h; omega), by (clear * - h; omega),
    greedy_qs_ite_swap_not_lt lt hasymm _ _ _ _ _ (by (clear * - h; omega))⟩

theorem greedy_qs_sort_R {α : Type} (lt : α → α → Bool) {n : ℕ} (as : Vector α n) (lo hi : ℕ) (w : lo ≤ hi)
    (hlo : lo < n) (hhi : hi < n) : greedy_qs_R lo hi as (Array.qsort.sort lt as lo hi w hlo hhi) := by
  rw [Array.qsort.sort.eq_def]
  split
  · rename_i h₁
    have hp := greedy_qs_qpartition_part lt as lo hi w hlo hhi
    split
    rename_i mid hmid b heq
    rw [heq] at hp
    split
    · exact hp.1
    · rename_i h₂
      exact greedy_qs_R_trans hp.1 (greedy_qs_R_trans (greedy_qs_R_mono (greedy_qs_sort_R lt b lo mid _ _ _) le_rfl (by (clear * - mid hi n lo h₂; omega)))
        (greedy_qs_R_mono (greedy_qs_sort_R lt _ (mid + 1) hi _ _ _) (by (clear * - lo mid n hi hmid; omega)) le_rfl))
  · exact greedy_qs_R_refl _ _ _
termination_by hi - lo
decreasing_by all_goals omega

theorem greedy_qs_sort_sorted {α : Type} (lt : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) {n : ℕ} (as : Vector α n) (lo hi : ℕ)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (i j : ℕ) (hi' : i < n) (hj : j < n)
    (a1 : lo ≤ i) (a2 : i < j) (a3 : j ≤ hi) :
    lt (Array.qsort.sort lt as lo hi w hlo hhi)[j] (Array.qsort.sort lt as lo hi w hlo hhi)[i] = false := by
  rw [Array.qsort.sort.eq_def]
  split
  · rename_i h₁
    have hp := greedy_qs_qpartition_part lt as lo hi w hlo hhi
    have hlt := greedy_qs_qpartition_lt_hi lt hasymm as lo hi w hlo hhi h₁
    split
    rename_i mid hmid b heq
    rw [heq] at hp hlt
    dsimp only [greedy_qs_part] at hp hlt
    split
    · omega
    · rename_i h₂
      have Rc := greedy_qs_sort_R lt b lo mid hmid.1 hlo (by (clear * - mid n lo hi hhi i j hlt; omega))
      have Rd := greedy_qs_sort_R lt (Array.qsort.sort lt b lo mid hmid.1 hlo (by (clear * - mid n lo hi hhi i j hlt; omega))) (mid + 1) hi
        (by (clear * - mid hi n lo i j hlt; omega)) (by (clear * - mid n lo hi hhi i j hlt; omega)) hhi
      by_cases hA : mid + 1 ≤ i
      · exact greedy_qs_sort_sorted lt htrans hasymm _ (mid + 1) hi _ _ _ i j hi' hj hA a2 a3
      by_cases hB : j ≤ mid
      · rw [Rd.2.1 i hi' (by (clear * - i mid hi n lo j hA; omega)), Rd.2.1 j hj (by (clear * - j mid hi n lo i hB; omega))]
        exact greedy_qs_sort_sorted lt htrans hasymm b lo mid _ _ _ i j hi' hj a1 a2 hB
      · rw [Rd.2.1 i hi' (by (clear * - i mid hi n lo j hA; omega))]
        obtain ⟨i', hi'', b1, b2, ei⟩ := Rc.2.2 i hi' a1 (by (clear * - i mid n lo hi j hA; omega))
        obtain ⟨j', hj', c1, c2, ej⟩ := Rd.2.2 j hj (by (clear * - mid j n lo hi i hB i'; omega)) a3
        rw [ei, ej, Rc.2.1 j' hj' (by (clear * - j' lo mid n hi i j i' c1; omega))]
        have hr := hp.2.2 j' hj' (by (clear * - mid j' n lo hi i j i' c1; omega)) c2
        by_cases e : i' = mid
        · subst e; exact hr
        · have hl := hp.2.1 i' hi'' b1 (by (clear * - i' mid n lo hi i j b2 j' e; omega))
          cases hc : lt b[j'] b[i']
          · rfl
          · rw [htrans _ _ _ hc hl] at hr; exact hr
  · omega
termination_by hi - lo
decreasing_by all_goals omega

theorem greedy_qs_qsort_perm {α : Type} (as : Array α) (lt : α → α → Bool) :
    (as.qsort lt).toList.Perm as.toList := by
  unfold Array.qsort
  split
  · exact List.Perm.refl _
  · exact (greedy_qs_sort_R lt as.toVector _ _ _ _ _).1

theorem greedy_qs_qsort_size {α : Type} (as : Array α) (lt : α → α → Bool) : (as.qsort lt).size = as.size := by
  unfold Array.qsort
  split
  · rfl
  · simp only [zero_le, inf_of_le_left, min_self, sup_of_le_right, Vector.size_toArray]

theorem greedy_qs_qsort_sorted {α : Type} (as : Array α) (lt : α → α → Bool)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hasymm : ∀ a b, lt a b = true → lt b a = false) :
    (as.qsort lt).toList.Pairwise fun a b ↦ lt b a = false := by
  unfold Array.qsort
  split
  · rename_i h
    simp only [Array.eq_empty_of_size_eq_zero h, Array.toList_empty, List.Pairwise.nil]
  · rename_i h
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [Array.length_toList, Vector.size_toArray] at hi hj
    simp only [Array.getElem_toList, Vector.getElem_toArray]
    exact greedy_qs_sort_sorted lt htrans hasymm as.toVector _ _ _ _ _ i j hi hj (by (clear * - h; omega)) hij (by (clear * - h hi hj; omega))

/-! ## `keysLt` is the strict lexicographic order on `List (ℕ × ℕ)` -/

/-! ## `runsAt` -/

theorem greedy_forIn_arr {α β : Type} (l : Array α) (init : β) (B : α → β → Id (ForInStep β))
    (F : β → α → β) (hB : ∀ a b, B a b = pure (ForInStep.yield (F b a))) :
    forIn l init B = pure (l.foldl F init) := by
  have : B = fun a b ↦ pure (ForInStep.yield (F b a)) := funext fun a ↦ funext fun b ↦ hB a b
  subst this
  simp only [Array.forIn_pure_yield_eq_foldl]

/-- One step of `runsAt`'s loop. -/
def greedy_rStep (as : Array Atom) (L : ℕ) (s : Array ((ℕ × ℕ) × Array ℕ) × Array ℕ × (ℕ × ℕ)) (i : ℕ) :
    Array ((ℕ × ℕ) × Array ℕ) × Array ℕ × (ℕ × ℕ) :=
  if (keyAt as L i != s.2.2 && !s.2.1.isEmpty) = true then (s.1.push (s.2.2, s.2.1), #[i], keyAt as L i)
  else (s.1, s.2.1.push i, keyAt as L i)

theorem greedy_runsAt_eq (as : Array Atom) (L : ℕ) (ix : Array ℕ) :
    runsAt as L ix = (let s := ix.foldl (greedy_rStep as L) (#[], #[], keyAt as L (ix.getD 0 0))
      if (!s.2.1.isEmpty) = true then s.1.push (s.2.2, s.2.1) else s.1) := by
  unfold runsAt
  simp only [Id.run]
  rw [greedy_forIn_arr _ _ _ (greedy_rStep as L) (fun a b ↦ by simp only [greedy_rStep]; split_ifs <;> rfl)]
  simp only [pure_bind]
  split_ifs <;> rfl

/-- Consecutive entries differ. -/
def greedy_adj : List (ℕ × ℕ) → Prop
  | a :: b :: l => a ≠ b ∧ greedy_adj (b :: l)
  | _ => True

theorem greedy_adj_snoc (l : List (ℕ × ℕ)) (a b : ℕ × ℕ) (h : greedy_adj (l ++ [a])) (hab : a ≠ b) :
    greedy_adj (l ++ [a] ++ [b]) := by
  induction l with
  | nil => exact ⟨hab, trivial⟩
  | cons x l ih =>
    cases l with
    | nil => exact ⟨h.1, hab, trivial⟩
    | cons y l => exact ⟨h.1, ih h.2⟩

/-- The invariant of `runsAt`'s loop after the prefix `p`. -/
def greedy_rInv (as : Array Atom) (L : ℕ) (p : List ℕ)
    (s : Array ((ℕ × ℕ) × Array ℕ) × Array ℕ × (ℕ × ℕ)) : Prop :=
  (s.1.toList.map (·.2.toList)).flatten ++ s.2.1.toList = p ∧
    (∀ r ∈ s.1.toList, r.2.toList ≠ [] ∧ ∀ i ∈ r.2.toList, keyAt as L i = r.1) ∧
    (∀ i ∈ s.2.1.toList, keyAt as L i = s.2.2) ∧ (s.2.1.toList = [] → s.1.toList = []) ∧
    greedy_adj (s.1.toList.map (·.1) ++ [s.2.2])

theorem greedy_rInv_step (as : Array Atom) (L : ℕ) (p : List ℕ) (s : Array ((ℕ × ℕ) × Array ℕ) × Array ℕ × (ℕ × ℕ))
    (i : ℕ) (h : greedy_rInv as L p s) : greedy_rInv as L (p ++ [i]) (greedy_rStep as L s i) := by
  obtain ⟨out, cur, k⟩ := s
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  unfold greedy_rStep
  dsimp only
  split_ifs with hc
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', Array.isEmpty_eq_false_iff] at hc
    have hcur : cur.toList ≠ [] := by simpa only [ne_eq, Array.toList_eq_nil_iff] using hc.2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc, ← h1]
    · intro r hr
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact h2 r hr
      · exact ⟨hcur, h3⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    · simp only [List.cons_ne_self, Array.toList_push, List.append_eq_nil_iff, Array.toList_eq_nil_iff, and_false, imp_self]
    · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
      exact greedy_adj_snoc _ _ _ h5 (Ne.symm hc.1)
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', Array.isEmpty_eq_false_iff,
      not_and, not_not] at hc
    refine ⟨?_, h2, ?_, ?_, ?_⟩
    · simp only [Array.toList_push, ← h1, List.append_assoc]
    · intro j hj
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · by_cases hk : keyAt as L i = k
        · rw [hk]; exact h3 j hj
        · have := hc hk; simp only [this, Array.toList_empty, List.not_mem_nil] at hj
      · rfl
    · simp only [Array.toList_push, List.append_eq_nil_iff, Array.toList_eq_nil_iff, List.cons_ne_self, and_false, IsEmpty.forall_iff]
    · by_cases hk : keyAt as L i = k
      · rw [hk]; exact h5
      · have hcur := hc hk
        have : out.toList = [] := h4 (by simp only [hcur, Array.toList_empty])
        simp only [this, List.map_nil, List.nil_append, greedy_adj]

theorem greedy_rInv_fold (as : Array Atom) (L : ℕ) (l : List ℕ) :
    ∀ p s, greedy_rInv as L p s → greedy_rInv as L (p ++ l) (l.foldl (greedy_rStep as L) s) := by
  induction l with
  | nil => intro p s h; simpa only [List.append_nil, List.foldl_nil] using h
  | cons i l ih =>
    intro p s h
    have := ih _ _ (greedy_rInv_step as L p s i h)
    simpa only [List.foldl_cons, List.append_assoc, List.cons_append, List.nil_append] using this

/-- **`runsAt`**: its runs' members, concatenated, are the input; each run is nonempty and its members carry its
key; consecutive runs have distinct keys. -/
theorem greedy_runsAt_spec (as : Array Atom) (L : ℕ) (xs : Array ℕ) :
    ((runsAt as L xs).toList.map (·.2.toList)).flatten = xs.toList ∧
      (∀ r ∈ (runsAt as L xs).toList, r.2.toList ≠ [] ∧ ∀ i ∈ r.2.toList, keyAt as L i = r.1) ∧
      greedy_adj ((runsAt as L xs).toList.map (·.1)) := by
  have h0 : greedy_rInv as L [] (#[], #[], keyAt as L (xs.getD 0 0)) :=
    ⟨by simp only [List.map_nil, List.flatten_nil, List.append_nil], by simp only [List.not_mem_nil, ne_eq, Array.toList_eq_nil_iff, Array.mem_toList_iff, IsEmpty.forall_iff, implies_true], by simp only [List.not_mem_nil, Array.getD_eq_getD_getElem?, IsEmpty.forall_iff, implies_true], by simp only [imp_self], trivial⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := greedy_rInv_fold as L xs.toList [] _ h0
  rw [greedy_runsAt_eq, ← Array.foldl_toList]
  dsimp only
  split_ifs with hc
  · simp only [Bool.not_eq_true', Array.isEmpty_eq_false_iff] at hc
    have hcur : (xs.toList.foldl (greedy_rStep as L) (#[], #[], keyAt as L (xs.getD 0 0))).2.1.toList ≠ [] := by
      simpa only [Array.getD_eq_getD_getElem?, Array.foldl_toList, ne_eq, Array.toList_eq_nil_iff] using hc
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Array.getD_eq_getD_getElem?, Array.foldl_toList, Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append] using h1
    · intro r hr
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact h2 r hr
      · exact ⟨hcur, h3⟩
    · simpa only [Array.getD_eq_getD_getElem?, Array.foldl_toList, Array.toList_push, List.map_append, List.map_cons, List.map_nil] using h5
  · simp only [Bool.not_eq_true', Array.isEmpty_eq_false_iff, not_not] at hc
    have hcur : (xs.toList.foldl (greedy_rStep as L) (#[], #[], keyAt as L (xs.getD 0 0))).2.1.toList = [] := by
      rw [hc]
    have := h4 hcur
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nil_append] at h1; rw [← h1, hcur, this]; simp only [Array.getD_eq_getD_getElem?, List.map_nil, List.flatten_nil, List.append_nil, List.foldl_nil, Array.toList_empty]
    · rw [this]; simp only [List.not_mem_nil, ne_eq, Array.toList_eq_nil_iff, Array.mem_toList_iff, IsEmpty.forall_iff, implies_true]
    · rw [this]; trivial

theorem greedy_sortAt_perm (as : Array Atom) (L : ℕ) (ix : Array ℕ) : (sortAt as L ix).toList.Perm ix.toList :=
  greedy_qs_qsort_perm _ _

theorem greedy_sortAt_size (as : Array Atom) (L : ℕ) (ix : Array ℕ) : (sortAt as L ix).size = ix.size :=
  greedy_qs_qsort_size _ _

theorem greedy_len_le (R : List ((ℕ × ℕ) × Array ℕ)) (h : ∀ r ∈ R, r.2.toList ≠ []) :
    R.length ≤ (R.map (·.2.toList)).flatten.length := by
  induction R with
  | nil => simp only [List.length_nil, List.map_nil, List.flatten_nil, Std.le_refl]
  | cons r R ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.length_append]
    have h1 := List.length_pos_iff.2 (h r List.mem_cons_self)
    have h2 := ih (fun r' hr' ↦ h r' (List.mem_cons_of_mem _ hr'))
    (clear * - h1 h2; omega)

theorem greedy_runsAt_size (as : Array Atom) (L : ℕ) (xs : Array ℕ) : (runsAt as L xs).size ≤ xs.size := by
  obtain ⟨h1, h2, -⟩ := greedy_runsAt_spec as L xs
  have := greedy_len_le _ (fun r hr ↦ (h2 r hr).1)
  rw [h1] at this
  simpa only [ge_iff_le, Array.length_toList] using this

/-- Summing over `ix` is summing over the runs of `runsAt` of the sorted `ix`. -/
theorem greedy_runs_sum (as : Array Atom) (L : ℕ) (ix : Array ℕ) (f : ℕ → 𝔽) :
    (ix.toList.map f).sum = ((runsAt as L (sortAt as L ix)).toList.map fun r ↦ (r.2.toList.map f).sum).sum := by
  rw [← ((greedy_sortAt_perm as L ix).map f).sum_eq, ← (greedy_runsAt_spec as L (sortAt as L ix)).1]
  simp only [List.map_flatten, List.map_map, Function.comp_def, List.sum_flatten]

/-- **`bestLevel`** picks a level of `levels` and its runs. -/
theorem greedy_bestLevel (as : Array Atom) (ix : Array ℕ) (L0 : ℕ) (t : List ℕ) :
    ∃ L ∈ L0 :: t, bestLevel as ix (L0 :: t) = (L, runsAt as L (sortAt as L ix)) := by
  unfold bestLevel
  dsimp only
  rw [List.foldl_cons]
  have hc : ¬ ix.size + 1 ≤ ((runsAt as L0 (sortAt as L0 ix)).filter fun r ↦ r.1.1 != 0).size := by
    have := greedy_runsAt_size as L0 (sortAt as L0 ix)
    have := Array.size_filter_le (p := fun r : (ℕ × ℕ) × Array ℕ ↦ r.1.1 != 0)
      (xs := runsAt as L0 (sortAt as L0 ix))
    rw [greedy_sortAt_size] at *
    omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
  suffices ∀ (l : List ℕ) (acc : ℕ × Array ((ℕ × ℕ) × Array ℕ) × ℕ), (∀ L ∈ l, L ∈ L0 :: t) →
      acc.1 ∈ L0 :: t → acc.2.1 = runsAt as acc.1 (sortAt as acc.1 ix) →
      ∃ L ∈ L0 :: t, ((l.foldl (fun (acc : ℕ × Array ((ℕ × ℕ) × Array ℕ) × ℕ) L ↦
        if acc.2.2 ≤ ((runsAt as L (sortAt as L ix)).filter fun r ↦ r.1.1 != 0).size then acc
        else (L, runsAt as L (sortAt as L ix), ((runsAt as L (sortAt as L ix)).filter fun r ↦ r.1.1 != 0).size))
          acc).1, (l.foldl (fun (acc : ℕ × Array ((ℕ × ℕ) × Array ℕ) × ℕ) L ↦
        if acc.2.2 ≤ ((runsAt as L (sortAt as L ix)).filter fun r ↦ r.1.1 != 0).size then acc
        else (L, runsAt as L (sortAt as L ix), ((runsAt as L (sortAt as L ix)).filter fun r ↦ r.1.1 != 0).size))
          acc).2.1) = (L, runsAt as L (sortAt as L ix)) from
    this t _ (fun L hL ↦ List.mem_cons_of_mem _ hL) List.mem_cons_self rfl
  intro l
  induction l with
  | nil => intro acc _ h1 h2; exact ⟨acc.1, h1, by rw [← h2]; rfl⟩
  | cons L l ih =>
    intro acc hl h1 h2
    rw [List.foldl_cons]
    apply ih _ (fun L' hL' ↦ hl L' (List.mem_cons_of_mem _ hL'))
    · split_ifs
      · exact h1
      · exact hl L List.mem_cons_self
    · split_ifs
      · exact h2
      · rfl

/-! ## `genG` -/

theorem greedy_loop_Spec {X : Type} (T : Array (Array 𝔽)) (F : Code → X → Code) (e : X → 𝔽) (l : List X)
    (hF : ∀ c x, x ∈ l → code_Al c → 0 < c.ws.size → code_Spec T c (F c x) (e x)) :
    ∀ c, code_Al c → 0 < c.ws.size → code_Spec T c (l.foldl F c) (l.map e).sum := by
  induction l with
  | nil => intro c hc _; simpa only [List.foldl_nil, List.map_nil, List.sum_nil] using code_Spec_zero T c hc
  | cons x l ih =>
    intro c hc hw
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    have h1 := hF c x List.mem_cons_self hc hw
    obtain ⟨hA1, ⟨R1, hR1⟩, -⟩ := id h1
    exact code_Spec_trans T _ _ _ _ _ h1
      (ih (fun c x hx ↦ hF c x (List.mem_cons_of_mem _ hx)) _ hA1 (by rw [hR1, Array.size_append]; (clear * - hw; omega)))

/-- The sum over `ix` of `w · Π_levels`, split by the runs at `L0 ∈ levels`. -/
theorem greedy_sum_level (T : Array (Array 𝔽)) (as : Array Atom) (levels : List ℕ) (L0 : ℕ) (hL0 : L0 ∈ levels)
    (ix : Array ℕ) :
    (ix.toList.map fun i ↦ KRing.ofE (as.getD i default).w * (levels.map fun L ↦ keyValG T (keyAt as L i)).prod).sum =
      ((runsAt as L0 (sortAt as L0 ix)).toList.map fun r ↦ keyValG T r.1 *
        (r.2.toList.map fun i ↦ KRing.ofE (as.getD i default).w *
          ((levels.erase L0).map fun L ↦ keyValG T (keyAt as L i)).prod).sum).sum := by
  rw [greedy_runs_sum as L0 ix]
  refine congrArg List.sum (List.map_congr_left fun r hr ↦ ?_)
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
  have hk := (greedy_runsAt_spec as L0 (sortAt as L0 ix)).2.1 r hr |>.2 i hi
  rw [((List.perm_cons_erase hL0).map _).prod_eq, List.map_cons, List.prod_cons, hk]
  ring

theorem greedy_genG_P (T : Array (Array 𝔽)) (as : Array Atom) (P : ℕ → Prop) (hT : keyValG T (0, 0) = 1)
    (hK : ∀ i m, P m → (keyAt as m i).1 = 0 → keyValG T (keyAt as m i) = 1) :
    ∀ fuel (ix : Array ℕ) (levels : List ℕ) (c : Code), levels.Nodup → levels.length < fuel →
      (∀ L ∈ levels, P L) → code_Al c → 0 < c.ws.size →
      code_Spec T c (genG as fuel ix levels c)
        ((ix.toList.map fun i ↦ KRing.ofE (as.getD i default).w * (levels.map fun L ↦ keyValG T (keyAt as L i)).prod).sum) := by
  intro fuel
  induction fuel with
  | zero => intro ix levels c _ h; (clear * - h; omega)
  | succ f ih =>
    intro ix levels c hn hl hP hc hw
    match levels, hn, hl, hP with
    | [], _, _, _ =>
      have e : genG as (f + 1) ix [] c = code_leaf c (0, 0) (ix.foldl (fun acc i ↦ acc + (as.getD i default).w) 0) := by
        simp only [genG, code_leaf]
        generalize (ix.foldl (fun acc i ↦ acc + (as.getD i default).w) 0 == 0) = b
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Array.getD_eq_getD_getElem?, beq_iff_eq, Bool.not_false, Bool.not_true]
      rw [e]
      have := code_Spec_leaf T c (0, 0) (ix.foldl (fun acc i ↦ acc + (as.getD i default).w) 0) hc hw
      rw [hT, one_mul] at this
      convert this using 1
      rw [← Array.foldl_toList, runs_foldl_add, zero_add]
      simp only [Array.getD_eq_getD_getElem?, List.map_nil, List.prod_nil, mul_one, map_list_sum, List.map_map, Function.comp_def]
    | [L], _, _, _ =>
      have e : genG as (f + 1) ix [L] c = (runsAt as L (sortAt as L ix)).toList.foldl
          (fun c r ↦ code_leaf c r.1 (r.2.foldl (fun acc i ↦ acc + (as.getD i default).w) 0)) c := by
        simp only [genG, Id.run]
        rw [greedy_forIn_arr _ _ _ (fun c r ↦ code_leaf c r.1 (r.2.foldl (fun acc i ↦ acc + (as.getD i default).w) 0))
          (fun a b ↦ by
            obtain ⟨k, g⟩ := a; simp only [code_leaf]
            generalize g.foldl (fun acc i ↦ acc + (as.getD i default).w) 0 = w
            cases w == 0 <;> cases w == 1 <;> rfl), ← Array.foldl_toList]
        rfl
      rw [e, greedy_sum_level T as [L] L List.mem_cons_self ix]
      apply greedy_loop_Spec _ _ _ _ _ c hc hw
      intro c r hr hc hw
      have := code_Spec_leaf T c r.1 (r.2.foldl (fun acc i ↦ acc + (as.getD i default).w) 0) hc hw
      convert this using 1
      rw [← Array.foldl_toList, runs_foldl_add, zero_add]
      simp only [Array.getD_eq_getD_getElem?, List.erase_cons_head, List.map_nil, List.prod_nil, mul_one, map_list_sum, List.map_map, Function.comp_def]
    | L :: L' :: t, hn, hl, hP =>
      obtain ⟨L0, hL0, hb⟩ := greedy_bestLevel as ix L (L' :: t)
      have e : genG as (f + 1) ix (L :: L' :: t) c = (runsAt as L0 (sortAt as L0 ix)).toList.foldl
          (fun c r ↦ if r.1.1 == 0 then genG as f r.2 ((L :: L' :: t).erase L0) c
            else (genG as f r.2 ((L :: L' :: t).erase L0) (c.emit 0 0 0 0)).emit 1 r.1.1 r.1.2 0) c := by
        simp only [genG, Id.run]
        rw [hb, greedy_forIn_arr _ _ _ (fun c r ↦ if r.1.1 == 0 then genG as f r.2 ((L :: L' :: t).erase L0) c
            else (genG as f r.2 ((L :: L' :: t).erase L0) (c.emit 0 0 0 0)).emit 1 r.1.1 r.1.2 0)
          (fun a b ↦ by split_ifs <;> rfl), ← Array.foldl_toList]
        rfl
      rw [e, greedy_sum_level T as _ L0 hL0 ix]
      apply greedy_loop_Spec _ _ _ _ _ c hc hw
      intro c r hr hc hw
      obtain ⟨hne, hkey⟩ := (greedy_runsAt_spec as L0 (sortAt as L0 ix)).2.1 r hr
      have hn' : ((L :: L' :: t).erase L0).Nodup := hn.erase L0
      have hl' : ((L :: L' :: t).erase L0).length < f := by
        rw [List.length_erase_of_mem hL0]; simp only [List.length_cons] at hl ⊢; (clear * - hl; omega)
      have hP' : ∀ M ∈ (L :: L' :: t).erase L0, P M := fun M h ↦ hP M (List.mem_of_mem_erase h)
      split_ifs with h0
      · obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hne
        have hk1 : keyValG T r.1 = 1 := by
          rw [← hkey i hi]; exact hK i L0 (hP L0 hL0) (by rw [hkey i hi]; simpa only [beq_iff_eq] using h0)
        rw [hk1, one_mul]
        exact ih _ _ _ hn' hl' hP' hc hw
      · obtain ⟨hA0, -, hW0⟩ := code_emit c 0 0 0 0 hc
        exact code_Spec_wrap T c _ _ _ _ hc (by simpa only [ne_eq, beq_iff_eq] using h0) (ih _ _ _ hn' hl' hP' hA0 (by rw [hW0]; exact hw))

/-- The greedy code's block adds Σ_{i ∈ ix} w_i Π_{L ∈ levels} keyVal(key_L(i)). -/
theorem greedy_genG (T : Array (Array 𝔽)) (as : Array Atom) (hT : keyValG T (0, 0) = 1)
    (hK : ∀ i m, ((as.getD i default).keys.getD m (0, 0)).1 = 0 → keyValG T ((as.getD i default).keys.getD m (0, 0)) = 1) :
    ∀ fuel (ix : Array ℕ) (levels : List ℕ) (c : Code), levels.Nodup → levels.length < fuel → code_Al c → 0 < c.ws.size →
      code_Spec T c (genG as fuel ix levels c)
        ((ix.toList.map fun i ↦ KRing.ofE (as.getD i default).w * (levels.map fun L ↦ keyValG T (keyAt as L i)).prod).sum) :=
  fun fuel ix levels c hn hl hc hw ↦ greedy_genG_P T as (fun _ ↦ True) hT (fun i m _ h ↦ hK i m h) fuel ix levels c
    hn hl (fun _ _ ↦ trivial) hc hw

/-! ## The atom sum -/

theorem greedy_range_map (as : Array Atom) (g : Atom → 𝔽) :
    (List.range as.size).map (fun i ↦ g (as.getD i default)) = as.toList.map g := by
  apply List.ext_getElem
  · simp only [Array.getD_eq_getD_getElem?, List.length_map, List.length_range, Array.length_toList]
  · intro n h1 h2
    simp only [List.length_map, Array.length_toList] at h2
    simp only [Array.getD_eq_getD_getElem?, List.getElem_map, List.getElem_range, h2, getElem?_pos, Option.getD_some, Array.getElem_toList]

theorem greedy_foldl_mul (T : Array (Array 𝔽)) (l : List (ℕ × ℕ)) (c : 𝔽) :
    l.foldl (fun acc k ↦ acc * keyValG T k) c = c * (l.map (keyValG T)).prod := by
  induction l generalizing c with
  | nil => simp only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | cons k l ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

theorem greedy_keys_toList (a : Atom) :
    a.keys.toList = (List.range a.keys.size).map fun L ↦ a.keys.getD L (0, 0) := by
  apply List.ext_getElem
  · simp only [Array.length_toList, Array.getD_eq_getD_getElem?, List.length_map, List.length_range]
  · intro n h1 h2
    simp only [Array.length_toList] at h1
    simp only [Array.getElem_toList, Array.getD_eq_getD_getElem?, List.getElem_map, List.getElem_range, h1, getElem?_pos, Option.getD_some]

theorem greedy_atom_prod (T : Array (Array 𝔽)) (a : Atom) (D : ℕ) (h : a.keys.size = D) :
    KRing.ofE a.w * ((List.range D).map fun L ↦ keyValG T (a.keys.getD L (0, 0))).prod = atomVal T a := by
  rw [atomVal, ← Array.foldl_toList, greedy_foldl_mul, greedy_keys_toList, h, List.map_map]
  rfl

theorem greedy_hK (T : Array (Array 𝔽)) (as : Array Atom) (hT : keyValG T (0, 0) = 1)
    (h0 : ∀ a ∈ as, ∀ k ∈ a.keys, k.1 = 0 → k.2 = 0) :
    ∀ i m, ((as.getD i default).keys.getD m (0, 0)).1 = 0 → keyValG T ((as.getD i default).keys.getD m (0, 0)) = 1 := by
  intro i m h1
  rcases code_key as i m with h | ⟨a, ha, hm, h⟩
  · rw [h]; exact hT
  · have h2 := h0 a ha _ (Array.getElem_mem hm) (h ▸ h1)
    rw [h, ← hT]
    congr 1
    exact Prod.ext (h ▸ h1) h2

theorem runCode_atomCodeG (T : Array (Array 𝔽)) (as : Array Atom) (D : ℕ)
    (hD : ∀ a ∈ as, a.keys.size = D) (hT : keyValG T (0, 0) = 1)
    (h0 : ∀ a ∈ as, ∀ k ∈ a.keys, k.1 = 0 → k.2 = 0) :
    (runCodeG T (atomCodeG as D)).1 = (as.toList.map (atomVal T)).sum := by
  obtain ⟨-, -, L, hL, hf⟩ := greedy_genG T as hT (greedy_hK T as hT h0) (D + 1) (Array.range as.size)
    (List.range D) _ List.nodup_range (by simp only [List.length_range, lt_add_iff_pos_right, Order.lt_one_iff]) code_atom0 (by decide)
  rw [code_runCode]
  unfold atomCodeG
  have := hf #[] 0 #[] #[]
  rw [Array.append_empty] at this
  have hn : code_instrs (⟨#[], #[], #[], #[], #[1]⟩ : Code) = [] := rfl
  rw [hL, hn, List.nil_append, this, zero_add, Array.toList_range]
  dsimp only
  rw [← greedy_range_map as (atomVal T)]
  refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
  exact greedy_atom_prod T _ D (hD _ (runs_getD_mem as i (List.mem_range.1 hi)))

/-! ## Flat tables and fused code (B1-K2)

`runCode` reads `T[ta][ix]` through two arrays and spends one instruction on every open, leaf and close. The
fused form reads one flat array of every table's entries and fuses the frequent shapes: an open and its first
leaf; an open, one leaf and a keyed close (one product, about three in four closes at P20). `fuse` translates a
`Code` to it, checking every index against the recipes' static sizes (else `none`, and `evalC` runs the code
itself); the result computes what the code computes (`runF_fuse`, proved below). -/

/-- A recipe's table size (that of `tabsAt`'s table for it). -/
def TRec.size : TRec → ℕ
  | .one => 1
  | .eqx bits => 2 ^ bits.length
  | .eqy bits => 2 ^ bits.length
  | .kap => 16
  | .ker ks => ks.size
  | .prod rows => rows.size

/-- The tables' offsets in the flat array: `offs[t] = Σ_{u<t} (rs[u]).size`, the total last. -/
def tabOffs (rs : Array TRec) : Array ℕ :=
  rs.foldl (fun acc r ↦ acc.push (acc.getD (acc.size - 1) 0 + r.size)) #[0]

/-- **The flat tables**: entry `i < (rs[t]).size` of table `t` at `offs[t] + i` (by `getD`: a short table reads
`0` past its end, as `keyVal` does). -/
def flatTabs (rs : Array TRec) (T : Array (Array FE)) : Array FE := Id.run do
  let mut F : Array FE := Array.mkEmpty ((tabOffs rs).getD rs.size 0)
  for t in [0:rs.size] do
    let tt := T.getD t #[]
    for i in [0:(rs.getD t .one).size] do
      F := F.push (tt.getD i 0)
  return F

omit [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] in
/-- The proof-side twin of `flatTabs` over a value ring (S2GT-W). -/
def flatTabsG (rs : Array TRec) (T : Array (Array 𝔽)) : Array 𝔽 := Id.run do
  let mut F : Array 𝔽 := Array.mkEmpty ((tabOffs rs).getD rs.size 0)
  for t in [0:rs.size] do
    let tt := T.getD t #[]
    for i in [0:(rs.getD t .one).size] do
      F := F.push (tt.getD i 0)
  return F

/-- A weight's kind: `m < 3` for `c·y^m` with `c ∈ K` (`fmul`'s cases, in its order), `3` otherwise. -/
def wKind (w : FE) : ℕ :=
  if w.c₁ == 0 && w.c₂ == 0 then 0 else if w.c₀ == 0 && w.c₂ == 0 then 1
  else if w.c₀ == 0 && w.c₁ == 0 then 2 else 3

/-- `v·w` by the weight's kind `m` (`fmul v w` when `m = wKind w`, without its test). -/
@[inline] def wmul (m : ℕ) (v w : FE) : FE :=
  if m == 0 then FE.smulBase w.c₀ v else if m == 1 then mulY (FE.smulBase w.c₁ v)
  else if m == 2 then mulY (mulY (FE.smulBase w.c₂ v)) else v * w

/-- The proof-side twin of `wmul` over a value ring (S2GT-W). -/
@[inline] def wmulG (m : ℕ) (v : 𝔽) (w : FE) : 𝔽 :=
  if m == 0 then KRing.ofE (FE.ofK w.c₀) * v else if m == 1 then KRing.ofE FE.y * (KRing.ofE (FE.ofK w.c₁) * v)
  else if m == 2 then KRing.ofE FE.y * (KRing.ofE FE.y * (KRing.ofE (FE.ofK w.c₂) * v)) else v * KRing.ofE w

/-- **Fused code**: instruction `ins[k] = op + 16·m + 2^6·a + 2^26·b + 2^46·w` (flat indices `a, b < 2^20`,
weight kind `m < 4`, weight index `w < 2^17` into `ws`; an emitted state is `b + 2^20·w`). `op`:
`0` open; `1` open with the leaf `F[a]`; `2` open with the leaf `F[a]·ws[w]`; `3` close times `F[a]`;
`4` close and emit; `5` the leaf `F[a]`; `6` the leaf `F[a]·ws[w]`; `7` the product `F[a]·F[b]` (an open, a leaf
and a keyed close); `8` `F[a]·(F[b]·ws[w])`; `9` close with no key. -/
structure FCode where
  /-- The packed instructions. -/
  ins : Array ℕ
  /-- The weights (those of the `Code`). -/
  ws : Array FE
  deriving Inhabited

/-- An instruction. -/
@[inline] def pkI (op m a b w : ℕ) : ℕ := op + 16 * m + 2 ^ 6 * a + 2 ^ 26 * b + 2 ^ 46 * w

/-- **Run fused code** on the flat tables (as `runCode`: the outer sum and the emitted pairs). -/
def runF (F : Array FE) (c : FCode) : FE × Array (ℕ × FE) := Id.run do
  let mut top : FE := 0
  let mut st : Array FE := Array.mkEmpty 8
  let mut em : Array (ℕ × FE) := #[]
  for k in [0:c.ins.size] do
    let n := c.ins.getD k 0
    let op := n &&& 15
    let a := F.getD ((n >>> 6) &&& 0xFFFFF) 0
    if op == 7 then
      top := top + mulI a (F.getD ((n >>> 26) &&& 0xFFFFF) 0)
    else if op == 5 then
      top := top + a
    else if op == 6 then
      top := top + wmul ((n >>> 4) &&& 3) a (c.ws.getD (n >>> 46) 1)
    else if op == 3 then
      top := st.getD (st.size - 1) 0 + mulI a top
      st := st.pop
    else if op == 1 then
      st := st.push top
      top := a
    else if op == 0 then
      st := st.push top
      top := 0
    else if op == 8 then
      top := top + mulI a (wmul ((n >>> 4) &&& 3) (F.getD ((n >>> 26) &&& 0xFFFFF) 0) (c.ws.getD (n >>> 46) 1))
    else if op == 4 then
      em := em.push (n >>> 26, top)
      top := st.getD (st.size - 1) 0
      st := st.pop
    else if op == 2 then
      st := st.push top
      top := wmul ((n >>> 4) &&& 3) a (c.ws.getD (n >>> 46) 1)
    else
      top := st.getD (st.size - 1) 0 + top
      st := st.pop
  return (top, em)

/-- The proof-side twin of `runF` over a value ring (S2GT-W). -/
def runFG (F : Array 𝔽) (c : FCode) : 𝔽 × Array (ℕ × 𝔽) := Id.run do
  let mut top : 𝔽 := 0
  let mut st : Array 𝔽 := Array.mkEmpty 8
  let mut em : Array (ℕ × 𝔽) := #[]
  for k in [0:c.ins.size] do
    let n := c.ins.getD k 0
    let op := n &&& 15
    let a := F.getD ((n >>> 6) &&& 0xFFFFF) 0
    if op == 7 then
      top := top + a * (F.getD ((n >>> 26) &&& 0xFFFFF) 0)
    else if op == 5 then
      top := top + a
    else if op == 6 then
      top := top + wmulG ((n >>> 4) &&& 3) a (c.ws.getD (n >>> 46) 1)
    else if op == 3 then
      top := st.getD (st.size - 1) 0 + a * top
      st := st.pop
    else if op == 1 then
      st := st.push top
      top := a
    else if op == 0 then
      st := st.push top
      top := 0
    else if op == 8 then
      top := top + a * (wmulG ((n >>> 4) &&& 3) (F.getD ((n >>> 26) &&& 0xFFFFF) 0) (c.ws.getD (n >>> 46) 1))
    else if op == 4 then
      em := em.push (n >>> 26, top)
      top := st.getD (st.size - 1) 0
      st := st.pop
    else if op == 2 then
      st := st.push top
      top := wmulG ((n >>> 4) &&& 3) a (c.ws.getD (n >>> 46) 1)
    else
      top := st.getD (st.size - 1) 0 + top
      st := st.pop
  return (top, em)

/-- The flat index of key `(t, i)` when it is in range (`t` a table, `i` below its size, both packable). -/
def flatIx (rs : Array TRec) (offs : Array ℕ) (t i : ℕ) : Option ℕ :=
  if t < rs.size ∧ i < (rs.getD t .one).size ∧ offs.getD t 0 + i < 2 ^ 20 then some (offs.getD t 0 + i)
  else none

/-- The fused instructions of a code's instruction list `(op, ta, ix, wi)`, appended to `acc` (tail-recursive);
`none` if an index is out of range or an instruction unknown. -/
def fuseL (rs : Array TRec) (offs : Array ℕ) (ws : Array FE) (acc : Array ℕ) :
    List (ℕ × ℕ × ℕ × ℕ) → Option (Array ℕ)
  | [] => some acc
  | (0, _, _, _) :: (2, t, i, w) :: (1, t', i', _) :: rest =>
    match flatIx rs offs t i, (if t' == 0 then some 0 else flatIx rs offs t' i') with
    | some b, some a =>
      if !(w < ws.size ∧ w < 2 ^ 17) then none
      else if t' == 0 then
        fuseL rs offs ws (acc.push (if w == 0 then pkI 5 0 b 0 0 else pkI 6 (wKind (ws.getD w 1)) b 0 w)) rest
      else
        fuseL rs offs ws (acc.push (if w == 0 then pkI 7 0 a b 0 else pkI 8 (wKind (ws.getD w 1)) a b w)) rest
    | _, _ => none
  | (0, _, _, _) :: (2, t, i, w) :: rest =>
    match flatIx rs offs t i with
    | some b =>
      if !(w < ws.size ∧ w < 2 ^ 17) then none
      else fuseL rs offs ws (acc.push (if w == 0 then pkI 1 0 b 0 0 else pkI 2 (wKind (ws.getD w 1)) b 0 w)) rest
    | none => none
  | (0, _, _, _) :: rest => fuseL rs offs ws (acc.push (pkI 0 0 0 0 0)) rest
  | (1, t, i, _) :: rest =>
    if t == 0 then fuseL rs offs ws (acc.push (pkI 9 0 0 0 0)) rest
    else match flatIx rs offs t i with
      | some a => fuseL rs offs ws (acc.push (pkI 3 0 a 0 0)) rest
      | none => none
  | (2, t, i, w) :: rest =>
    match flatIx rs offs t i with
    | some b =>
      if !(w < ws.size ∧ w < 2 ^ 17) then none
      else fuseL rs offs ws (acc.push (if w == 0 then pkI 5 0 b 0 0 else pkI 6 (wKind (ws.getD w 1)) b 0 w)) rest
    | none => none
  | (3, _, i, _) :: rest =>
    if i < 2 ^ 37 then fuseL rs offs ws (acc.push (pkI 4 0 0 (i % 2 ^ 20) (i / 2 ^ 20))) rest else none
  | _ :: _ => none

/-- A code's instruction list. -/
def Code.insts (c : Code) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range c.op.size).map fun k ↦ (c.op.getD k 0, c.ta.getD k 0, c.ix.getD k 0, c.wi.getD k 0)

/-- **Fuse a code** over the recipes `rs` (`none` if an index is out of range). -/
def fuse (rs : Array TRec) (c : Code) : Option FCode :=
  (fuseL rs (tabOffs rs) c.ws (Array.mkEmpty c.op.size) c.insts).map fun ins ↦ ⟨ins, c.ws⟩

-- **The fused code computes the code**: `runF_fuse` (LA2, below): `fuse rs c = some fc → runF (flatTabs rs T) fc =
-- runCode T c`, for any tables `T`.

/-- One fused instruction of `runF` (flat tables `F`, weights `W`). -/
def fuse_fstep (F : Array 𝔽) (W : Array FE) (s : 𝔽 × Array 𝔽 × Array (ℕ × 𝔽)) (n : ℕ) :
    𝔽 × Array 𝔽 × Array (ℕ × 𝔽) :=
  let a := F.getD ((n >>> 6) &&& 0xFFFFF) 0
  if n &&& 15 == 7 then (s.1 + a * (F.getD ((n >>> 26) &&& 0xFFFFF) 0), s.2.1, s.2.2)
  else if n &&& 15 == 5 then (s.1 + a, s.2.1, s.2.2)
  else if n &&& 15 == 6 then (s.1 + wmulG ((n >>> 4) &&& 3) a (W.getD (n >>> 46) 1), s.2.1, s.2.2)
  else if n &&& 15 == 3 then (s.2.1.getD (s.2.1.size - 1) 0 + a * s.1, s.2.1.pop, s.2.2)
  else if n &&& 15 == 1 then (a, s.2.1.push s.1, s.2.2)
  else if n &&& 15 == 0 then (0, s.2.1.push s.1, s.2.2)
  else if n &&& 15 == 8 then
    (s.1 + a * (wmulG ((n >>> 4) &&& 3) (F.getD ((n >>> 26) &&& 0xFFFFF) 0) (W.getD (n >>> 46) 1)),
      s.2.1, s.2.2)
  else if n &&& 15 == 4 then (s.2.1.getD (s.2.1.size - 1) 0, s.2.1.pop, s.2.2.push (n >>> 26, s.1))
  else if n &&& 15 == 2 then (wmulG ((n >>> 4) &&& 3) a (W.getD (n >>> 46) 1), s.2.1.push s.1, s.2.2)
  else (s.2.1.getD (s.2.1.size - 1) 0 + s.1, s.2.1.pop, s.2.2)

theorem fuse_and_mask (x n : ℕ) (k : ℕ) (hk : k = 2 ^ n - 1) : x &&& k = x % 2 ^ n := by
  subst hk; exact Nat.and_two_pow_sub_one_eq_mod x n

theorem fuse_pk_op (op m a b w : ℕ) (hop : op < 16) : pkI op m a b w &&& 15 = op := by
  rw [fuse_and_mask _ 4 15 rfl, pkI]; (clear * - op m a b w hop; omega)

theorem fuse_pk_m (op m a b w : ℕ) (hop : op < 16) (hm : m < 4) : (pkI op m a b w >>> 4) &&& 3 = m := by
  rw [fuse_and_mask _ 2 3 rfl, Nat.shiftRight_eq_div_pow, pkI]; (clear * - op m a b w hop hm; omega)

theorem fuse_pk_a (op m a b w : ℕ) (hop : op < 16) (hm : m < 4) (ha : a < 2 ^ 20) :
    (pkI op m a b w >>> 6) &&& 0xFFFFF = a := by
  rw [fuse_and_mask _ 20 0xFFFFF rfl, Nat.shiftRight_eq_div_pow, pkI]; (clear * - op m a b w hop hm ha; omega)

theorem fuse_pk_hi (op m a b w : ℕ) (hop : op < 16) (hm : m < 4) (ha : a < 2 ^ 20) :
    pkI op m a b w >>> 26 = b + 2 ^ 20 * w := by
  rw [Nat.shiftRight_eq_div_pow, pkI]; (clear * - op m a b w hop hm ha; omega)

theorem fuse_pk_w (op m a b w : ℕ) (hop : op < 16) (hm : m < 4) (ha : a < 2 ^ 20) (hb : b < 2 ^ 20) :
    pkI op m a b w >>> 46 = w := by
  rw [Nat.shiftRight_eq_div_pow, pkI]; (clear * - op m a b w hop hm ha hb; omega)

theorem fuse_wKind_lt (w : FE) : wKind w < 4 := by
  unfold wKind; split_ifs <;> (clear * -; omega)

/-- `c·y = (0, c, 0)` in `E3`. -/
theorem fuse_fe_y1 (c : FK) : (⟨0, c, 0⟩ : FE) = FE.ofK c * FE.y := by
  apply FE.toExt3_injective
  rw [FE.toExt3_mul, FE.toExt3_ofK, FE.toExt3_eq, FE.toExt3_eq FE.y]
  simp only [FE.y, FK.toBF64_zero, FK.toBF64_one, map_zero, map_one]; ring

/-- `c·y² = (0, 0, c)` in `E3`. -/
theorem fuse_fe_y2 (c : FK) : (⟨0, 0, c⟩ : FE) = FE.ofK c * (FE.y * FE.y) := by
  apply FE.toExt3_injective
  rw [FE.toExt3_mul, FE.toExt3_mul, FE.toExt3_ofK, FE.toExt3_eq, FE.toExt3_eq FE.y]
  simp only [FE.y, FK.toBF64_zero, FK.toBF64_one, map_zero, map_one]; ring

/-- `c = (c, 0, 0)` in `E3`. -/
theorem fuse_fe_y0 (c : FK) : (⟨c, 0, 0⟩ : FE) = FE.ofK c := rfl

theorem fuse_wmulG (v : 𝔽) (w : FE) : wmulG (wKind w) v w = v * KRing.ofE w := by
  obtain ⟨w0, w1, w2⟩ := w
  unfold wKind
  dsimp only
  by_cases h1 : (w1 == 0 && w2 == 0) = true
  · rw [if_pos h1]
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    show KRing.ofE (FE.ofK w0) * v = v * KRing.ofE ⟨w0, 0, 0⟩
    rw [fuse_fe_y0, mul_comm]
  · rw [if_neg h1]
    by_cases h2 : (w0 == 0 && w2 == 0) = true
    · rw [if_pos h2]
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      show KRing.ofE FE.y * (KRing.ofE (FE.ofK w1) * v) = v * KRing.ofE ⟨0, w1, 0⟩
      rw [fuse_fe_y1, map_mul]; ring
    · rw [if_neg h2]
      by_cases h3 : (w0 == 0 && w1 == 0) = true
      · rw [if_pos h3]
        simp only [Bool.and_eq_true, beq_iff_eq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        show KRing.ofE FE.y * (KRing.ofE FE.y * (KRing.ofE (FE.ofK w2) * v)) = v * KRing.ofE ⟨0, 0, w2⟩
        rw [fuse_fe_y2, map_mul, map_mul]; ring
      · rw [if_neg h3]; rfl

/-- `fuse_fstep` on a decoded instruction (`op`, kind `m`, indices `a`, `b`, weight `w`). -/
def fuse_dstep (F : Array 𝔽) (W : Array FE) (s : 𝔽 × Array 𝔽 × Array (ℕ × 𝔽)) (op m a b w : ℕ) :
    𝔽 × Array 𝔽 × Array (ℕ × 𝔽) :=
  if op == 7 then (s.1 + F.getD a 0 * F.getD b 0, s.2.1, s.2.2)
  else if op == 5 then (s.1 + F.getD a 0, s.2.1, s.2.2)
  else if op == 6 then (s.1 + wmulG m (F.getD a 0) (W.getD w 1), s.2.1, s.2.2)
  else if op == 3 then (s.2.1.back?.getD 0 + F.getD a 0 * s.1, s.2.1.pop, s.2.2)
  else if op == 1 then (F.getD a 0, s.2.1.push s.1, s.2.2)
  else if op == 0 then (0, s.2.1.push s.1, s.2.2)
  else if op == 8 then (s.1 + F.getD a 0 * wmulG m (F.getD b 0) (W.getD w 1), s.2.1, s.2.2)
  else if op == 4 then (s.2.1.back?.getD 0, s.2.1.pop, s.2.2.push (b + 2 ^ 20 * w, s.1))
  else if op == 2 then (wmulG m (F.getD a 0) (W.getD w 1), s.2.1.push s.1, s.2.2)
  else (s.2.1.back?.getD 0 + s.1, s.2.1.pop, s.2.2)

theorem fuse_back (st : Array 𝔽) : st.getD (st.size - 1) 0 = st.back?.getD 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.back?]

theorem fuse_hi_mask (b w : ℕ) (hb : b < 2 ^ 20) : (b + 2 ^ 20 * w) &&& 1048575 = b := by
  rw [fuse_and_mask _ 20 1048575 rfl]; (clear * - b w hb; omega)

theorem fuse_fstep_pk (F : Array 𝔽) (W : Array FE) (s : 𝔽 × Array 𝔽 × Array (ℕ × 𝔽)) (op m a b w : ℕ) (hop : op < 16)
    (hm : m < 4) (ha : a < 2 ^ 20) (hb : b < 2 ^ 20) :
    fuse_fstep F W s (pkI op m a b w) = fuse_dstep F W s op m a b w := by
  unfold fuse_fstep fuse_dstep
  simp only [fuse_pk_op op m a b w hop, fuse_pk_m op m a b w hop hm, fuse_pk_a op m a b w hop hm ha,
    fuse_hi_mask b w hb, fuse_pk_w op m a b w hop hm ha hb, fuse_pk_hi op m a b w hop hm ha,
    fuse_back]

theorem fuse_term (e s : 𝔽) : (if (s == 1) = true then e else e * s) = e * s := by
  split_ifs with h
  · rw [beq_iff_eq.1 h, mul_one]
  · rfl

section

variable (F : Array 𝔽) (W : Array FE) (T : Array (Array 𝔽)) (s : 𝔽 × Array 𝔽 × Array (ℕ × 𝔽))

theorem fuse_hx_open (x y z : ℕ) :
    fuse_fstep F W s (pkI 0 0 0 0 0) = [(0, x, y, z)].foldl (code_step T W) s := by
  rw [fuse_fstep_pk F W s 0 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [fuse_dstep, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, List.foldl_cons, code_step, List.foldl_nil]

theorem fuse_hx_close0 (t i z : ℕ) (ht : (t == 0) = true) :
    fuse_fstep F W s (pkI 9 0 0 0 0) = [(1, t, i, z)].foldl (code_step T W) s := by
  rw [fuse_fstep_pk F W s 9 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  simp only [fuse_dstep, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, List.foldl_cons, code_step, ht, List.foldl_nil]

theorem fuse_hx_close (t i z a : ℕ) (ht : ¬ (t == 0) = true) (ha : a < 2 ^ 20)
    (hv : F.getD a 0 = (T.getD t #[]).getD i 0) :
    fuse_fstep F W s (pkI 3 0 a 0 0) = [(1, t, i, z)].foldl (code_step T W) s := by
  rw [fuse_fstep_pk F W s 3 0 a 0 0 (by norm_num) (by norm_num) ha (by norm_num)]
  simp only [fuse_dstep, code_step, List.foldl_cons, List.foldl_nil]
  simp only [ht, fuse_term, hv]
  simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Array.getD_eq_getD_getElem?]

theorem fuse_hx_emit (x i z : ℕ) :
    fuse_fstep F W s (pkI 4 0 0 (i % 2 ^ 20) (i / 2 ^ 20)) = [(3, x, i, z)].foldl (code_step T W) s := by
  rw [fuse_fstep_pk F W s 4 0 0 _ _ (by norm_num) (by norm_num) (by norm_num) (Nat.mod_lt _ (by norm_num))]
  simp only [fuse_dstep, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Nat.reducePow, Nat.mod_add_div, List.foldl_cons, code_step, List.foldl_nil]

theorem fuse_hx_leaf (t i w b : ℕ) (hb : b < 2 ^ 20) (hv : F.getD b 0 = (T.getD t #[]).getD i 0) :
    fuse_fstep F W s (if (w == 0) = true then pkI 5 0 b 0 0 else pkI 6 (wKind (W.getD w 1)) b 0 w) =
      [(2, t, i, w)].foldl (code_step T W) s := by
  by_cases hw : w = 0
  · subst hw
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [fuse_fstep_pk F W s 5 0 b 0 0 (by norm_num) (by norm_num) hb (by norm_num)]
    simp only [fuse_dstep, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, hv, Array.getD_eq_getD_getElem?, Prod.mk.eta, List.foldl_cons, code_step, List.foldl_nil]
  · have hw' : (w == 0) = false := by simpa only [beq_eq_false_iff_ne, ne_eq] using hw
    simp only [hw', Bool.false_eq_true, ↓reduceIte]
    rw [fuse_fstep_pk F W s 6 _ b 0 w (by norm_num) (fuse_wKind_lt _) hb (by norm_num)]
    simp only [fuse_dstep, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Array.getD_eq_getD_getElem?, hv, fuse_wmulG, Prod.mk.eta, List.foldl_cons, code_step, beq_iff_eq, hw, List.foldl_nil]

theorem fuse_hx_open1 (x y z t i w b : ℕ) (hb : b < 2 ^ 20) (hv : F.getD b 0 = (T.getD t #[]).getD i 0) :
    fuse_fstep F W s (if (w == 0) = true then pkI 1 0 b 0 0 else pkI 2 (wKind (W.getD w 1)) b 0 w) =
      [(0, x, y, z), (2, t, i, w)].foldl (code_step T W) s := by
  by_cases hw : w = 0
  · subst hw
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [fuse_fstep_pk F W s 1 0 b 0 0 (by norm_num) (by norm_num) hb (by norm_num)]
    simp only [fuse_dstep, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, hv, Array.getD_eq_getD_getElem?, List.foldl_cons, code_step, zero_add, List.foldl_nil]
  · have hw' : (w == 0) = false := by simpa only [beq_eq_false_iff_ne, ne_eq] using hw
    simp only [hw', Bool.false_eq_true, ↓reduceIte]
    rw [fuse_fstep_pk F W s 2 _ b 0 w (by norm_num) (fuse_wKind_lt _) hb (by norm_num)]
    simp only [fuse_dstep, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Array.getD_eq_getD_getElem?, hv, fuse_wmulG, List.foldl_cons, code_step, beq_iff_eq, hw, zero_add, List.foldl_nil]

theorem fuse_hx_leafc (x y z t i w t' i' z' b : ℕ) (ht : (t' == 0) = true) (hb : b < 2 ^ 20)
    (hv : F.getD b 0 = (T.getD t #[]).getD i 0) :
    fuse_fstep F W s (if (w == 0) = true then pkI 5 0 b 0 0 else pkI 6 (wKind (W.getD w 1)) b 0 w) =
      [(0, x, y, z), (2, t, i, w), (1, t', i', z')].foldl (code_step T W) s := by
  by_cases hw : w = 0
  · subst hw
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [fuse_fstep_pk F W s 5 0 b 0 0 (by norm_num) (by norm_num) hb (by norm_num)]
    simp only [fuse_dstep, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, hv, Array.getD_eq_getD_getElem?, Prod.mk.eta, List.foldl_cons, code_step, zero_add, Array.back?_push, Option.getD_some, ht, Array.pop_push, List.foldl_nil]
  · have hw' : (w == 0) = false := by simpa only [beq_eq_false_iff_ne, ne_eq] using hw
    simp only [hw', Bool.false_eq_true, ↓reduceIte]
    rw [fuse_fstep_pk F W s 6 _ b 0 w (by norm_num) (fuse_wKind_lt _) hb (by norm_num)]
    simp only [fuse_dstep, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Array.getD_eq_getD_getElem?, hv, fuse_wmulG, Prod.mk.eta, List.foldl_cons, code_step, beq_iff_eq, hw, zero_add, Array.back?_push, Option.getD_some, ht, Array.pop_push, List.foldl_nil]

theorem fuse_hx_prod (x y z t i w t' i' z' a b : ℕ) (ht : ¬ (t' == 0) = true) (ha : a < 2 ^ 20) (hb : b < 2 ^ 20)
    (hva : F.getD a 0 = (T.getD t' #[]).getD i' 0) (hv : F.getD b 0 = (T.getD t #[]).getD i 0) :
    fuse_fstep F W s (if (w == 0) = true then pkI 7 0 a b 0 else pkI 8 (wKind (W.getD w 1)) a b w) =
      [(0, x, y, z), (2, t, i, w), (1, t', i', z')].foldl (code_step T W) s := by
  by_cases hw : w = 0
  · subst hw
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [fuse_fstep_pk F W s 7 0 a b 0 (by norm_num) (by norm_num) ha hb]
    simp only [fuse_dstep, code_step, List.foldl_cons, List.foldl_nil]
    simp only [ht, fuse_term, hv, hva]
    simp only [BEq.rfl, ↓reduceIte, Array.getD_eq_getD_getElem?, Prod.mk.eta, Nat.reduceBEq, Bool.false_eq_true, zero_add, Array.back?_push, Option.getD_some, Array.pop_push]
  · have hw' : (w == 0) = false := by simpa only [beq_eq_false_iff_ne, ne_eq] using hw
    simp only [hw', Bool.false_eq_true, ↓reduceIte]
    rw [fuse_fstep_pk F W s 8 _ a b w (by norm_num) (fuse_wKind_lt _) ha hb]
    simp only [fuse_dstep, code_step, List.foldl_cons, List.foldl_nil]
    simp only [ht, Bool.false_eq_true, ↓reduceIte, fuse_term]
    simp only [hv, hva, fuse_wmulG]
    simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Array.getD_eq_getD_getElem?, Prod.mk.eta, beq_iff_eq, hw, zero_add, Array.back?_push, Option.getD_some, Array.pop_push]

end

theorem fuse_ite_pure {β : Type} (p : Prop) [Decidable p] (a b : β) :
    (if p then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if p then a else b)) := by
  split <;> rfl

theorem fuse_runF (F : Array 𝔽) (c : FCode) :
    runFG F c = ((c.ins.toList.foldl (fuse_fstep F c.ws) (0, #[], #[])).1,
      (c.ins.toList.foldl (fuse_fstep F c.ws) (0, #[], #[])).2.2) := by
  unfold runFG
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', code_forIn_list _ _ _
    (fun s k ↦ fuse_fstep F c.ws s (c.ins.getD k 0))
    (by intro k s; simp only [fuse_fstep, fuse_ite_pure])]
  have : c.ins.toList = (List.range' 0 c.ins.size).map (fun k ↦ c.ins.getD k 0) := by
    apply List.ext_getElem
    · simp only [Array.length_toList, Array.getD_eq_getD_getElem?, List.length_map, List.length_range']
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range', Array.getElem_toList]
      simp only [Array.length_toList] at h1
      simp only [Array.getD, one_mul, zero_add, h1, ↓reduceDIte, Array.getInternal_eq_getElem]
  simp only [this, List.foldl_map, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem fuse_foldl_push {α : Type} (g : ℕ → α) (L : List ℕ) : ∀ (b : Array α),
    (L.foldl (fun b i ↦ b.push (g i)) b).toList = b.toList ++ L.map g := by
  induction L with
  | nil => intro b; simp only [List.foldl_nil, List.map_nil, List.append_nil]
  | cons x L ih => intro b; simp only [List.foldl_cons]; rw [ih]; simp only [Array.toList_push, List.append_assoc, List.cons_append, List.nil_append, List.map_cons]

theorem fuse_foldl_rows {α : Type} (g : ℕ → ℕ → α) (sz : ℕ → ℕ) (L : List ℕ) : ∀ (b : Array α),
    (L.foldl (fun b t ↦ (List.range' 0 (sz t)).foldl (fun b i ↦ b.push (g t i)) b) b).toList =
      b.toList ++ L.flatMap (fun t ↦ (List.range (sz t)).map (g t)) := by
  induction L with
  | nil => intro b; simp only [List.foldl_push_eq_append, List.foldl_nil, List.flatMap_nil, List.append_nil]
  | cons x L ih =>
    intro b; simp only [List.foldl_cons]; rw [ih, fuse_foldl_push]; simp only [List.range_eq_range', List.append_assoc, List.flatMap_cons]

omit [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] in
theorem fuse_flatTabs (rs : Array TRec) (T : Array (Array 𝔽)) :
    (flatTabsG rs T).toList = (List.range rs.size).flatMap
      (fun t ↦ (List.range (rs.getD t .one).size).map fun i ↦ (T.getD t #[]).getD i 0) := by
  unfold flatTabsG
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, pure_bind, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [show ∀ x : Array 𝔽, (pure x : Id (Array 𝔽)) = x from fun _ ↦ rfl,
    fuse_foldl_rows (fun t i ↦ (T.getD t #[]).getD i 0) (fun t ↦ (rs.getD t .one).size)]
  simp only [Array.getD_eq_getD_getElem?, Array.mkEmpty_eq, Array.toList_empty, List.range_eq_range', List.nil_append]

/-- `Σ_{u<t} (rs[u]).size`. -/
def fuse_off (rs : Array TRec) (t : ℕ) : ℕ := ((List.range t).map fun u ↦ (rs.getD u .one).size).sum

theorem fuse_off_succ (rs : Array TRec) (t : ℕ) : fuse_off rs (t + 1) = fuse_off rs t + (rs.getD t .one).size := by
  simp only [fuse_off, Array.getD_eq_getD_getElem?, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero, Nat.add_left_cancel_iff]

theorem fuse_off_mono (rs : Array TRec) (t n : ℕ) (h : t ≤ n) : fuse_off rs t ≤ fuse_off rs n := by
  induction n with
  | zero => simp only [nonpos_iff_eq_zero] at h; subst h; exact le_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge t (n + 1) with h1 | h1
    · rw [fuse_off_succ]; have := ih (by (clear * - h1; omega)); (clear * - this; omega)
    · rw [show t = n + 1 by (clear * - h h1; omega)]

theorem fuse_rows_get {α : Type} (rs : Array TRec) (g : ℕ → ℕ → α) (n t i : ℕ) (ht : t < n)
    (hi : i < (rs.getD t .one).size) :
    ((List.range n).flatMap (fun t ↦ (List.range (rs.getD t .one).size).map (g t)))[fuse_off rs t + i]? =
      some (g t i) := by
  have hlen : ∀ n, ((List.range n).flatMap (fun t ↦ (List.range (rs.getD t .one).size).map (g t))).length =
      fuse_off rs n := by
    intro n
    induction n with
    | zero => simp only [Array.getD_eq_getD_getElem?, List.range_zero, List.flatMap_nil, List.length_nil, fuse_off, List.map_nil, List.sum_nil]
    | succ n ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih, fuse_off_succ]; simp only [Array.getD_eq_getD_getElem?, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map, List.length_range, Nat.add_left_cancel_iff]
  induction n with
  | zero => (clear * - ht; omega)
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge t n with h1 | h1
    · have := fuse_off_mono rs (t + 1) n h1
      rw [fuse_off_succ] at this
      rw [List.getElem?_append_left (by rw [hlen]; (clear * - hi this; omega)), ih h1]
    · have h2 : t = n := by (clear * - ht h1; omega)
      subst h2
      rw [List.getElem?_append_right (by rw [hlen]; (clear * -; (clear * - rs t i; omega))), hlen, Nat.add_sub_cancel_left]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getElem?_map, List.getElem?_range hi]
      rfl

omit [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] in
theorem fuse_flat_get (rs : Array TRec) (T : Array (Array 𝔽)) (t i : ℕ) (ht : t < rs.size)
    (hi : i < (rs.getD t .one).size) :
    (flatTabsG rs T).getD (fuse_off rs t + i) 0 = (T.getD t #[]).getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, fuse_flatTabs,
    fuse_rows_get rs (fun t i ↦ (T.getD t #[]).getD i 0) _ t i ht hi]
  rfl

/-- `tabOffs`'s step. -/
def fuse_ostep (acc : Array ℕ) (r : TRec) : Array ℕ := acc.push (acc.getD (acc.size - 1) 0 + r.size)

theorem fuse_ofold_pre (l : List TRec) : ∀ (acc : Array ℕ) (j : ℕ), j < acc.size →
    (l.foldl fuse_ostep acc).getD j 0 = acc.getD j 0 := by
  induction l with
  | nil => intro acc j _; simp only [List.foldl_nil, Array.getD_eq_getD_getElem?]
  | cons r l ih =>
    intro acc j hj
    simp only [List.foldl_cons]
    rw [ih _ _ (by simp only [fuse_ostep, Array.getD_eq_getD_getElem?, Array.size_push, Order.lt_add_one_iff]; (clear * - hj; omega))]
    simp only [fuse_ostep, Array.getD_eq_getD_getElem?, Array.getElem?_push, show j ≠ acc.size by (clear * - hj; omega), ↓reduceIte]

theorem fuse_ofold_get (l : List TRec) : ∀ (acc : Array ℕ), 0 < acc.size → ∀ k ≤ l.length,
    (l.foldl fuse_ostep acc).getD (acc.size - 1 + k) 0 =
      acc.getD (acc.size - 1) 0 + ((l.take k).map TRec.size).sum := by
  induction l with
  | nil => intro acc _ k hk; simp only [List.length_nil, nonpos_iff_eq_zero] at hk; subst hk; simp only [List.foldl_nil, add_zero, Array.getD_eq_getD_getElem?, List.take_nil, List.map_nil, List.sum_nil]
  | cons r l ih =>
    intro acc h0 k hk
    rcases k with _ | k
    · simp only [Nat.add_zero, List.take_zero, List.map_nil, List.sum_nil]
      exact fuse_ofold_pre _ _ _ (by (clear * - h0; omega))
    · simp only [List.foldl_cons]
      have h1 := ih (fuse_ostep acc r) (by simp only [fuse_ostep, Array.getD_eq_getD_getElem?, Array.size_push, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le]) k (by simp only [List.length_cons, add_le_add_iff_right] at hk; (clear * - hk; omega))
      have hs : (fuse_ostep acc r).size - 1 = acc.size - 1 + 1 := by simp only [fuse_ostep, Array.getD_eq_getD_getElem?, Array.size_push, add_tsub_cancel_right]; (clear * - h0; omega)
      rw [hs, show acc.size - 1 + 1 + k = acc.size - 1 + (k + 1) by (clear * -; (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done))] at h1
      rw [h1]
      have hg : (fuse_ostep acc r).getD (acc.size - 1 + 1) 0 = acc.getD (acc.size - 1) 0 + r.size := by
        simp only [fuse_ostep, Array.getD_eq_getD_getElem?, show acc.size - 1 + 1 = acc.size by (clear * - h0; omega), Array.size_push, lt_add_iff_pos_right, Order.lt_one_iff, getElem?_pos, Array.getElem_push_eq, Option.getD_some, Nat.add_left_cancel_iff]
      rw [hg]
      simp only [Array.getD_eq_getD_getElem?, List.map_take, List.take_succ_cons, List.map_cons, List.sum_cons]
      ring

theorem fuse_take_sum (rs : Array TRec) (t : ℕ) (ht : t ≤ rs.size) :
    ((rs.toList.take t).map TRec.size).sum = fuse_off rs t := by
  induction t with
  | zero => simp only [List.take_zero, List.map_nil, List.sum_nil, fuse_off, Array.getD_eq_getD_getElem?, List.range_zero]
  | succ t ih =>
    rw [fuse_off_succ, ← ih (by (clear * - ht; omega)), List.take_add_one, List.map_append, List.sum_append]
    simp only [List.map_take, Array.length_toList, show t < rs.size by (clear * - ht; omega), getElem?_pos, Array.getElem_toList, Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Array.getD_eq_getD_getElem?, Option.getD_some, Nat.add_left_cancel_iff]

theorem fuse_tabOffs (rs : Array TRec) (t : ℕ) (ht : t ≤ rs.size) : (tabOffs rs).getD t 0 = fuse_off rs t := by
  have h := fuse_ofold_get rs.toList #[0] (by simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add, Order.lt_one_iff]) t (by simpa only [Array.length_toList] using ht)
  have e : tabOffs rs = rs.toList.foldl fuse_ostep #[0] := by
    rw [tabOffs, ← Array.foldl_toList]; rfl
  rw [e]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.sub_self] at h
  rw [h, fuse_take_sum rs t ht]
  simp only [Array.getD_eq_getD_getElem?, List.size_toArray, List.length_cons, List.length_nil, zero_add, Order.lt_one_iff, getElem?_pos, List.getElem_toArray, List.getElem_cons_zero, Option.getD_some]

theorem fuse_flatIx (rs : Array TRec) (T : Array (Array 𝔽)) (t i b : ℕ)
    (h : flatIx rs (tabOffs rs) t i = some b) :
    b < 2 ^ 20 ∧ (flatTabsG rs T).getD b 0 = (T.getD t #[]).getD i 0 := by
  unfold flatIx at h
  split_ifs at h with hc
  obtain ⟨h1, h2, h3⟩ := hc
  cases h
  rw [fuse_tabOffs rs t h1.le] at h3 ⊢
  exact ⟨h3, fuse_flat_get rs T t i h1 h2⟩

theorem fuse_push (F : Array 𝔽) (W : Array FE) (T : Array (Array 𝔽)) (x : ℕ) (L rest : List (ℕ × ℕ × ℕ × ℕ))
    (acc out : Array ℕ)
    (ih : ∀ s, out.toList.foldl (fuse_fstep F W) s =
      rest.foldl (code_step T W) ((acc.push x).toList.foldl (fuse_fstep F W) s))
    (hx : ∀ s, fuse_fstep F W s x = L.foldl (code_step T W) s) :
    ∀ s, out.toList.foldl (fuse_fstep F W) s =
      (L ++ rest).foldl (code_step T W) (acc.toList.foldl (fuse_fstep F W) s) := by
  intro s
  rw [ih, Array.toList_push, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil, hx]

theorem fuse_sim (rs : Array TRec) (T : Array (Array 𝔽)) (ws : Array FE) (acc : Array ℕ)
    (l : List (ℕ × ℕ × ℕ × ℕ)) :
    ∀ out, fuseL rs (tabOffs rs) ws acc l = some out → ∀ s,
      out.toList.foldl (fuse_fstep (flatTabsG rs T) ws) s =
        l.foldl (code_step T ws) (acc.toList.foldl (fuse_fstep (flatTabsG rs T) ws) s) := by
  induction acc, l using fuseL.induct rs (tabOffs rs) ws with
  | case1 acc =>
    intro out h s; rw [fuseL.eq_1] at h; cases h; rfl
  | case2 acc fst fst_1 snd t i w t' i' snd_1 rest b a ha hb hw =>
    intro out h; rw [fuseL.eq_2, hb, ha] at h; simp only [hw, ↓reduceIte] at h; cases h
  | case3 acc fst fst_1 snd t i w t' i' snd_1 rest b a ha hb hw ht ih =>
    intro out h
    rw [fuseL.eq_2, hb, ha] at h
    simp only [hw, ht, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hb1, hb2⟩ := fuse_flatIx rs T t i b hb
    exact fuse_push _ _ T _ [(0, fst, fst_1, snd), (2, t, i, w), (1, t', i', snd_1)] rest acc out (ih out h)
      (fun s ↦ fuse_hx_leafc _ _ T s fst fst_1 snd t i w t' i' snd_1 b ht hb1 hb2)
  | case4 acc fst fst_1 snd t i w t' i' snd_1 rest b a ha hb hw ht ih =>
    intro out h
    rw [fuseL.eq_2, hb, ha] at h
    simp only [hw, ht, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hb1, hb2⟩ := fuse_flatIx rs T t i b hb
    simp only [ht, Bool.false_eq_true, ↓reduceIte] at ha
    obtain ⟨ha1, ha2⟩ := fuse_flatIx rs T t' i' a ha
    exact fuse_push _ _ T _ [(0, fst, fst_1, snd), (2, t, i, w), (1, t', i', snd_1)] rest acc out (ih out h)
      (fun s ↦ fuse_hx_prod _ _ T s fst fst_1 snd t i w t' i' snd_1 a b ht ha1 hb1 ha2 hb2)
  | case5 acc fst fst_1 snd t i w t' i' snd_1 rest hne =>
    intro out h
    rw [fuseL.eq_2] at h
    split at h
    · rename_i b a hb ha; exact (hne b a hb ha).elim
    · cases h
  | case6 acc fst fst_1 snd t i w rest hr b hb hw =>
    intro out h; rw [fuseL.eq_3 _ _ _ _ _ _ _ _ _ _ _ hr, hb] at h; simp only [hw, ↓reduceIte] at h; cases h
  | case7 acc fst fst_1 snd t i w rest hr b hb hw ih =>
    intro out h
    rw [fuseL.eq_3 _ _ _ _ _ _ _ _ _ _ _ hr, hb] at h
    simp only [hw, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hb1, hb2⟩ := fuse_flatIx rs T t i b hb
    exact fuse_push _ _ T _ [(0, fst, fst_1, snd), (2, t, i, w)] rest acc out (ih out h)
      (fun s ↦ fuse_hx_open1 _ _ T s fst fst_1 snd t i w b hb1 hb2)
  | case8 acc fst fst_1 snd t i w rest hr hb =>
    intro out h; rw [fuseL.eq_3 _ _ _ _ _ _ _ _ _ _ _ hr, hb] at h; cases h
  | case9 acc fst fst_1 snd rest h1 h2 ih =>
    intro out h
    rw [fuseL.eq_4 _ _ _ _ _ _ _ _ h1 h2] at h
    exact fuse_push _ _ T _ [(0, fst, fst_1, snd)] rest acc out (ih out h)
      (fun s ↦ fuse_hx_open _ _ T s fst fst_1 snd)
  | case10 acc t i snd rest ht ih =>
    intro out h
    rw [fuseL.eq_5] at h
    simp only [ht, ↓reduceIte] at h
    exact fuse_push _ _ T _ [(1, t, i, snd)] rest acc out (ih out h)
      (fun s ↦ fuse_hx_close0 _ _ T s t i snd ht)
  | case11 acc t i snd rest ht a ha ih =>
    intro out h
    rw [fuseL.eq_5] at h
    simp only [ht, Bool.false_eq_true, ↓reduceIte, ha] at h
    obtain ⟨ha1, ha2⟩ := fuse_flatIx rs T t i a ha
    exact fuse_push _ _ T _ [(1, t, i, snd)] rest acc out (ih out h)
      (fun s ↦ fuse_hx_close _ _ T s t i snd a ht ha1 ha2)
  | case12 acc t i snd rest ht ha =>
    intro out h
    rw [fuseL.eq_5] at h
    simp only [ht, Bool.false_eq_true, ↓reduceIte, ha] at h
    cases h
  | case13 acc t i w rest b hb hw =>
    intro out h; rw [fuseL.eq_6, hb] at h; simp only [hw, ↓reduceIte] at h; cases h
  | case14 acc t i w rest b hb hw ih =>
    intro out h
    rw [fuseL.eq_6, hb] at h
    simp only [hw, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hb1, hb2⟩ := fuse_flatIx rs T t i b hb
    exact fuse_push _ _ T _ [(2, t, i, w)] rest acc out (ih out h)
      (fun s ↦ fuse_hx_leaf _ _ T s t i w b hb1 hb2)
  | case15 acc t i w rest hb =>
    intro out h; rw [fuseL.eq_6, hb] at h; cases h
  | case16 acc fst i snd rest hi ih =>
    intro out h
    rw [fuseL.eq_7] at h
    simp only [hi, ↓reduceIte] at h
    exact fuse_push _ _ T _ [(3, fst, i, snd)] rest acc out (ih out h)
      (fun s ↦ fuse_hx_emit _ _ T s fst i snd)
  | case17 acc fst i snd rest hi =>
    intro out h; rw [fuseL.eq_7] at h; simp only [hi, ↓reduceIte] at h; cases h
  | case18 acc head tail h1 h2 h3 h4 h5 h6 =>
    intro out h; rw [fuseL.eq_8 _ _ _ _ _ _ h1 h2 h3 h4 h5 h6] at h; cases h

/-- **The fused code computes the code.** -/
theorem runF_fuse (rs : Array TRec) (T : Array (Array 𝔽)) (c : Code) (fc : FCode) (h : fuse rs c = some fc) :
    runFG (flatTabsG rs T) fc = runCodeG T c := by
  unfold fuse at h
  obtain ⟨ins, h1, rfl⟩ := Option.map_eq_some_iff.1 h
  have hs := fuse_sim rs T c.ws _ _ ins h1 (0, #[], #[])
  rw [fuse_runF, code_runCode]
  have hi : c.insts = code_instrs c := rfl
  rw [← hi]
  simp only at hs ⊢
  rw [hs]
  rfl

end L1

/-! ## The carry automaton (K3) -/

/-- **A carry-automaton pass**: `Σ_a atom_a · Σ_{j < 2^n} eq(r_x,xs, j) · Fin(s_a + R·j)` where `s_a` is atom
`a`'s level-0 key index (the initial state) and its other levels give its coefficient; `Fin(y)` is
`Π_{(t, bs) ∈ fin} T[t][pext (y ≫ n) bs]`, times the limb factor at `limbE` if set. -/
structure Pass where
  /-- The automaton's `x` bits (step `k` reads `r_x[xs[k]]` and `r_y[k]`). -/
  xs : Array ℕ
  /-- The stride. -/
  R : ℕ
  /-- The members, sorted by initial state (level 0: `(0, s)`). -/
  atoms : Array Atom
  /-- Their levels. -/
  depth : ℕ
  /-- The finish: the table and the bits (relative to bit `n`) of each `y` group past bit `n`. -/
  fin : Array (ℕ × List ℕ)
  /-- A merged `E` cell's limb bit, if any (its limb factor multiplies the pass). -/
  limbE : Option ℕ
  /-- The code of the initial states (`initCode atoms depth`). -/
  code : Code := default
  /-- Its fused form, if fused (B1-K2). -/
  fcode : Option FCode := none
  deriving Inhabited

/-- **One step of the automaton** on sorted states `(c, v)` (distinct `c`): state `c` at `x` bit `j ∈ {0, 1}`
emits `y` bit `(c + j·R) mod 2` and moves to `(c + j·R) / 2`, with weight `eq(r_x, j)·eq(r_y, bit)`. A target
`t` has up to two sources per `j` (`2t`, `2t + 1` after the shift). In characteristic 2 a source pair is one
product (`v + r_y·(v + v')`) and both halves meet in one more (`A + r_x·(A + B)`); a lone source is one product
with the step's precomputed weight `e[j][bit]`. About 1.5 products per state on dense windows, 2 on sparse
ones (never more than the direct two products per state). -/
def autoStep (R : ℕ) (rxk ryk : 𝔽) (st : Array (ℕ × 𝔽)) : Array (ℕ × 𝔽) := Id.run do
  let p := rxk * ryk
  -- e[j][b] = eq(r_x, j)·eq(r_y, b)
  let e00 := 1 - rxk - ryk + p
  let e01 := ryk - p
  let e10 := rxk - p
  let e11 := p
  -- the half sums of one half: `(t, val, kind)`, kind 0/1 a lone source at that bit (`val` raw), 2 a pair
  -- already weighted by `eq(r_y, ·)`
  let half (sh : ℕ) : Array (ℕ × 𝔽 × ℕ) := Id.run do
    let mut out : Array (ℕ × 𝔽 × ℕ) := Array.mkEmpty st.size
    let mut i := 0
    while i < st.size do
      let (c, v) := st.getD i (0, 0)
      let d := c + sh
      if d % 2 == 0 then
        let (c', v') := st.getD (i + 1) (0, 0)
        if i + 1 < st.size && c' == c + 1 then
          out := out.push (d / 2, v + ryk * (v + v'), 2)
          i := i + 2
        else
          out := out.push (d / 2, v, 0)
          i := i + 1
      else
        out := out.push (d / 2, v, 1)
        i := i + 1
    return out
  let as := half 0
  let bs := half R
  let wy (val : 𝔽) (k : ℕ) : 𝔽 := if k == 2 then val else if k == 0 then val - ryk * val else ryk * val
  let mut out : Array (ℕ × 𝔽) := Array.mkEmpty (as.size + bs.size)
  let mut i := 0
  let mut j := 0
  while i < as.size || j < bs.size do
    let (ta, va, ka) := as.getD i (0, 0, 0)
    let (tb, vb, kb) := bs.getD j (0, 0, 0)
    if j ≥ bs.size || (i < as.size && ta < tb) then
      out := out.push (ta, if ka == 2 then va - rxk * va else va * (if ka == 0 then e00 else e01))
      i := i + 1
    else if i ≥ as.size || tb < ta then
      out := out.push (tb, if kb == 2 then rxk * vb else vb * (if kb == 0 then e10 else e11))
      j := j + 1
    else
      if ka != 2 && kb != 2 then
        out := out.push (ta, va * (if ka == 0 then e00 else e01) + vb * (if kb == 0 then e10 else e11))
      else
        let A := wy va ka
        let B := wy vb kb
        out := out.push (ta, A + rxk * (A + B))
      i := i + 1
      j := j + 1
  return out

/-- `autoStep` on parallel arrays (states `cs`, values `vs`): the same sums, no tuple per state. -/
def autoStepP (R : ℕ) (rxk ryk : FE) (cs : Array ℕ) (vs : Array FE) : Array ℕ × Array FE := Id.run do
  let p := rxk * ryk
  let e00 := 1 - rxk - ryk + p
  let e01 := ryk - p
  let e10 := rxk - p
  let e11 := p
  let n := cs.size
  -- one half: targets, values, kinds (0/1 a lone source at that bit, raw; 2 a pair, `eq(r_y)`-weighted)
  let half (sh : ℕ) : Array ℕ × Array FE × Array ℕ := Id.run do
    let mut ts : Array ℕ := Array.mkEmpty n
    let mut xs : Array FE := Array.mkEmpty n
    let mut ks : Array ℕ := Array.mkEmpty n
    let mut i := 0
    while i < n do
      let c := cs.getD i 0
      let v := vs.getD i 0
      let d := c + sh
      if d % 2 == 0 then
        if i + 1 < n && cs.getD (i + 1) 0 == c + 1 then
          let v' := vs.getD (i + 1) 0
          ts := ts.push (d / 2); xs := xs.push (v + ryk * (v + v')); ks := ks.push 2
          i := i + 2
        else
          ts := ts.push (d / 2); xs := xs.push v; ks := ks.push 0
          i := i + 1
      else
        ts := ts.push (d / 2); xs := xs.push v; ks := ks.push 1
        i := i + 1
    return (ts, xs, ks)
  let (ta, va, ka) := half 0
  let (tb, vb, kb) := half R
  let wy (val : FE) (k : ℕ) : FE := if k == 2 then val else if k == 0 then val - ryk * val else ryk * val
  let mut oc : Array ℕ := Array.mkEmpty (ta.size + tb.size)
  let mut ov : Array FE := Array.mkEmpty (ta.size + tb.size)
  let mut i := 0
  let mut j := 0
  while i < ta.size || j < tb.size do
    let a := ta.getD i 0
    let b := tb.getD j 0
    if j ≥ tb.size || (i < ta.size && a < b) then
      let x := va.getD i 0
      let k := ka.getD i 0
      oc := oc.push a; ov := ov.push (if k == 2 then x - rxk * x else x * (if k == 0 then e00 else e01))
      i := i + 1
    else if i ≥ ta.size || b < a then
      let x := vb.getD j 0
      let k := kb.getD j 0
      oc := oc.push b; ov := ov.push (if k == 2 then rxk * x else x * (if k == 0 then e10 else e11))
      j := j + 1
    else
      let x := va.getD i 0
      let y := vb.getD j 0
      let k := ka.getD i 0
      let k' := kb.getD j 0
      oc := oc.push a
      if k != 2 && k' != 2 then
        ov := ov.push (x * (if k == 0 then e00 else e01) + y * (if k' == 0 then e10 else e11))
      else
        let A := wy x k
        let B := wy y k'
        ov := ov.push (A + rxk * (A + B))
      i := i + 1
      j := j + 1
  return (oc, ov)

/-- The proof-side twin of `autoStepP` over a value ring (S2GT-W). -/
def autoStepPG (R : ℕ) (rxk ryk : 𝔽) (cs : Array ℕ) (vs : Array 𝔽) : Array ℕ × Array 𝔽 := Id.run do
  let p := rxk * ryk
  let e00 := 1 - rxk - ryk + p
  let e01 := ryk - p
  let e10 := rxk - p
  let e11 := p
  let n := cs.size
  -- one half: targets, values, kinds (0/1 a lone source at that bit, raw; 2 a pair, `eq(r_y)`-weighted)
  let half (sh : ℕ) : Array ℕ × Array 𝔽 × Array ℕ := Id.run do
    let mut ts : Array ℕ := Array.mkEmpty n
    let mut xs : Array 𝔽 := Array.mkEmpty n
    let mut ks : Array ℕ := Array.mkEmpty n
    let mut i := 0
    while i < n do
      let c := cs.getD i 0
      let v := vs.getD i 0
      let d := c + sh
      if d % 2 == 0 then
        if i + 1 < n && cs.getD (i + 1) 0 == c + 1 then
          let v' := vs.getD (i + 1) 0
          ts := ts.push (d / 2); xs := xs.push (v + ryk * (v + v')); ks := ks.push 2
          i := i + 2
        else
          ts := ts.push (d / 2); xs := xs.push v; ks := ks.push 0
          i := i + 1
      else
        ts := ts.push (d / 2); xs := xs.push v; ks := ks.push 1
        i := i + 1
    return (ts, xs, ks)
  let (ta, va, ka) := half 0
  let (tb, vb, kb) := half R
  let wy (val : 𝔽) (k : ℕ) : 𝔽 := if k == 2 then val else if k == 0 then val - ryk * val else ryk * val
  let mut oc : Array ℕ := Array.mkEmpty (ta.size + tb.size)
  let mut ov : Array 𝔽 := Array.mkEmpty (ta.size + tb.size)
  let mut i := 0
  let mut j := 0
  while i < ta.size || j < tb.size do
    let a := ta.getD i 0
    let b := tb.getD j 0
    if j ≥ tb.size || (i < ta.size && a < b) then
      let x := va.getD i 0
      let k := ka.getD i 0
      oc := oc.push a; ov := ov.push (if k == 2 then x - rxk * x else x * (if k == 0 then e00 else e01))
      i := i + 1
    else if i ≥ ta.size || b < a then
      let x := vb.getD j 0
      let k := kb.getD j 0
      oc := oc.push b; ov := ov.push (if k == 2 then rxk * x else x * (if k == 0 then e10 else e11))
      j := j + 1
    else
      let x := va.getD i 0
      let y := vb.getD j 0
      let k := ka.getD i 0
      let k' := kb.getD j 0
      oc := oc.push a
      if k != 2 && k' != 2 then
        ov := ov.push (x * (if k == 0 then e00 else e01) + y * (if k' == 0 then e10 else e11))
      else
        let A := wy x k
        let B := wy y k'
        ov := ov.push (A + rxk * (A + B))
      i := i + 1
      j := j + 1
  return (oc, ov)

/-- The automaton over `n` steps from the sorted initial states. -/
def runAuto (P : Pt) (xs : Array ℕ) (R : ℕ) (st : Array (ℕ × FE)) : Array (ℕ × FE) := Id.run do
  let mut cs := st.map (·.1)
  let mut vs := st.map (·.2)
  for k in [0:xs.size] do
    let r := autoStepP R (P.rx.getD (xs.getD k 0) 0) (P.ry.getD k 0) cs vs
    cs := r.1
    vs := r.2
  return (Array.range cs.size).map fun i ↦ (cs.getD i 0, vs.getD i 0)

/-- The proof-side twin of `runAuto` over a value ring (S2GT-W). -/
def runAutoG (P : PtG 𝔽) (xs : Array ℕ) (R : ℕ) (st : Array (ℕ × 𝔽)) : Array (ℕ × 𝔽) := Id.run do
  let mut cs := st.map (·.1)
  let mut vs := st.map (·.2)
  for k in [0:xs.size] do
    let r := autoStepPG R (P.rx.getD (xs.getD k 0) 0) (P.ry.getD k 0) cs vs
    cs := r.1
    vs := r.2
  return (Array.range cs.size).map fun i ↦ (cs.getD i 0, vs.getD i 0)

theorem auto_loop {β : Type} (f : Unit → β → Id (ForInStep β)) (μ : β → ℕ) (P Q : β → Prop)
    (h : ∀ b, P b → match (f () b).run with
      | .done b' => Q b'
      | .yield b' => P b' ∧ μ b' < μ b)
    (b : β) (hb : P b) : Q (forIn Lean.Loop.mk b f).run := by
  induction hm : μ b using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    have := h b hb
    rw [show forIn Lean.Loop.mk b f = Lean.Loop.forIn Lean.Loop.mk b f from rfl,
      Lean.Loop.forIn_eq_of_monadTail]
    revert this
    rcases hf : (f () b).run with b' | b' <;> intro this
    · simp only [Id.run] at hf ⊢; rw [hf]; exact this
    · simp only [Id.run] at hf ⊢; rw [hf]; exact ih _ (hm ▸ this.2) b' this.1 rfl

theorem auto_getD_push {α : Type} (a : Array α) (x d : α) (i : ℕ) :
    (a.push x).getD i d = if i < a.size then a.getD i d else if i = a.size then x else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs with h1 h2 <;> try (clear * - α x d a i h1 h2; omega)
  · rfl
  · rfl
  · rw [Array.getElem?_eq_none (by omega)]; rfl

/-! Helpers for `runAuto_eq` (L-A agent, prefix `auto_`). The per-step sum identity holds for any input
states, so the sortedness hypothesis of `runAuto_eq` is not needed. -/

/-- One `eq` factor at bit 0 of `x`. -/
def auto_e (r : 𝔽) (x : ℕ) : 𝔽 := if x % 2 = 1 then r else 1 - r

/-- The weight of a half entry of kind `k`. -/
def auto_W (b x : 𝔽) (k : ℕ) : 𝔽 := if k = 2 then x else if k = 0 then (1 - b) * x else b * x

theorem auto_W_two (b x : 𝔽) : auto_W b x 2 = x := by simp only [auto_W, ↓reduceIte]

theorem auto_W_zero (b x : 𝔽) : auto_W b x 0 = (1 - b) * x := by simp only [auto_W, OfNat.zero_ne_ofNat, ↓reduceIte]

theorem auto_W_one (b x : 𝔽) : auto_W b x 1 = b * x := by simp only [auto_W, OfNat.one_ne_ofNat, ↓reduceIte, one_ne_zero]

/-- The state sum. -/
def auto_S (cs : Array ℕ) (vs : Array 𝔽) (g : ℕ → 𝔽) : 𝔽 :=
  ∑ i ∈ Finset.range cs.size, vs.getD i 0 * g (cs.getD i 0)

/-- The half sum of the first `m` entries. -/
def auto_HS (b : 𝔽) (ts : Array ℕ) (xs : Array 𝔽) (ks : Array ℕ) (g : ℕ → 𝔽) (m : ℕ) : 𝔽 :=
  ∑ i ∈ Finset.range m, auto_W b (xs.getD i 0) (ks.getD i 0) * g (ts.getD i 0)

theorem auto_S_push (cs : Array ℕ) (vs : Array 𝔽) (g : ℕ → 𝔽) (c : ℕ) (v : 𝔽)
    (h : cs.size = vs.size) : auto_S (cs.push c) (vs.push v) g = auto_S cs vs g + v * g c := by
  unfold auto_S
  rw [Array.size_push, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [auto_getD_push, auto_getD_push, if_pos hi, if_pos (h ▸ hi)]
  · simp only [auto_getD_push, ← h, lt_irrefl, ↓reduceIte]

theorem auto_HS_push (b : 𝔽) (ts : Array ℕ) (xs : Array 𝔽) (ks : Array ℕ) (g : ℕ → 𝔽)
    (t : ℕ) (x : 𝔽) (k : ℕ) (h1 : ts.size = xs.size) (h2 : ts.size = ks.size) :
    auto_HS b (ts.push t) (xs.push x) (ks.push k) g (ts.push t).size =
      auto_HS b ts xs ks g ts.size + auto_W b x k * g t := by
  unfold auto_HS
  rw [Array.size_push, Finset.sum_range_succ]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [auto_getD_push, auto_getD_push, auto_getD_push, if_pos hi, if_pos (h1 ▸ hi), if_pos (h2 ▸ hi)]
  · simp only [auto_getD_push, ← h1, ← h2, lt_irrefl, ↓reduceIte]

theorem auto_HS_succ (b : 𝔽) (ts : Array ℕ) (xs : Array 𝔽) (ks : Array ℕ) (g : ℕ → 𝔽) (m : ℕ) :
    auto_HS b ts xs ks g (m + 1) =
      auto_HS b ts xs ks g m + auto_W b (xs.getD m 0) (ks.getD m 0) * g (ts.getD m 0) := by
  unfold auto_HS; rw [Finset.sum_range_succ]

/-- `autoStepP`'s `half`. -/
def auto_half (cs : Array ℕ) (vs : Array 𝔽) (ryk : 𝔽) (sh : ℕ) : Array ℕ × Array 𝔽 × Array ℕ := Id.run do
    let n := cs.size
    let mut ts : Array ℕ := Array.mkEmpty n
    let mut xs : Array 𝔽 := Array.mkEmpty n
    let mut ks : Array ℕ := Array.mkEmpty n
    let mut i := 0
    while i < n do
      let c := cs.getD i 0
      let v := vs.getD i 0
      let d := c + sh
      if d % 2 == 0 then
        if i + 1 < n && cs.getD (i + 1) 0 == c + 1 then
          let v' := vs.getD (i + 1) 0
          ts := ts.push (d / 2); xs := xs.push (v + ryk * (v + v')); ks := ks.push 2
          i := i + 2
        else
          ts := ts.push (d / 2); xs := xs.push v; ks := ks.push 0
          i := i + 1
      else
        ts := ts.push (d / 2); xs := xs.push v; ks := ks.push 1
        i := i + 1
    return (ts, xs, ks)

theorem auto_half_gen (cs : Array ℕ) (vs : Array 𝔽) (b : 𝔽) (sh : ℕ) (g : ℕ → 𝔽)
    (Φ : Array ℕ × Array 𝔽 × Array ℕ → Prop)
    (hΦ : ∀ s : Array ℕ × Array 𝔽 × Array ℕ × ℕ, s.1.size = s.2.1.size → s.1.size = s.2.2.1.size →
      auto_HS b s.1 s.2.1 s.2.2.1 g s.1.size = ∑ l ∈ Finset.range cs.size,
        vs.getD l 0 * auto_e b (cs.getD l 0 + sh) * g ((cs.getD l 0 + sh) / 2) → Φ (s.1, s.2.1, s.2.2.1)) :
    Φ (auto_half cs vs b sh) := by
  unfold auto_half
  simp only [Id.run_bind, Id.run_pure]
  refine auto_loop (β := Array ℕ × Array 𝔽 × Array ℕ × ℕ) _ (fun s => cs.size - s.2.2.2)
    (fun s => s.1.size = s.2.1.size ∧ s.1.size = s.2.2.1.size ∧ s.2.2.2 ≤ cs.size ∧
      auto_HS b s.1 s.2.1 s.2.2.1 g s.1.size = ∑ l ∈ Finset.range s.2.2.2,
        vs.getD l 0 * auto_e b (cs.getD l 0 + sh) * g ((cs.getD l 0 + sh) / 2))
    (fun s => Φ (s.1, s.2.1, s.2.2.1)) ?_ _ ?_
  · rintro ⟨ts, xs, ks, i⟩ ⟨h1, h2, hi, hS⟩
    dsimp only at h1 h2 hi hS ⊢
    by_cases hlt : i < cs.size
    · rw [if_pos hlt]
      by_cases hev : (cs.getD i 0 + sh) % 2 = 0
      · rw [if_pos (by simpa only [Array.getD_eq_getD_getElem?, beq_iff_eq] using hev)]
        by_cases hp : i + 1 < cs.size ∧ cs.getD (i + 1) 0 = cs.getD i 0 + 1
        · rw [if_pos (by simpa only [Array.getD_eq_getD_getElem?, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hp)]
          obtain ⟨hp1, hp2⟩ := hp
          refine ⟨⟨by simp only [Array.getD_eq_getD_getElem?, Array.size_push, h1, Nat.add_left_cancel_iff], by simp only [Array.getD_eq_getD_getElem?, Array.size_push, h2, Nat.add_left_cancel_iff], by dsimp only; (clear * - hp1; omega), ?_⟩, by dsimp only; (clear * - hp1; omega)⟩
          dsimp only
          rw [auto_HS_push _ _ _ _ _ _ _ _ h1 h2, hS, show i + 2 = i + 1 + 1 from rfl, Finset.sum_range_succ,
            Finset.sum_range_succ, hp2]
          have e1 : auto_e b (cs.getD i 0 + sh) = 1 - b := by unfold auto_e; rw [if_neg (by (clear * - hev; omega))]
          have e2 : auto_e b (cs.getD i 0 + 1 + sh) = b := by unfold auto_e; rw [if_pos (by (clear * - hev; omega))]
          have e3 : (cs.getD i 0 + 1 + sh) / 2 = (cs.getD i 0 + sh) / 2 := by (clear * - hev; omega)
          rw [e1, e2, e3]
          rw [auto_W_two]
          linear_combination (b * vs.getD i 0 * g ((cs.getD i 0 + sh) / 2)) * (CharTwo.two_eq_zero (R := 𝔽))
        · rw [if_neg (by simpa only [Array.getD_eq_getD_getElem?, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] using hp)]
          refine ⟨⟨by simp only [Array.getD_eq_getD_getElem?, Array.size_push, h1, Nat.add_left_cancel_iff], by simp only [Array.getD_eq_getD_getElem?, Array.size_push, h2, Nat.add_left_cancel_iff], by dsimp only; (clear * - hlt; omega), ?_⟩, by dsimp only; (clear * - hlt; omega)⟩
          dsimp only
          rw [auto_HS_push _ _ _ _ _ _ _ _ h1 h2, hS, Finset.sum_range_succ]
          rw [show auto_e b (cs.getD i 0 + sh) = 1 - b by unfold auto_e; rw [if_neg (by (clear * - hev; omega))]]
          rw [auto_W_zero]
          ring
      · rw [if_neg (by simpa only [Array.getD_eq_getD_getElem?, beq_iff_eq, Nat.mod_two_not_eq_zero] using hev)]
        have hev' : (cs.getD i 0 + sh) % 2 = 1 := by (clear * - hev; omega)
        refine ⟨⟨by simp only [Array.getD_eq_getD_getElem?, Array.size_push, h1, Nat.add_left_cancel_iff], by simp only [Array.getD_eq_getD_getElem?, Array.size_push, h2, Nat.add_left_cancel_iff], by dsimp only; (clear * - hlt; omega), ?_⟩, by dsimp only; (clear * - hlt; omega)⟩
        dsimp only
        rw [auto_HS_push _ _ _ _ _ _ _ _ h1 h2, hS, Finset.sum_range_succ]
        rw [show auto_e b (cs.getD i 0 + sh) = b by unfold auto_e; rw [if_pos hev']]
        rw [auto_W_one]
        ring
    · rw [if_neg hlt]
      exact hΦ (ts, xs, ks, i) h1 h2 (by rw [hS, show i = cs.size by (clear * - hi hlt; omega)])
  · simp only [Array.mkEmpty_eq, List.size_toArray, List.length_nil, zero_le, auto_HS, Finset.range_zero, Array.getD_eq_getD_getElem?, not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none, Finset.sum_const, Finset.card_empty, zero_nsmul, Finset.sum_empty, and_self]

/-- `autoStepP`'s merge of the two halves. -/
def auto_merge (rxk ryk : 𝔽) (A B : Array ℕ × Array 𝔽 × Array ℕ) : Array ℕ × Array 𝔽 := Id.run do
  let p := rxk * ryk
  let e00 := 1 - rxk - ryk + p
  let e01 := ryk - p
  let e10 := rxk - p
  let e11 := p
  let (ta, va, ka) := A
  let (tb, vb, kb) := B
  let wy (val : 𝔽) (k : ℕ) : 𝔽 := if k == 2 then val else if k == 0 then val - ryk * val else ryk * val
  let mut oc : Array ℕ := Array.mkEmpty (ta.size + tb.size)
  let mut ov : Array 𝔽 := Array.mkEmpty (ta.size + tb.size)
  let mut i := 0
  let mut j := 0
  while i < ta.size || j < tb.size do
    let a := ta.getD i 0
    let b := tb.getD j 0
    if j ≥ tb.size || (i < ta.size && a < b) then
      let x := va.getD i 0
      let k := ka.getD i 0
      oc := oc.push a; ov := ov.push (if k == 2 then x - rxk * x else x * (if k == 0 then e00 else e01))
      i := i + 1
    else if i ≥ ta.size || b < a then
      let x := vb.getD j 0
      let k := kb.getD j 0
      oc := oc.push b; ov := ov.push (if k == 2 then rxk * x else x * (if k == 0 then e10 else e11))
      j := j + 1
    else
      let x := va.getD i 0
      let y := vb.getD j 0
      let k := ka.getD i 0
      let k' := kb.getD j 0
      oc := oc.push a
      if k != 2 && k' != 2 then
        ov := ov.push (x * (if k == 0 then e00 else e01) + y * (if k' == 0 then e10 else e11))
      else
        let A := wy x k
        let B := wy y k'
        ov := ov.push (A + rxk * (A + B))
      i := i + 1
      j := j + 1
  return (oc, ov)

theorem auto_autoStepP_eq (R : ℕ) (rxk ryk : 𝔽) (cs : Array ℕ) (vs : Array 𝔽) :
    autoStepPG R rxk ryk cs vs = auto_merge rxk ryk (auto_half cs vs ryk 0) (auto_half cs vs ryk R) := rfl

theorem auto_half_sum (cs : Array ℕ) (vs : Array 𝔽) (b : 𝔽) (sh : ℕ) (g : ℕ → 𝔽) :
    auto_HS b (auto_half cs vs b sh).1 (auto_half cs vs b sh).2.1 (auto_half cs vs b sh).2.2 g
      (auto_half cs vs b sh).1.size =
      ∑ l ∈ Finset.range cs.size, vs.getD l 0 * auto_e b (cs.getD l 0 + sh) * g ((cs.getD l 0 + sh) / 2) :=
  auto_half_gen cs vs b sh g (fun r => auto_HS b r.1 r.2.1 r.2.2 g r.1.size = _) fun _ _ _ h => h

theorem auto_V1 (a b x : 𝔽) (k : ℕ) :
    (if (k == 2) = true then x - a * x else x * if (k == 0) = true then 1 - a - b + a * b else b - a * b) =
      (1 - a) * auto_W b x k := by
  by_cases h2 : k = 2
  · subst h2; simp only [BEq.rfl, ↓reduceIte, auto_W]; ring
  · by_cases h0 : k = 0
    · subst h0; simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, auto_W, OfNat.zero_ne_ofNat]; ring
    · simp only [beq_iff_eq, h2, ↓reduceIte, h0, auto_W]; ring

theorem auto_V2 (a b x : 𝔽) (k : ℕ) :
    (if (k == 2) = true then a * x else x * if (k == 0) = true then a - a * b else a * b) =
      a * auto_W b x k := by
  by_cases h2 : k = 2
  · subst h2; simp only [BEq.rfl, ↓reduceIte, auto_W]
  · by_cases h0 : k = 0
    · subst h0; simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, auto_W, OfNat.zero_ne_ofNat]; ring
    · simp only [beq_iff_eq, h2, ↓reduceIte, h0, auto_W]; ring

theorem auto_wy (b x : 𝔽) (k : ℕ) :
    (if (k == 2) = true then x else if (k == 0) = true then x - b * x else b * x) = auto_W b x k := by
  by_cases h2 : k = 2
  · subst h2; simp only [BEq.rfl, ↓reduceIte, auto_W]
  · by_cases h0 : k = 0
    · subst h0; simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, auto_W, OfNat.zero_ne_ofNat]; ring
    · simp only [beq_iff_eq, h2, ↓reduceIte, h0, auto_W]

theorem auto_V3 (a b x y : 𝔽) (k k' : ℕ) :
    (if (k != 2 && k' != 2) = true then
        x * (if (k == 0) = true then 1 - a - b + a * b else b - a * b) +
          y * (if (k' == 0) = true then a - a * b else a * b)
      else
        (if (k == 2) = true then x else if (k == 0) = true then x - b * x else b * x) +
          a * ((if (k == 2) = true then x else if (k == 0) = true then x - b * x else b * x) +
            (if (k' == 2) = true then y else if (k' == 0) = true then y - b * y else b * y))) =
      (1 - a) * auto_W b x k + a * auto_W b y k' := by
  rw [auto_wy, auto_wy]
  by_cases hc : k ≠ 2 ∧ k' ≠ 2
  · obtain ⟨h2, h2'⟩ := hc
    rw [if_pos (by simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, h2, not_false_eq_true, h2', and_self])]
    by_cases h0 : k = 0 <;> by_cases h0' : k' = 0 <;> simp only [h0, BEq.rfl, ↓reduceIte, h0', auto_W, OfNat.zero_ne_ofNat, beq_iff_eq, h2', h2] <;> ring
  · rw [if_neg (by simpa only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] using hc)]
    linear_combination (a * auto_W b x k) * (CharTwo.two_eq_zero (R := 𝔽))

theorem auto_merge_gen (a b : 𝔽) (ta : Array ℕ) (va : Array 𝔽) (ka : Array ℕ) (tb : Array ℕ)
    (vb : Array 𝔽) (kb : Array ℕ) (g : ℕ → 𝔽) (Φ : Array ℕ × Array 𝔽 → Prop)
    (hΦ : ∀ s : Array ℕ × Array 𝔽 × ℕ × ℕ, s.1.size = s.2.1.size →
      auto_S s.1 s.2.1 g = (1 - a) * auto_HS b ta va ka g ta.size + a * auto_HS b tb vb kb g tb.size →
        Φ (s.1, s.2.1)) :
    Φ (auto_merge a b (ta, va, ka) (tb, vb, kb)) := by
  unfold auto_merge
  simp only [Id.run_bind, Id.run_pure]
  refine auto_loop (β := Array ℕ × Array 𝔽 × ℕ × ℕ) _ (fun s => (ta.size - s.2.2.1) + (tb.size - s.2.2.2))
    (fun s => s.1.size = s.2.1.size ∧ s.2.2.1 ≤ ta.size ∧ s.2.2.2 ≤ tb.size ∧
      auto_S s.1 s.2.1 g = (1 - a) * auto_HS b ta va ka g s.2.2.1 + a * auto_HS b tb vb kb g s.2.2.2)
    (fun s => Φ (s.1, s.2.1)) ?_ _ ?_
  · rintro ⟨oc, ov, i, j⟩ ⟨h1, hi, hj, hS⟩
    dsimp only at h1 hi hj hS ⊢
    by_cases hl : i < ta.size ∨ j < tb.size
    · rw [if_pos (by simpa only [Bool.or_eq_true, decide_eq_true_eq] using hl)]
      by_cases c1 : j ≥ tb.size ∨ (i < ta.size ∧ ta.getD i 0 < tb.getD j 0)
      · rw [if_pos (by simpa only [ge_iff_le, Array.getD_eq_getD_getElem?, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] using c1)]
        have hi' : i < ta.size := by (clear * - hi hj hl c1; omega)
        refine ⟨⟨by simp only [Array.getD_eq_getD_getElem?, Array.size_push, h1, beq_iff_eq, mul_ite, Nat.add_left_cancel_iff], by dsimp only; (clear * - hi'; omega), by dsimp only; omega, ?_⟩, by dsimp only; (clear * - hj hi'; omega)⟩
        dsimp only
        rw [auto_S_push _ _ _ _ _ h1, hS, auto_HS_succ, auto_V1]
        ring
      · rw [if_neg (by simpa only [ge_iff_le, Array.getD_eq_getD_getElem?, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, not_or, not_le, not_and, not_lt] using c1)]
        by_cases c2 : i ≥ ta.size ∨ tb.getD j 0 < ta.getD i 0
        · rw [if_pos (by simpa only [ge_iff_le, Array.getD_eq_getD_getElem?, Bool.or_eq_true, decide_eq_true_eq] using c2)]
          have hj' : j < tb.size := by (clear * - c1; omega)
          refine ⟨⟨by simp only [Array.getD_eq_getD_getElem?, Array.size_push, h1, beq_iff_eq, mul_ite, Nat.add_left_cancel_iff], by dsimp only; (clear * - hi; omega), by dsimp only; (clear * - c1; omega), ?_⟩, by dsimp only; (clear * - c1; omega)⟩
          dsimp only
          rw [auto_S_push _ _ _ _ _ h1, hS, auto_HS_succ, auto_V2]
          ring
        · rw [if_neg (by simpa only [ge_iff_le, Array.getD_eq_getD_getElem?, Bool.or_eq_true, decide_eq_true_eq, not_or, not_le, not_lt] using c2)]
          have hi' : i < ta.size := by (clear * - c2; omega)
          have hj' : j < tb.size := by (clear * - c1; omega)
          have hab : tb.getD j 0 = ta.getD i 0 := by (clear * - c1 c2; omega)
          have hV := auto_V3 a b (va.getD i 0) (vb.getD j 0) (ka.getD i 0) (kb.getD j 0)
          by_cases hc : (ka.getD i 0 != 2 && kb.getD j 0 != 2) = true
          · rw [if_pos hc] at hV ⊢
            refine ⟨⟨by simp only [Array.getD_eq_getD_getElem?, Array.size_push, h1, beq_iff_eq, mul_ite, Nat.add_left_cancel_iff], by dsimp only; (clear * - c2; omega), by dsimp only; (clear * - c1; omega), ?_⟩, by dsimp only; (clear * - c1 c2; omega)⟩
            dsimp only
            rw [auto_S_push _ _ _ _ _ h1, hS, auto_HS_succ, auto_HS_succ, hV, hab]
            ring
          · rw [if_neg hc] at hV ⊢
            refine ⟨⟨by simp only [Array.getD_eq_getD_getElem?, Array.size_push, h1, beq_iff_eq, Nat.add_left_cancel_iff], by dsimp only; (clear * - c2; omega), by dsimp only; (clear * - c1; omega), ?_⟩, by dsimp only; (clear * - c1 c2; omega)⟩
            dsimp only
            rw [auto_S_push _ _ _ _ _ h1, hS, auto_HS_succ, auto_HS_succ, hV, hab]
            ring
    · rw [if_neg (by simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] using hl)]
      exact hΦ (oc, ov, i, j) h1 (by rw [hS, show i = ta.size by (clear * - hi hl; omega), show j = tb.size by (clear * - hj hl; omega)])
  · simp only [Array.mkEmpty_eq, List.size_toArray, List.length_nil, zero_le, auto_S, Finset.range_zero, Array.getD_eq_getD_getElem?, not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none, zero_mul, Finset.sum_const_zero, auto_HS, Finset.sum_empty, mul_zero, add_zero, and_self]

/-- One automaton step on a test function. -/
def auto_T (R : ℕ) (a b : 𝔽) (g : ℕ → 𝔽) (c : ℕ) : 𝔽 :=
  (1 - a) * auto_e b c * g (c / 2) + a * auto_e b (c + R) * g ((c + R) / 2)

theorem auto_step_sum (R : ℕ) (a b : 𝔽) (cs : Array ℕ) (vs : Array 𝔽) (g : ℕ → 𝔽) :
    auto_S (autoStepPG R a b cs vs).1 (autoStepPG R a b cs vs).2 g = auto_S cs vs (auto_T R a b g) := by
  rw [auto_autoStepP_eq]
  have hA := auto_half_sum cs vs b 0 g
  have hB := auto_half_sum cs vs b R g
  generalize auto_half cs vs b 0 = A at hA ⊢
  generalize auto_half cs vs b R = B at hB ⊢
  obtain ⟨ta, va, ka⟩ := A
  obtain ⟨tb, vb, kb⟩ := B
  dsimp only at hA hB
  refine auto_merge_gen a b ta va ka tb vb kb g
    (fun r => auto_S r.1 r.2 g = auto_S cs vs (auto_T R a b g)) fun s _ h => ?_
  dsimp only
  rw [h, hA, hB]
  unfold auto_S auto_T
  simp only [add_zero, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The composed steps. -/
def auto_Tc (R : ℕ) (A B : ℕ → 𝔽) : List ℕ → (ℕ → 𝔽) → (ℕ → 𝔽)
  | [], g => g
  | k :: l, g => auto_T R (A k) (B k) (auto_Tc R A B l g)

theorem auto_nat (t u m : ℕ) :
    (t + 2 * u) % 2 ^ (m + 1) % 2 = t % 2 ∧ (t + 2 * u) % 2 ^ (m + 1) / 2 = (t / 2 + u) % 2 ^ m ∧
      (t + 2 * u) / 2 ^ (m + 1) = (t / 2 + u) / 2 ^ m := by
  rw [pow_succ']
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 _)]; (clear * - t u; omega)
  · rw [Nat.mod_mul_right_div_self, show (t + 2 * u) / 2 = t / 2 + u from Nat.add_mul_div_left t u (by decide)]
  · rw [← Nat.div_div_eq_div_mul, show (t + 2 * u) / 2 = t / 2 + u from Nat.add_mul_div_left t u (by decide)]

theorem auto_eqW_cons (r : 𝔽) (rs : List 𝔽) (x : ℕ) :
    eqWG (r :: rs) x = auto_e r x * eqWG rs (x / 2) := rfl

theorem auto_term (b : 𝔽) (bs : List 𝔽) (g : ℕ → 𝔽) (m t u : ℕ) :
    eqWG (b :: bs) ((t + 2 * u) % 2 ^ (m + 1)) * g ((t + 2 * u) / 2 ^ (m + 1)) =
      auto_e b t * (eqWG bs ((t / 2 + u) % 2 ^ m) * g ((t / 2 + u) / 2 ^ m)) := by
  obtain ⟨h1, h2, h3⟩ := auto_nat t u m
  rw [auto_eqW_cons, h2, h3, mul_assoc]
  congr 1
  unfold auto_e; rw [h1]

theorem auto_e_even (r : 𝔽) (j : ℕ) : auto_e r (2 * j) = 1 - r := by
  unfold auto_e; rw [if_neg (by (clear * - j; omega))]

theorem auto_e_odd (r : 𝔽) (j : ℕ) : auto_e r (2 * j + 1) = r := by
  unfold auto_e; rw [if_pos (by (clear * - j; omega))]

theorem auto_sum_double (f : ℕ → 𝔽) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), f j = ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1)) := by
  induction N with
  | zero => simp only [mul_zero, Finset.range_zero, Finset.sum_empty]
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

theorem auto_Tc_eq (R : ℕ) (A B : ℕ → 𝔽) (g : ℕ → 𝔽) (m : ℕ) :
    ∀ k0 s, auto_Tc R A B (List.range' k0 m) g s =
      ∑ j ∈ Finset.range (2 ^ m), eqWG ((List.range' k0 m).map A) j *
        eqWG ((List.range' k0 m).map B) ((s + R * j) % 2 ^ m) * g ((s + R * j) / 2 ^ m) := by
  induction m with
  | zero => intro k0 s; simp only [List.range'_zero, auto_Tc, pow_zero, Finset.range_one, List.map_nil, eqWG, mul_one, Nat.div_one, one_mul, Finset.sum_singleton, mul_zero, add_zero]
  | succ m ih =>
    intro k0 s
    simp only [List.range'_succ, auto_Tc, List.map_cons]
    unfold auto_T
    rw [ih, ih, show Finset.range (2 ^ (m + 1)) = Finset.range (2 * 2 ^ m) by rw [pow_succ'],
      auto_sum_double, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show s + R * (2 * j) = s + 2 * (R * j) by ring, mul_assoc (eqWG _ (2 * j)), auto_term, auto_eqW_cons,
        show 2 * j / 2 = j from Nat.mul_div_right j (by decide), auto_e_even]
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show s + R * (2 * j + 1) = s + R + 2 * (R * j) by ring, mul_assoc (eqWG _ (2 * j + 1)), auto_term,
        auto_eqW_cons, show (2 * j + 1) / 2 = j by rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt (by decide : 1 < 2), Nat.zero_add], auto_e_odd]
      ring

theorem auto_fold (R : ℕ) (A B : ℕ → 𝔽) (l : List ℕ) (s : Array ℕ × Array 𝔽) (g : ℕ → 𝔽) :
    auto_S (l.foldl (fun b a => ((autoStepPG R (A a) (B a) b.1 b.2).1, (autoStepPG R (A a) (B a) b.1 b.2).2))
        s).1
      (l.foldl (fun b a => ((autoStepPG R (A a) (B a) b.1 b.2).1, (autoStepPG R (A a) (B a) b.1 b.2).2)) s).2 g =
      auto_S s.1 s.2 (auto_Tc R A B l g) := by
  induction l generalizing s with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldl_cons, ih]
    exact auto_step_sum R (A k) (B k) s.1 s.2 _

theorem auto_listsum (f : ℕ → 𝔽) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp only [List.range_zero, List.map_nil, List.sum_nil, Finset.range_zero, Finset.sum_empty]
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem auto_out (cs : Array ℕ) (vs : Array 𝔽) (g : ℕ → 𝔽) :
    (((Array.range cs.size).map fun i => (cs.getD i 0, vs.getD i 0)).toList.map fun cv => cv.2 * g cv.1).sum =
      auto_S cs vs g := by
  simp only [Array.toList_map, Array.toList_range, List.map_map]
  rw [auto_listsum]; rfl

theorem auto_init (st : Array (ℕ × 𝔽)) (h : ℕ → 𝔽) :
    auto_S (st.map (·.1)) (st.map (·.2)) h = (st.toList.map fun sv => sv.2 * h sv.1).sum := by
  unfold auto_S
  rw [← auto_listsum]
  congr 1
  apply List.ext_getElem (by simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.size_map, List.length_map, List.length_range, Array.length_toList])
  intro i h1 h2
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.size_map, List.length_map, List.length_range] at h1
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.size_map, List.getElem_map, List.getElem_range, h1, getElem?_pos, Option.map_some, Option.getD_some, Array.getElem_toList]

theorem auto_rx (rx : Array 𝔽) (xs : Array ℕ) :
    (List.range' 0 xs.size).map (fun a => rx.getD (xs.getD a 0) 0) = xs.toList.map fun i => rx.getD i 0 := by
  apply List.ext_getElem (by simp only [Array.getD_eq_getD_getElem?, List.length_map, List.length_range', Array.length_toList])
  intro i h1 h2
  simp only [Array.getD_eq_getD_getElem?, List.length_map, List.length_range'] at h1
  simp only [Array.getD_eq_getD_getElem?, List.getElem_map, List.getElem_range', one_mul, zero_add, h1, getElem?_pos, Option.getD_some, Array.getElem_toList]

theorem auto_ry (ry : Array 𝔽) (n : ℕ) : (List.range' 0 n).map (fun a => ry.getD a 0) = sub ry 0 n := by
  unfold sub
  rw [List.range_eq_range']
  simp only [Array.getD_eq_getD_getElem?, zero_add]

/-- **The automaton** (statement): on states sorted with distinct keys, the final states carry
`Σ_s v_s Σ_j eq(r_x,xs, j)·eq(r_y[0,n), (s + R·j) mod 2^n)` on `(s + R·j) / 2^n`. Owner L-A. -/
theorem runAuto_eq (P : PtG 𝔽) (xs : Array ℕ) (R : ℕ) (st : Array (ℕ × 𝔽))
    (hs : st.toList.Pairwise fun a b ↦ a.1 < b.1) (g : ℕ → 𝔽) :
    ((runAutoG P xs R st).toList.map fun cv ↦ cv.2 * g cv.1).sum =
      (st.toList.map fun sv ↦ sv.2 * ((List.range (2 ^ xs.size)).map fun j ↦
        eqWG (xs.toList.map fun i ↦ P.rx.getD i 0) j *
          eqWG (sub P.ry 0 xs.size) ((sv.1 + R * j) % 2 ^ xs.size) * g ((sv.1 + R * j) / 2 ^ xs.size)).sum).sum := by
  unfold runAutoG
  simp only [Id.run_bind, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  have hn : [:xs.size].size = xs.size := by simp only [Std.Legacy.Range.size, tsub_zero, add_tsub_cancel_right, Nat.div_one]
  rw [hn, auto_out, auto_fold R (fun a => P.rx.getD (xs.getD a 0) 0) (fun a => P.ry.getD a 0), auto_init]
  refine congrArg List.sum (List.map_congr_left fun sv _ => ?_)
  rw [auto_Tc_eq, auto_listsum, auto_rx, auto_ry]

section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-! ## The initial-state code -/

/-- `c'` is `c` with a block appended that emits `O` (and leaves the open sum alone). -/
def code_ISpec (T : Array (Array 𝔽)) (c c' : Code) (O : Array (ℕ × 𝔽)) : Prop :=
  code_Al c' ∧ (∃ R, c'.ws = c.ws ++ R) ∧ ∃ L, code_instrs c' = code_instrs c ++ L ∧
    ∀ (R : Array FE) top st em, L.foldl (code_step T (c'.ws ++ R)) (top, st, em) = (top, st, em ++ O)

theorem code_ISpec_zero (T : Array (Array 𝔽)) (c : Code) (hc : code_Al c) : code_ISpec T c c #[] :=
  ⟨hc, ⟨#[], by simp only [Array.append_empty]⟩, [], by simp only [List.append_nil], by simp only [List.foldl_nil, Array.append_empty, implies_true]⟩

theorem code_ISpec_trans (T : Array (Array 𝔽)) (c c1 c2 : Code) (O1 O2 : Array (ℕ × 𝔽))
    (h1 : code_ISpec T c c1 O1) (h2 : code_ISpec T c1 c2 O2) : code_ISpec T c c2 (O1 ++ O2) := by
  obtain ⟨-, ⟨R1, hR1⟩, L1, hL1, hf1⟩ := h1
  obtain ⟨hA, ⟨R2, hR2⟩, L2, hL2, hf2⟩ := h2
  refine ⟨hA, ⟨R1 ++ R2, by rw [hR2, hR1, Array.append_assoc]⟩, L1 ++ L2, by rw [hL2, hL1, List.append_assoc],
    fun R top st em ↦ ?_⟩
  rw [List.foldl_append]
  have : c2.ws ++ R = c1.ws ++ (R2 ++ R) := by rw [hR2, Array.append_assoc]
  rw [this, hf1, ← this, hf2, Array.append_assoc]

/-- An open sum, a block adding `E`, and a close emitting `(s, E)`. -/
theorem code_ISpec_wrap (T : Array (Array 𝔽)) (c c2 : Code) (E : 𝔽) (s : ℕ) (hc : code_Al c)
    (h : code_Spec T (c.emit 0 0 0 0) c2 E) : code_ISpec T c (c2.emit 3 0 s 0) #[(s, E)] := by
  obtain ⟨hA0, hI0, hW0⟩ := code_emit c 0 0 0 0 hc
  obtain ⟨hA2, ⟨R2, hR2⟩, L2, hL2, hf2⟩ := h
  obtain ⟨hA3, hI3, hW3⟩ := code_emit c2 3 0 s 0 hA2
  refine ⟨hA3, ⟨R2, by rw [hW3, hR2, hW0]⟩, [(0, 0, 0, 0)] ++ L2 ++ [(3, 0, s, 0)],
    by rw [hI3, hL2, hI0]; simp only [List.append_assoc], fun R top st em ↦ ?_⟩
  rw [hW3, List.foldl_append, List.foldl_append]
  have h1 : List.foldl (code_step T (c2.ws ++ R)) (top, st, em) [(0, 0, 0, 0)] = (0, st.push top, em) := by
    simp only [List.foldl_cons, code_step, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl, List.foldl_nil]
  rw [h1, hf2, zero_add]
  simp only [List.foldl_cons, List.foldl_nil, code_step]
  simp only [show ((3 : ℕ) == 2) = false from rfl, show ((3 : ℕ) == 0) = false from rfl,
    show ((3 : ℕ) == 3) = true from rfl, Bool.false_eq_true, ite_false, ite_true, Array.back?_push,
    Option.getD_some, Array.pop_push]
  rfl

theorem greedy_loop_ISpec {X : Type} (T : Array (Array 𝔽)) (F : Code → X → Code) (s : X → ℕ) (v : X → 𝔽)
    (l : List X) (hF : ∀ c x, x ∈ l → code_Al c → 0 < c.ws.size → code_ISpec T c (F c x) #[(s x, v x)]) :
    ∀ c, code_Al c → 0 < c.ws.size → code_ISpec T c (l.foldl F c) (l.map fun x ↦ (s x, v x)).toArray := by
  induction l with
  | nil => intro c hc _; simpa only [List.foldl_nil, List.map_nil] using code_ISpec_zero T c hc
  | cons x l ih =>
    intro c hc hw
    rw [List.foldl_cons]
    have h1 := hF c x List.mem_cons_self hc hw
    obtain ⟨hA1, ⟨R1, hR1⟩, -⟩ := id h1
    have := code_ISpec_trans T _ _ _ _ _ h1
      (ih (fun c x hx ↦ hF c x (List.mem_cons_of_mem _ hx)) _ hA1 (by rw [hR1, Array.size_append]; (clear * - hw; omega)))
    convert this using 1
    apply Array.toList_inj.1
    simp only [List.map_cons, List.append_toArray, List.cons_append, List.nil_append]

/-- `sortAt`'s order. -/
def greedy_cmp (κ : ℕ → ℕ × ℕ) (i j : ℕ) : Bool := keyLt (κ i) (κ j) || (κ i == κ j && decide (i < j))

theorem greedy_cmp_trans (κ : ℕ → ℕ × ℕ) (a b c : ℕ) (h1 : greedy_cmp κ a b = true) (h2 : greedy_cmp κ b c = true) :
    greedy_cmp κ a c = true := by
  simp only [greedy_cmp, keyLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Prod.ext_iff] at h1 h2 ⊢
  (clear * - κ a c b h1 h2; omega)

theorem greedy_cmp_asymm (κ : ℕ → ℕ × ℕ) (a b : ℕ) (h : greedy_cmp κ a b = true) : greedy_cmp κ b a = false := by
  simp only [greedy_cmp, keyLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Prod.ext_iff] at h
  simp only [greedy_cmp, keyLt, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne,
    ne_eq, Prod.ext_iff]
  (clear * - κ b a h; omega)

theorem greedy_sortAt_sorted (as : Array Atom) (L : ℕ) (ix : Array ℕ) :
    (sortAt as L ix).toList.Pairwise fun a b ↦ keyLt (keyAt as L b) (keyAt as L a) = false := by
  have := greedy_qs_qsort_sorted ix (greedy_cmp (keyAt as L)) (greedy_cmp_trans _) (greedy_cmp_asymm _)
  refine this.imp fun h ↦ ?_
  simp only [greedy_cmp, Bool.or_eq_false_iff] at h
  exact h.1

/-- Runs' keys are sorted when the input is sorted by key. -/
theorem greedy_runs_le (as : Array Atom) (L : ℕ) (xs : Array ℕ)
    (hs : xs.toList.Pairwise fun a b ↦ (keyAt as L a).2 ≤ (keyAt as L b).2) :
    ((runsAt as L xs).toList.map (·.1)).Pairwise fun x y ↦ x.2 ≤ y.2 := by
  obtain ⟨h1, h2, -⟩ := greedy_runsAt_spec as L xs
  rw [← h1, List.pairwise_flatten, List.pairwise_map] at hs
  rw [List.pairwise_map]
  refine hs.2.imp_of_mem fun {r r'} hr hr' h ↦ ?_
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ (h2 r hr).1
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ (h2 r' hr').1
  have := h i hi j hj
  rwa [(h2 r hr).2 i hi, (h2 r' hr').2 j hj] at this

theorem greedy_strict (l : List (ℕ × ℕ)) (h1 : l.Pairwise fun x y ↦ x.2 ≤ y.2) (h2 : ∀ x ∈ l, x.1 = 0)
    (h3 : greedy_adj l) : l.Pairwise fun x y ↦ x.2 < y.2 := by
  induction l with
  | nil => simp only [List.Pairwise.nil]
  | cons x l ih =>
    rw [List.pairwise_cons] at h1 ⊢
    have ih' := ih h1.2 (fun y hy ↦ h2 y (List.mem_cons_of_mem _ hy))
      (by cases l with | nil => trivial | cons y l => exact h3.2)
    refine ⟨fun z hz ↦ ?_, ih'⟩
    cases l with
    | nil => simp only [List.not_mem_nil] at hz
    | cons y l =>
      have hxy : x.2 < y.2 := by
        have a1 := h1.1 y List.mem_cons_self
        have a2 := h2 x List.mem_cons_self
        have a3 := h2 y (List.mem_cons_of_mem _ List.mem_cons_self)
        have a4 : x.2 ≠ y.2 := fun e ↦ h3.1 (Prod.ext (by (clear * - a2 a3; omega)) e)
        (clear * - a1 a4; omega)
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy
      · exact lt_trans hxy ((List.pairwise_cons.1 ih').1 z hz)

theorem greedy_hK1 (T : Array (Array 𝔽)) (as : Array Atom) (hT : keyValG T (0, 0) = 1)
    (h0 : ∀ a ∈ as, ∀ k ∈ a.keys.toList.drop 1, k.1 = 0 → k.2 = 0) :
    ∀ i m, m ≠ 0 → (keyAt as m i).1 = 0 → keyValG T (keyAt as m i) = 1 := by
  intro i m hm h1
  unfold keyAt at *
  rcases code_key as i m with h | ⟨a, ha, hm', h⟩
  · rw [h]; exact hT
  · have hmem : a.keys[m] ∈ a.keys.toList.drop 1 := by
      have e : 1 + (m - 1) = m := by (clear * - hm; omega)
      exact List.mem_drop_iff_getElem.2 ⟨m - 1, by simp only [Array.length_toList]; (clear * - hm' e; omega), by simp only [e, Array.getElem_toList]⟩
    have h2 := h0 a ha _ hmem (h ▸ h1)
    rw [h, ← hT]
    congr 1
    exact Prod.ext (h ▸ h1) h2

theorem greedy_hk0 (as : Array Atom) (h1 : ∀ a ∈ as, (a.keys.getD 0 (0, 0)).1 = 0) (i : ℕ) :
    (keyAt as 0 i).1 = 0 := by
  unfold keyAt
  rcases code_key as i 0 with h | ⟨a, ha, hm, h⟩
  · rw [h]
  · rw [h]
    have := h1 a ha
    simpa only [Array.getD_eq_getD_getElem?, hm, getElem?_pos, Option.getD_some] using this

theorem greedy_range_erase_zero (D : ℕ) : (List.range D).erase 0 = (List.range D).drop 1 := by
  cases D with
  | zero => simp only [List.range_zero, List.erase_nil, List.drop_nil]
  | succ n => rw [List.range_succ_eq_map]; simp only [List.erase_cons_head, List.drop_succ_cons, List.drop_zero]

theorem greedy_valFrom1 (T : Array (Array 𝔽)) (a : Atom) (D : ℕ) (h : a.keys.size = D) :
    KRing.ofE a.w * (((List.range D).erase 0).map fun L ↦ keyValG T (a.keys.getD L (0, 0))).prod = runs_valFrom T 1 a := by
  rw [runs_valFrom, greedy_foldl_mul, greedy_keys_toList, h, ← List.map_drop, List.map_map, greedy_range_erase_zero]
  rfl

theorem greedy_initCodeG (T : Array (Array 𝔽)) (as : Array Atom) (D : ℕ)
    (hD : ∀ a ∈ as, a.keys.size = D) (hT : keyValG T (0, 0) = 1)
    (h0 : ∀ a ∈ as, ∀ k ∈ a.keys.toList.drop 1, k.1 = 0 → k.2 = 0) (h1 : ∀ a ∈ as, (a.keys.getD 0 (0, 0)).1 = 0)
    (g : ℕ → 𝔽) :
    ((runCodeG T (initCodeG as D)).2.toList.Pairwise fun a b ↦ a.1 < b.1) ∧
      ((runCodeG T (initCodeG as D)).2.toList.map fun sv ↦ sv.2 * g sv.1).sum =
        (as.toList.map fun a ↦ runs_valFrom T 1 a * g (a.keys.getD 0 (0, 0)).2).sum := by
  have hcode : initCodeG as D = (runsAt as 0 (sortAt as 0 (Array.range as.size))).toList.foldl
      (fun c r ↦ (genG as (D + 1) r.2 ((List.range D).erase 0) (c.emit 0 0 0 0)).emit 3 0 r.1.2 0)
      ⟨#[], #[], #[], #[], #[1]⟩ := by
    simp only [initCodeG, Id.run]
    rw [greedy_forIn_arr _ _ _
      (fun (c : Code) (r : (ℕ × ℕ) × Array ℕ) ↦ (genG as (D + 1) r.2 ((List.range D).erase 0) (c.emit 0 0 0 0)).emit 3 0 r.1.2 0)
      (fun a b ↦ rfl), ← Array.foldl_toList]
    rfl
  have hspec := greedy_loop_ISpec T
    (fun c r ↦ (genG as (D + 1) r.2 ((List.range D).erase 0) (c.emit 0 0 0 0)).emit 3 0 r.1.2 0)
    (fun r ↦ r.1.2)
    (fun r ↦ (r.2.toList.map fun i ↦ KRing.ofE (as.getD i default).w *
      (((List.range D).erase 0).map fun L ↦ keyValG T (keyAt as L i)).prod).sum)
    (runsAt as 0 (sortAt as 0 (Array.range as.size))).toList
    (fun c r _ hc hw ↦ code_ISpec_wrap T c _ _ _ hc
      (greedy_genG_P T as (· ≠ 0) hT (greedy_hK1 T as hT h0) (D + 1) r.2 ((List.range D).erase 0)
        (c.emit 0 0 0 0) (List.nodup_range.erase 0)
        (lt_of_le_of_lt List.erase_sublist.length_le (by simp only [List.length_range, lt_add_iff_pos_right, Order.lt_one_iff]))
        (fun L hL ↦ (List.nodup_range.mem_erase_iff.1 hL).1) (code_emit c 0 0 0 0 hc).1
        (by rw [(code_emit c 0 0 0 0 hc).2.2]; exact hw)))
    _ code_atom0 (by decide)
  have hem : (runCodeG T (initCodeG as D)).2 = ((runsAt as 0 (sortAt as 0 (Array.range as.size))).toList.map
      fun r ↦ (r.1.2, (r.2.toList.map fun i ↦ KRing.ofE (as.getD i default).w *
        (((List.range D).erase 0).map fun L ↦ keyValG T (keyAt as L i)).prod).sum)).toArray := by
    obtain ⟨-, -, L, hL, hf⟩ := hspec
    have := hf #[] 0 #[] #[]
    rw [Array.append_empty] at this
    have hn : code_instrs (⟨#[], #[], #[], #[], #[1]⟩ : Code) = [] := rfl
    rw [code_runCode, hcode, hL, hn, List.nil_append, this]
    simp only [Array.getD_eq_getD_getElem?, List.append_toArray, List.nil_append]
  obtain ⟨hs1, hs2, hs3⟩ := greedy_runsAt_spec as 0 (sortAt as 0 (Array.range as.size))
  rw [hem, List.toList_toArray]
  constructor
  · have := greedy_strict _
      (greedy_runs_le as 0 _ ((greedy_sortAt_sorted as 0 _).imp fun {a b} h ↦ by
        have e1 := greedy_hk0 as h1 a
        have e2 := greedy_hk0 as h1 b
        simp only [keyLt, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
          beq_eq_false_iff_ne, ne_eq] at h
        (clear * - e1 e2 h; omega)))
      (fun x hx ↦ by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ (hs2 r hr).1
        rw [← (hs2 r hr).2 i hi]
        exact greedy_hk0 as h1 i) hs3
    simp only [List.pairwise_map] at this ⊢
    exact this
  · rw [List.map_map]
    have e1 : ∀ r ∈ (runsAt as 0 (sortAt as 0 (Array.range as.size))).toList,
        (Function.comp (fun sv ↦ sv.2 * g sv.1) fun r ↦ (r.1.2, (r.2.toList.map fun i ↦ KRing.ofE (as.getD i default).w *
          (((List.range D).erase 0).map fun L ↦ keyValG T (keyAt as L i)).prod).sum)) r =
        (r.2.toList.map fun i ↦ KRing.ofE (as.getD i default).w *
          (((List.range D).erase 0).map fun L ↦ keyValG T (keyAt as L i)).prod * g (keyAt as 0 i).2).sum := by
      intro r hr
      simp only [Function.comp_apply]
      rw [← List.sum_map_mul_right]
      refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
      rw [(hs2 r hr).2 i hi]
    rw [List.map_congr_left e1, ← greedy_runs_sum, Array.toList_range,
      ← greedy_range_map as (fun a ↦ runs_valFrom T 1 a * g (a.keys.getD 0 (0, 0)).2)]
    refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
    rw [← greedy_valFrom1 T _ D (hD _ (runs_getD_mem as i (List.mem_range.1 hi)))]
    rfl

/-! ## Paste below `passInit` (they use `Pass`, `passInit`) -/

end L1

/-- A pass's finish at a final state `c` (`y ≫ n`). -/
def finVal (T : Array (Array FE)) (p : Pass) (c : ℕ) : FE :=
  p.fin.foldl (fun acc (t, bs) ↦ acc * (T.getD t #[]).getD (pext c bs) 0) 1

/-- The proof-side twin of `finVal` over a value ring (S2GT-W). -/
def finValG (T : Array (Array 𝔽)) (p : Pass) (c : ℕ) : 𝔽 :=
  p.fin.foldl (fun acc (t, bs) ↦ acc * (T.getD t #[]).getD (pext c bs) 0) 1

/-- `lo` if `bs` is the run `[lo, lo + bs.length)` (`pext` is then a shift and a mask). -/
def runOf (bs : List ℕ) : Option ℕ :=
  match bs with
  | [] => some 0
  | b :: _ => if bs == (List.range bs.length).map (b + ·) then some b else none

/-- `pext v bs`, by a shift and the mask `mk = 2^|bs| − 1` when `bs` is a run. -/
@[inline] def pextR (r : Option ℕ) (mk v : ℕ) (bs : List ℕ) : ℕ :=
  match r with
  | some lo => (v >>> lo) &&& mk
  | none => pext v bs

/-- **The finish** `Σ_c v_c·Fin(c)` on the sorted final states: with a low and a high table, the high factor once
per run of equal high index (`Σ_h T_hi[h]·Σ_c v_c·T_lo[c]`); a group of bits that is a run is read by a shift. -/
def finSum (T : Array (Array FE)) (p : Pass) (fs : Array (ℕ × FE)) : FE := Id.run do
  if p.fin.size != 2 then return fs.foldl (fun acc (c, v) ↦ acc + v * finVal T p c) 0
  let (tl, bl) := p.fin.getD 0 (0, [])
  let (th, bh) := p.fin.getD 1 (0, [])
  let rl := runOf bl
  let rh := runOf bh
  let ml := 2 ^ bl.length - 1
  let mh := 2 ^ bh.length - 1
  let Tl := T.getD tl #[]
  let Th := T.getD th #[]
  let mut tot : FE := 0
  let mut inner : FE := 0
  let mut h := pextR rh mh (fs.getD 0 (0, 0)).1 bh
  for (c, v) in fs do
    let h' := pextR rh mh c bh
    if h' != h then
      tot := tot + Th.getD h 0 * inner
      inner := 0
      h := h'
    inner := inner + mulI v (Tl.getD (pextR rl ml c bl) 0)
  return tot + Th.getD h 0 * inner

/-- The proof-side twin of `finSum` over a value ring (S2GT-W). -/
def finSumG (T : Array (Array 𝔽)) (p : Pass) (fs : Array (ℕ × 𝔽)) : 𝔽 := Id.run do
  if p.fin.size != 2 then return fs.foldl (fun acc (c, v) ↦ acc + v * finValG T p c) 0
  let (tl, bl) := p.fin.getD 0 (0, [])
  let (th, bh) := p.fin.getD 1 (0, [])
  let rl := runOf bl
  let rh := runOf bh
  let ml := 2 ^ bl.length - 1
  let mh := 2 ^ bh.length - 1
  let Tl := T.getD tl #[]
  let Th := T.getD th #[]
  let mut tot : 𝔽 := 0
  let mut inner : 𝔽 := 0
  let mut h := pextR rh mh (fs.getD 0 (0, 0)).1 bh
  for (c, v) in fs do
    let h' := pextR rh mh c bh
    if h' != h then
      tot := tot + Th.getD h 0 * inner
      inner := 0
      h := h'
    inner := inner + v * (Tl.getD (pextR rl ml c bl) 0)
  return tot + Th.getD h 0 * inner

section L1
variable [KRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- **A pass's value.** -/
def runPass (P : PtG 𝔽) (T : Array (Array 𝔽)) (p : Pass) : 𝔽 :=
  let fs := runAutoG P p.xs p.R (runCodeG T p.code).2
  let s := finSumG T p fs
  match p.limbE with
  | some e => s * limbValG (P.ry.getD e 0) (P.ry.getD (e + 1) 0)
  | none => s

/-! ## The compiled evaluator -/

/-- **The compiled form of `Φ_Q`**: the tables, the atoms (sorted) and the passes. -/
structure Comp where
  /-- The table recipes (table `0` is `TRec.one`). -/
  tabs : Array TRec
  /-- The atoms of the K1/K2/point terms. -/
  atoms : Array Atom
  /-- Their levels. -/
  depth : ℕ
  /-- The K3 passes. -/
  passes : Array Pass
  /-- The code of the atoms (`atomCode atoms depth`). -/
  code : Code := default
  /-- Its fused form, if fused (B1-K2). -/
  fcode : Option FCode := none
  deriving Inhabited

/-- **A pass's value** on the flat tables too: its fused initial code if it has one. -/
def runPassF (P : Pt) (T : Array (Array FE)) (F : Array FE) (p : Pass) : FE :=
  let ini := match p.fcode with
    | some fc => (runF F fc).2
    | none => (runCode T p.code).2
  let s := finSum T p (runAuto P p.xs p.R ini)
  match p.limbE with
  | some e => s * limbVal (P.ry.getD e 0) (P.ry.getD (e + 1) 0)
  | none => s

/-- The proof-side twin of `runPassF` over a value ring (S2GT-W). -/
def runPassFG (P : PtG 𝔽) (T : Array (Array 𝔽)) (F : Array 𝔽) (p : Pass) : 𝔽 :=
  let ini := match p.fcode with
    | some fc => (runFG F fc).2
    | none => (runCodeG T p.code).2
  let s := finSumG T p (runAutoG P p.xs p.R ini)
  match p.limbE with
  | some e => s * limbValG (P.ry.getD e 0) (P.ry.getD (e + 1) 0)
  | none => s

/-- **The compiled evaluator**: the atom sum plus the passes, on the flat tables where the code is fused. -/
def evalC (c : Comp) (pt : List FE) : FE :=
  let P := Pt.ofList pt
  let T := tabsAt P c.tabs
  let F := flatTabs c.tabs T
  let a := match c.fcode with
    | some fc => (runF F fc).1
    | none => (runCode T c.code).1
  c.passes.foldl (fun acc p ↦ acc + runPassF P T F p) a

/-- The proof-side twin of `evalC` over a value ring (S2GT-W). -/
def evalCG (c : Comp) (pt : List 𝔽) : 𝔽 :=
  let P := PtG.ofList pt
  let T := tabsAtG P c.tabs
  let F := flatTabsG c.tabs T
  let a := match c.fcode with
    | some fc => (runFG F fc).1
    | none => (runCodeG T c.code).1
  c.passes.foldl (fun acc p ↦ acc + runPassFG P T F p) a

end L1

/-! ## The executable evaluator is the twin at `FE` (S2GT-W)

Each executable function equals its twin at `𝔽 = FE` by its equation lemmas (the twins differ by `mulI` against
`*`, `fmul`/`wmul`/`FE.smulBase` against the weights' map, and `Pt` against `PtG FE`). -/

/-- The weights' map at `FE` is the identity. -/
@[simp] theorem ofE_FE (w : FE) : (KRing.ofE w : FE) = w := rfl

/-- `eqW` is its twin at `FE`. -/
theorem eqW_eqG (l : List FE) (x : ℕ) : eqW l x = eqWG l x := by
  induction l generalizing x with
  | nil => rfl
  | cons r rs ih => simp only [eqW, eqWG, ih]

/-- The executable point as the twin's. -/
def Pt.toG (P : Pt) : PtG FE := ⟨P.kap, P.rx, P.ry⟩

theorem fmul_eqG : fmul = fun a b : FE ↦ a * b := funext fun a ↦ funext fun b ↦ runs_fmul a b

theorem mulI_eqG : mulI = fun a b : FE ↦ a * b := rfl

theorem eqTab_eqG (r : Array FE) (lo n : ℕ) : eqTab r lo n = eqTabG r lo n := by
  unfold eqTab eqTabG; simp only [mulI_eqG]

theorem eqTabB_eqG (r : Array FE) (bits : List ℕ) : eqTabB r bits = eqTabBG r bits := by
  unfold eqTabB eqTabBG; simp only [mulI_eqG]

theorem eqLevels_eqG (r : Array FE) (lo n : ℕ) : eqLevels r lo n = eqLevelsG r lo n := by
  unfold eqLevels eqLevelsG; simp only [mulI_eqG]

theorem margTab_eqG (lv : Array (Array FE)) (lo n : ℕ) (bits : List ℕ) :
    margTab lv lo n bits = margTabG lv lo n bits := by
  unfold margTab margTabG; rfl

theorem subTab_eqG (r : Array FE) (lv : Array (Array FE)) (lo n : ℕ) (bits : List ℕ) :
    subTab r lv lo n bits = subTabG r lv lo n bits := by
  unfold subTab subTabG; simp only [eqTabB_eqG, margTab_eqG]

theorem kapTab_eqG (κ : Array FE) : kapTab κ = kapTabG κ := by
  unfold kapTab kapTabG; simp only [eqTab_eqG]

theorem succVal_eqG (xs ys : List FE) : succVal xs ys = succValG xs ys := by
  unfold succVal succValG; rfl

theorem limbVal_eqG (a b : FE) : limbVal a b = limbValG a b := by
  unfold limbVal limbValG; simp only [ofE_FE]

theorem kfVal_eqG (P : Pt) (f : KF) : kfVal P f = kfValG P.toG f := by
  cases f <;> simp only [kfVal, kfValG, Pt.toG, eq1, eq1G, succVal_eqG, limbVal_eqG, ofE_FE, FE.smulBase_eq_mul]

theorem kerVal_eqG (P : Pt) (fs : List KF) : kerVal P fs = kerValG P.toG fs := by
  unfold kerVal kerValG; simp only [kfVal_eqG]

theorem TRec.eval_eqG (P : Pt) (r : TRec) : TRec.eval P r = TRec.evalG P.toG r := by
  have hk : kerVal P = kerValG P.toG := funext (kerVal_eqG P)
  cases r <;> simp only [TRec.eval, TRec.evalG, eqTabB_eqG, kapTab_eqG, hk] <;> rfl

theorem prodKeys_eqG (T : Array (Array FE)) (ks : List (ℕ × ℕ)) : prodKeys T ks = prodKeysG T ks := by
  cases ks <;> rfl

theorem tabsAt_eqG (P : Pt) (rs : Array TRec) : tabsAt P rs = tabsAtG P.toG rs := by
  have hp : prodKeys = prodKeysG (𝔽 := FE) := funext fun T ↦ funext fun ks ↦ prodKeys_eqG T ks
  unfold tabsAt tabsAtG
  simp only [eqLevels_eqG, subTab_eqG, TRec.eval_eqG, hp, Pt.toG]

theorem flatTabs_eqG (rs : Array TRec) (T : Array (Array FE)) : flatTabs rs T = flatTabsG rs T := by
  unfold flatTabs flatTabsG; rfl

theorem wmul_eqG (m : ℕ) (v w : FE) : wmul m v w = wmulG m v w := by
  unfold wmul wmulG
  simp only [ofE_FE, FE.smulBase_eq_mul, code_mulY, show (⟨0, 1, 0⟩ : FE) = FE.y from rfl]

theorem runF_eqG (F : Array FE) (c : FCode) : runF F c = runFG F c := by
  have hw : wmul = wmulG := funext fun m ↦ funext fun v ↦ funext fun w ↦ wmul_eqG m v w
  unfold runF runFG; simp only [mulI_eqG, hw]

theorem runCode_eqG (T : Array (Array FE)) (c : Code) : runCode T c = runCodeG T c := by
  unfold runCode runCodeG; simp only [fmul_eqG, ofE_FE]

theorem autoStepP_eqG (R : ℕ) (rxk ryk : FE) (cs : Array ℕ) (vs : Array FE) :
    autoStepP R rxk ryk cs vs = autoStepPG R rxk ryk cs vs := by
  unfold autoStepP autoStepPG; rfl

theorem runAuto_eqG (P : Pt) (xs : Array ℕ) (R : ℕ) (st : Array (ℕ × FE)) :
    runAuto P xs R st = runAutoG P.toG xs R st := by
  unfold runAuto runAutoG; simp only [autoStepP_eqG, Pt.toG]

theorem finVal_eqG (T : Array (Array FE)) (p : Pass) (c : ℕ) : finVal T p c = finValG T p c := by
  unfold finVal finValG; rfl

theorem finSum_eqG (T : Array (Array FE)) (p : Pass) (fs : Array (ℕ × FE)) : finSum T p fs = finSumG T p fs := by
  unfold finSum finSumG; simp only [mulI_eqG, finVal_eqG]

theorem runPassF_eqG (P : Pt) (T : Array (Array FE)) (F : Array FE) (p : Pass) :
    runPassF P T F p = runPassFG P.toG T F p := by
  unfold runPassF runPassFG
  simp only [runF_eqG, runCode_eqG, runAuto_eqG, finSum_eqG, limbVal_eqG, Pt.toG]

/-- **The executable evaluator is the twin at `FE`.** -/
theorem evalC_eqG (c : Comp) (pt : List FE) : evalC c pt = evalCG c pt := by
  unfold evalC evalCG
  simp only [tabsAt_eqG, flatTabs_eqG, runF_eqG, runCode_eqG, runPassF_eqG]
  rfl

end Lvm.Typed.K
