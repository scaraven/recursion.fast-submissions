-- G6: this module also holds the former modules `FRSoundness4RsvMLE`, `FRSoundness4P4bNames`, `FRSoundness4P4bRows` (one section each, in import order).
import FRVerifierImplOps
import FRSoundness4Pos
import FRSoundnessCoreFront
import FRVIRTplEval
import FRVIRTplFast
import FRNodeKinds4
import FRVIRFinalsCoreSG
import FRSoundness4Frame
import FRVerifierC4
import FRSoundness4P4aNames

section G6_FRSoundness4RsvMLE

-- New for `flock-recursive` (revision 4.4.2, the reserve in RSV2's stacked form, §2.5–§2.6; track
-- RSV-S): the extension lemmas the E-phase's child term needs.

/-!
# Points continued above their coordinates, and the constant extension

The reserve's child claim is one point `p ∈ F^23 × F^25` and each node kind's matrices read it at
their own coordinates (`e2R κ` rows, `ncR κ` cells). A parent sums over its own `n` coordinates
with the claim's higher ones fixed (**the mixed point**): `x ↦ M̃(x ‖ p[n, …))`. Two facts make the
sumcheck and the spec agree (RSV2 §2.5):

* **`mle_eq_hiPt`**: for a cube index `u` on `a` bits, the extension in `x ∈ {0,1}^n` of
  `eq((x ‖ hi)[<a], u)` is `eq((r ‖ hi)[<a], u)` at `r`, whether `a ≤ n` (the table is constant in
  the coordinates `a … n − 1`: **the constant extension**) or `a > n` (the coordinates `n … a − 1`
  are fixed: **the fixed evaluation**);
* **`matMLE_hiRow`**, **`matMLE_hiCol`**: the same for a matrix MLE in its row or its column point.

`hiPt u hi` is the point `u` on `n` coordinates continued by `hi` above `n`; `lowA a p` reads the
first `a` coordinates of a point `p : ℕ → R`.
-/

namespace FR.Snd.Rsv
open RecursionFast Finset

section Gen
variable {R : Type*} [CommRing R]

/-- **The point `u` (on `n` coordinates) continued by `hi`** above `n`. -/
def hiPt {n : ℕ} (u : Fin n → R) (hi : ℕ → R) (j : ℕ) : R := if h : j < n then u ⟨j, h⟩ else hi j

/-- A point read at its first `a` coordinates. -/
def lowA (a : ℕ) (p : ℕ → R) : Fin a → R := fun j => p j

theorem hiPt_lt {n : ℕ} (u : Fin n → R) (hi : ℕ → R) {j : ℕ} (h : j < n) : hiPt u hi j = u ⟨j, h⟩ :=
  dif_pos h

theorem hiPt_ge {n : ℕ} (u : Fin n → R) (hi : ℕ → R) {j : ℕ} (h : ¬ j < n) : hiPt u hi j = hi j :=
  dif_neg h

/-- A point continued by itself is itself. -/
theorem hiPt_self {n : ℕ} (p : ℕ → R) : hiPt (lowA n p) p = p := by
  funext j; unfold hiPt lowA; split_ifs <;> rfl

/-- The per-bit factor of `eq(·, u)`. -/
def fb (u : ℕ) (j : ℕ) (c : R) : R := if u.testBit j then c else 1 - c

/-- `eq((v ‖ hi)[<a], u)` split at `n`: the coordinates below `n` and the constant ones above. -/
theorem eq_hiPt_split (a n : ℕ) (u : Fin (2 ^ a)) (hi : ℕ → R) (v : Fin n → R) :
    eq (lowA a (hiPt v hi)) (cube u) =
      (∏ l : Fin n, if (l : ℕ) < a then fb u.val l (v l) else 1) *
        ∏ j ∈ (range a).filter (fun j => ¬ j < n), fb u.val j (hi j) := by
  rw [eq_cube]
  have e1 : (∏ l : Fin a, if u.val.testBit l then lowA a (hiPt v hi) l else 1 - lowA a (hiPt v hi) l) =
      ∏ j ∈ range a, fb u.val j (hiPt v hi j) :=
    Fin.prod_univ_eq_prod_range (fun j => fb u.val j (hiPt v hi j)) a
  rw [e1, ← prod_filter_mul_prod_filter_not (range a) (fun j => j < n)]
  congr 1
  · rw [Fin.prod_univ_eq_prod_range (fun l => if l < a then fb u.val l (hiPt v hi l) else 1) n |>.symm.trans
      (Finset.prod_congr rfl fun l _ => by rw [hiPt_lt v hi l.isLt]) |>.symm]
    rw [prod_ite, prod_const_one, mul_one]
    refine prod_congr ?_ fun _ _ => rfl
    ext j; simp only [mem_filter, mem_range]; omega
  · exact prod_congr rfl fun j hj => by rw [hiPt_ge v hi (mem_filter.1 hj).2]

/-- **The extension of `eq((x ‖ hi)[<a], u)` in `x`** (`n` coordinates) is `eq((r ‖ hi)[<a], u)`:
the constant extension (`a ≤ n`) and the fixed evaluation (`a > n`) at once. -/
theorem mle_eq_hiPt (a n : ℕ) (u : Fin (2 ^ a)) (hi : ℕ → R) (r : Fin n → R) :
    mle (fun x : Fin (2 ^ n) => eq (lowA a (hiPt (cube x) hi)) (cube u)) r =
      eq (lowA a (hiPt r hi)) (cube u) := by
  simp only [mle, eq_hiPt_split, ← mul_assoc, ← sum_mul]
  congr 1
  simp only [eq_cube]
  have h := sum_cube_prod (R := R) (ℓ := n) fun l b =>
    (if b then r l else 1 - r l) * (if (l : ℕ) < a then fb u.val l (if b then 1 else 0) else 1)
  have e : ∀ x : Fin (2 ^ n), (∏ l : Fin n, if x.val.testBit l then r l else 1 - r l) *
      (∏ l : Fin n, if (l : ℕ) < a then fb u.val l (cube x l) else 1) =
      ∏ l : Fin n, (if x.val.testBit l then r l else 1 - r l) *
        (if (l : ℕ) < a then fb u.val l (if x.val.testBit l then 1 else 0) else 1) := fun x => by
    rw [← prod_mul_distrib]; rfl
  rw [sum_congr rfl fun x _ => e x, h]
  refine prod_congr rfl fun l _ => ?_
  by_cases hl : (l : ℕ) < a
  · simp only [hl, ↓reduceIte, fb, Bool.false_eq_true]
    split_ifs <;> ring
  · simp only [hl, ↓reduceIte, Bool.false_eq_true]; ring

end Gen

/-! ## Matrix MLEs -/

/-- `matMLE` as a row extension: `Σ_u eq(τ, u)·(Σ_y eq(σ, y) M[u][y])`. -/
theorem matMLE_row (E : Eval.Entries) {a b : ℕ} (τ : Fin a → F) (σ : Fin b → F) :
    Eval.matMLE E τ σ = ∑ u : Fin (2 ^ a), (∑ y : Fin (2 ^ b), eq σ (cube y) * Eval.entry E u y) *
      eq τ (cube u) := by
  unfold Eval.matMLE
  refine sum_congr rfl fun u _ => ?_
  rw [sum_mul]; exact sum_congr rfl fun y _ => by ring

/-- `matMLE` as a column extension. -/
theorem matMLE_col (E : Eval.Entries) {a b : ℕ} (τ : Fin a → F) (σ : Fin b → F) :
    Eval.matMLE E τ σ = ∑ y : Fin (2 ^ b), (∑ u : Fin (2 ^ a), eq τ (cube u) * Eval.entry E u y) *
      eq σ (cube y) := by
  unfold Eval.matMLE
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_mul]; exact sum_congr rfl fun u _ => by ring

/-- **A matrix MLE's row point continued by `hi`**: its extension in the low `n` row coordinates is
the matrix MLE at `r ‖ hi`. -/
theorem matMLE_hiRow (E : Eval.Entries) (a b n : ℕ) (hi : ℕ → F) (σ : Fin b → F) (r : Fin n → F) :
    mle (fun x : Fin (2 ^ n) => Eval.matMLE E (lowA a (hiPt (cube x) hi)) σ) r =
      Eval.matMLE E (lowA a (hiPt r hi)) σ := by
  simp only [matMLE_row]
  rw [mle_sum]
  exact sum_congr rfl fun u _ => by rw [mle_eq_hiPt]

/-- **… and its column point.** -/
theorem matMLE_hiCol (E : Eval.Entries) (a b n : ℕ) (hi : ℕ → F) (τ : Fin a → F) (r : Fin n → F) :
    mle (fun y : Fin (2 ^ n) => Eval.matMLE E τ (lowA b (hiPt (cube y) hi))) r =
      Eval.matMLE E τ (lowA b (hiPt r hi)) := by
  simp only [matMLE_col]
  rw [mle_sum]
  exact sum_congr rfl fun u _ => by rw [mle_eq_hiPt]


/-! ## Tables on continued points; E1's table -/

theorem mle_add' {n : ℕ} (f g : Fin (2 ^ n) → F) (r : Fin n → F) :
    mle (fun u => f u + g u) r = mle f r + mle g r := mle_add f g r

theorem mle_sub' {n : ℕ} (f g : Fin (2 ^ n) → F) (r : Fin n → F) :
    mle (fun u => f u - g u) r = mle f r - mle g r := mle_sub f g r

theorem mle_const {n : ℕ} (c : F) (r : Fin n → F) : mle (fun _ : Fin (2 ^ n) => c) r = c := by
  simp only [mle, ← sum_mul, eq_sum_one, one_mul]

/-- **A table read at its own `a` coordinates of a continued point** (`mle_eq_hiPt` summed). -/
theorem mle_hiTab {a n : ℕ} (g : Fin (2 ^ a) → F) (hi : ℕ → F) (r : Fin n → F) :
    mle (fun x : Fin (2 ^ n) => mle g (lowA a (hiPt (cube x) hi))) r = mle g (lowA a (hiPt r hi)) := by
  have e : ∀ q : Fin a → F, mle g q = ∑ u ∈ univ, g u * eq q (cube u) := fun q => by
    simp only [mle]; exact sum_congr rfl fun _ _ => mul_comm _ _
  simp only [e]
  rw [mle_sum]
  exact sum_congr rfl fun u _ => by rw [mle_eq_hiPt]

/-- The extension of a coordinate function is the coordinate. -/
theorem mle_coord {n : ℕ} (k : Fin n) (r : Fin n → F) : mle (fun u : Fin (2 ^ n) => cube u k) r = r k := by
  unfold mle
  simp only [eq_cube]
  have e : ∀ u : Fin (2 ^ n), (∏ l : Fin n, if u.val.testBit l then r l else 1 - r l) * cube u k =
      ∏ l : Fin n, (if u.val.testBit l then r l else 1 - r l) *
        (if l = k then (if u.val.testBit l then 1 else 0) else 1) := fun u => by
    rw [prod_mul_distrib, prod_ite_eq' univ k, if_pos (mem_univ _)]; rfl
  rw [sum_congr rfl fun u _ => e u, sum_cube_prod (fun l b =>
    (if b then r l else 1 - r l) * (if l = k then (if b then (1 : F) else 0) else 1))]
  rw [show (fun l : Fin n => (if false = true then r l else 1 - r l) *
      (if l = k then (if false = true then (1 : F) else 0) else 1) +
      (if true = true then r l else 1 - r l) * (if l = k then (if true = true then 1 else 0) else 1)) =
      fun l => if l = k then r l else 1 from funext fun l => by
        by_cases h : l = k <;> simp [h]]
  rw [prod_ite_eq' univ k, if_pos (mem_univ _)]

/-- **E1's table** on `n` coordinates (RSV2 §2.6): the residual `g` on its own `a` coordinates, plus
`D` times coordinate `k` (`η`): `t(x) = g(x[<a]) + D·x_k`. Its extension is `g̃(r[<a]) + D·r_k`. -/
def zcT {a n : ℕ} (k : Fin n) (g : Fin (2 ^ a) → F) (D : F) : Fin (2 ^ n) → F :=
  fun u => mle g (lowA a (hiPt (cube u) 0)) + D * cube u k

theorem mle_zcT {a n : ℕ} (k : Fin n) (g : Fin (2 ^ a) → F) (D : F) (r : Fin n → F) :
    mle (zcT k g D) r = mle g (lowA a (hiPt r 0)) + D * r k := by
  unfold zcT
  rw [mle_add', mle_hiTab, mle_smul, mle_coord]

/-- **E1's table is nonzero** when the residual is, or the child claim's defect is (`a ≤ k`). -/
theorem zcT_ne {a n : ℕ} (k : Fin n) (ha : a ≤ k.val) {g : Fin (2 ^ a) → F} {D : F}
    (h : g ≠ 0 ∨ D ≠ 0) : zcT k g D ≠ 0 := by
  intro h0
  have hm : ∀ r, mle (zcT k g D) r = 0 := fun r => by rw [h0]; simp [mle]
  let rv : Fin (2 ^ a) → F → Fin n → F := fun v c j =>
    if hj : j.val < a then cube v ⟨j, hj⟩ else if j = k then c else 0
  have hlow : ∀ v c, lowA a (hiPt (rv v c) 0) = cube v := fun v c => by
    funext j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.isLt (le_trans ha (le_of_lt k.isLt))
    simp only [lowA, hiPt, hj, dite_true, rv, j.isLt]
  have hk : ∀ v c, rv v c k = c := fun v c => by
    simp only [rv, show ¬ (k : ℕ) < a by omega, dite_false, if_pos]
  have hv : ∀ v c, g v + D * c = 0 := fun v c => by
    have := hm (rv v c); rwa [mle_zcT, hlow, hk, mle_cube] at this
  rcases h with h | h
  · exact h (funext fun v => by have := hv v 0; simpa using this)
  · exact h (by have h1 := hv 0 1; have h2 := hv 0 0; simp at h2; rw [h2] at h1; simpa using h1)

/-! ## Controls -/

/-- (+/−) `hiPt` keeps the point below `n` and reads `hi` above it. -/
theorem hiPt_ctl : hiPt (n := 1) (fun _ => (1 : F)) (fun _ => 0) 0 = 1 ∧
    hiPt (n := 1) (fun _ => (1 : F)) (fun _ => 0) 1 = 0 := ⟨rfl, rfl⟩

end FR.Snd.Rsv

end G6_FRSoundness4RsvMLE

section G6_FRSoundness4P4bNames

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows Lr1 … B′, §5.2; stage P4b): the
-- names of the soundness front's Lr, E, RS dooms and checks at `seq4`, fixed first so that R4 (the
-- program layer) can state its front checks against them. `FRSoundnessRows`, `FRSoundnessFrE`,
-- `FRSoundnessFrRS0`, `FRSoundnessFrW0` are the 3.x templates.
-- RET-2: import re-pointed at Core: `FRSoundnessFrPend` → `FRSoundnessCoreRows`.

/-!
# P4b's names: the front's Lr, E and RS dooms and checks at revision 4.1

**The generalisation (S-G12′ F3, ruled as O1's restatement).** The 3.x row-Spartan unit reads its
matrices off a row list (`rowMat sel rows`), `f⁽⁰⁾` off 3.x's ladder (`fF (kindOf es)`), and the
log through 3.x's `Same`. Here each of the three is a parameter:

* **`ESrc`**, an **entries source**: the `A`, `B`, `C` entries (`Eval.Entries`); `entMat E a nc`
  is the matrix (`Eval.entry`). 3.x's row list is `ESrc.ofRows rows` (`rowMat_entMat`: `rfl`), and
  the **templated, indexed rows V evaluates** (`TEval.entriesI`, as `evalMS` reads
  `nodeIRows (planOf fin)`) are `ESrc.ofIRows rows` (O1).
* **`FSrc`**, what the front reads of `(L, es)`: an abstract `Same` relation and `f⁽⁰⁾`. 3.x is
  `src3` (`Same`, `fF (kindOf es)`); revision 4.1's is T4's (the Ligerito words at `CKind`'s
  ladder), so P4b's statements are parametric in it. **`ReadsS`** is `Reads` at an `FSrc`
  (`reads_iff_readsS`).
* **The generic unit** (`…G`): the 3.x unit's dooms without a kind gate, with the real row count
  `a` and the **slot** count `A` apart (the end absorb is at `b2 + 2A`): revision 4.1's phases have
  `seq4`'s slots (Lr2 17, E2 23, E4 25), a node kind's real rounds can be fewer (`N2`: 16, 22, 24).
  The rounds' dooms are 3.x's `D3`/`D2` with a **constant** round count, so they never read a kind.

**Revision 4.1** (`seq4`'s positions, `fsStarts4_eq`): Lr1 after 169 (9 squeezes), Lr2 from 179
(17 slots), Lrend 213, Lr3 (`κ_L`) 214, E1 after 214 (12), E2 from 227 (23), Eend 273, E3 (`κ_E`)
274, E4 from 275 (25), E4 end 325, RS0 326, RS1 327 … 330, B′ 331. A node kind `κ` has `lrR κ`
(`logL`: 16/17/17) Lr rows' bits, `e2R κ` (`logM`: 22/23/23) M rows' bits and `ncR κ` (`m − 7`:
24/25/25) cell bits = E4's real rounds. The gate is **`OnNode`**: the chain's kind (`kindOfC`) is
a node kind, and the doom at that kind's dims holds. The M and L rows per node kind are S-E's
(S-G13 F3), so they are parameters `srcE srcL : NodeKind → ESrc`.

**The checks R4 discharges on an accepted run** (each reads only the log): `RejEndLr4`,
`RejEndE4` (`finLr`/`finE` (ii)), `RejInE4` (E4's rounds), `RejFinE4` (`finE` (iv)), `RejRS4 ok`
(the RS claims' bindings at the slices' values, with `okRS4`).
-/

namespace FR.Snd.P4b
open RecursionFast FR.Merkle FR.Rev4 Finset

/-! ## What the front reads -/

/-- **What the front reads of a log pair**: an abstract `Same` (the entries before `p` and the
words of earlier caps) and `f⁽⁰⁾`, which reads the level-0 word (cap at position 2). -/
structure FSrc where
  Sm : Log → Log → Log → Log → ℕ → Prop
  agree : ∀ {L es L' es' : Log} {p : ℕ}, Sm L es L' es' p → Agree es es' p
  mono : ∀ {L es L' es' : Log} {p q : ℕ}, Sm L es L' es' p → q ≤ p → Sm L es L' es' q
  ofAgree : ∀ (L : Log) {es es' : Log} {p : ℕ}, Agree es es' p → Sm L es L es' p
  fz : Log → Log → ℕ → F
  fz_same : ∀ {L es L' es' : Log} {p : ℕ}, Sm L es L' es' p → 3 ≤ p → fz L es = fz L' es'

/-- **3.x's**: `Same` and `fF` at the log's kind. -/
noncomputable def src3 : FSrc where
  Sm := Same
  agree h := h.1
  mono h hq := h.mono hq
  ofAgree L _ _ _ h := same_of_agree L h
  fz L es := fF (kindOf es) L es
  fz_same h hp := by rw [h.kind (by omega)]; exact fF_same h hp _

/-- **`Reads` at an `FSrc`**: `P` reads only what lies before `p`. -/
def ReadsS (R : FSrc) (p : ℕ) (P : Log → Log → Prop) : Prop :=
  ∀ L es L' es', p ≤ es.length → p ≤ es'.length → R.Sm L es L' es' p → (P L es ↔ P L' es')

theorem reads_iff_readsS {p : ℕ} {P : Log → Log → Prop} : Reads p P ↔ ReadsS src3 p P := Iff.rfl

/-! ## Entries sources -/

/-- **An entries source**: the `A`, `B`, `C` entries `(row, cell, coefficient)`. -/
structure ESrc where
  ea : Eval.Entries
  eb : Eval.Entries
  ec : Eval.Entries

/-- The matrix of entries over `2^a` rows and `2^nc` cells. -/
def entMat (E : Eval.Entries) (a nc : ℕ) : Fin (2 ^ a) → Fin (2 ^ nc) → F :=
  fun x y => Eval.entry E x y

/-- 3.x's row list (`Eval.entriesOf`: row `i` at index `i`). -/
def ESrc.ofRows (rows : List Circ.Row) : ESrc :=
  ⟨Eval.entriesOf Circ.Row.a rows, Eval.entriesOf Circ.Row.b rows, Eval.entriesOf Circ.Row.c rows⟩

/-- **Indexed rows** (`TEval.entriesI`: row `(i, r)` at index `i`), as `evalMS` reads them. -/
def ESrc.ofIRows (rows : List (ℕ × Circ.Row)) : ESrc :=
  ⟨TEval.entriesI .a rows, TEval.entriesI .b rows, TEval.entriesI .c rows⟩

theorem rowMat_entMat (sel : Circ.Row → Circ.Lin) (rows : List Circ.Row) (a b : ℕ) :
    rowMat sel rows a b = entMat (Eval.entriesOf sel rows) a b := rfl

/-! ## The generic unit (no kind gate; `a` real rows, `A` slots) -/

section Unit
variable (R : FSrc) (E : ESrc) (a nc : ℕ)

/-- `f⁽⁰⁾` on `2^nc` cells. -/
def zCG (L es : Log) : Fin (2 ^ nc) → F := fun y => R.fz L es y

/-- **The unit's statement fails**: `f⁽⁰⁾` violates the source's R1CS. -/
def RowsBadG (L es : Log) : Prop :=
  ¬ Sat (entMat E.ea a nc) (entMat E.eb a nc) (entMat E.ec a nc) (zCG R nc L es)

variable (s0 b2 A : ℕ)

/-- **The zerocheck's final doom**: the residual's extension at the point is nonzero. -/
def ZCwG (L es : Log) : Prop :=
  mle (residual (entMat E.ea a nc) (entMat E.eb a nc) (entMat E.ec a nc) (zCG R nc L es))
    (ptOf a (tauS a s0 es)) ≠ 0

/-- The outer tables `eq(τ, ·)`, `Az`, `Bz`, `Cz`. -/
noncomputable def T3G (L es : Log) : Array (Array F) :=
  outerTables (tauS a s0 es) (entMat E.ea a nc) (entMat E.eb a nc) (entMat E.ec a nc)
    (zCG R nc L es)

/-- **The outer rounds' doom** (3.x's `D3`, `a` rounds from `b2`, claim `0`). -/
abbrev D3G : Log → Log → Prop :=
  D3 b2 (fun _ _ => 0) (fun _ => a) outerExpr (T3G R E a nc s0)

/-- The true triple at the outer rounds' point. -/
noncomputable def triTG (L es : Log) : F × F × F :=
  (mle (matVec (entMat E.ea a nc) (zCG R nc L es)) (ptOf a (rxs a b2 es)),
   mle (matVec (entMat E.eb a nc) (zCG R nc L es)) (ptOf a (rxs a b2 es)),
   mle (matVec (entMat E.ec a nc) (zCG R nc L es)) (ptOf a (rxs a b2 es)))

/-- **A wrong triple** after the end absorb (at `b2 + 2A`). -/
noncomputable def EndBadG (L es : Log) : Prop :=
  b2 + 2 * A < es.length ∧ (vEnd A b2 es 0, vEnd A b2 es 1, vEnd A b2 es 2) ≠ triTG R E a nc b2 L es

/-- The inner tables `M̃_κ(r, ·)` and `z`. -/
noncomputable def T4G (L es : Log) : Array (Array F) :=
  innerTables (ptOf a (rxs a b2 es)) (kapB A b2 es) (entMat E.ea a nc) (entMat E.eb a nc)
    (entMat E.ec a nc) (zCG R nc L es)

/-- **A false batched claim** after `κ` (at `b2 + 2A + 1`). -/
noncomputable def BatBadG (L es : Log) : Prop :=
  b2 + 2 * A + 1 < es.length ∧ c4 A b2 L es ≠ trueSum innerExpr (T4G R E a nc b2 A L es) nc

end Unit

/-- **The end check fails** (`finLr`/`finE` (ii)): the outer claim after `a` rounds is not
`eq(τ, r)·(â b̂ + ĉ)`, the triple absorbed at `b2 + 2A`. -/
def RejEndG (a s0 b2 A : ℕ) (L es : Log) : Prop :=
  b2 + 2 * A < es.length ∧
    clR b2 (fun _ _ => 0) L es a ≠ eq (ptOf a (tauS a s0 es)) (ptOf a (rxs a b2 es)) *
      (vEnd A b2 es 0 * vEnd A b2 es 1 + vEnd A b2 es 2)

/-! ## Revision 4.1: the node kinds' dims and the gate -/

/-- A node kind's Lr row bits (`logL`), M row bits (`logM`), cell bits (`m − 7`). -/
def lrR (κ : NodeKind) : ℕ := κ.dims.logL
def e2R (κ : NodeKind) : ℕ := κ.dims.logM
def ncR (κ : NodeKind) : ℕ := κ.m - 7

/-- **The node gate**: the chain's kind is a node kind `κ`, and `P κ` holds. -/
def OnNode (P : NodeKind → Log → Log → Prop) (L es : Log) : Prop :=
  ∃ κ, kindOfC es = .node κ ∧ P κ L es

/-! ## Lr (Lr1 after 169, Lr2 from 179, 17 slots; Lrend 213; Lr3 214) -/

section Lr
variable (R : FSrc) (srcL : NodeKind → ESrc)

def RowsBadLr4 : Log → Log → Prop := OnNode fun κ => RowsBadG R (srcL κ) (lrR κ) (ncR κ)
def ZCwLr4 : Log → Log → Prop := OnNode fun κ => ZCwG R (srcL κ) (lrR κ) (ncR κ) 169
def D3Lr4 : Log → Log → Prop := OnNode fun κ => D3G R (srcL κ) (lrR κ) (ncR κ) 169 179
def EndBadLr4 : Log → Log → Prop := OnNode fun κ => EndBadG R (srcL κ) (lrR κ) (ncR κ) 179 17
def BatBadLr4 : Log → Log → Prop := OnNode fun κ => BatBadG R (srcL κ) (lrR κ) (ncR κ) 179 17

end Lr

/-- **Lr's end check** (`finLr` (ii); Lrend at 213). -/
def RejEndLr4 : Log → Log → Prop := OnNode fun κ => RejEndG (lrR κ) 169 179 17

/-! ## E (E1 after 214, E2 from 227, 23 slots; Eend 273; E3 274; E4 from 275, 25 slots; 325) -/

/-! ### The reserve's child claim (revision 4.4.2; RSV2 §2.1, §2.6)

A node's proof carries one claim about the previous node, `X = Σ_i s_i·M̃_i(p)` over the nine
matrices of the three node kinds (`i = 3·κ.ix + m`, each read at its own coordinates), in Lrend's
message (213, from byte 48): the point `p = (p_x, p_y) ∈ F^23 × F^25`, the coefficients `s`, the
value `X`. E2 is a zerocheck **plus** this linear claim, batched by `η` (E1's coordinate 23), and E4
carries `m̂*` (Eend's message at 273, byte 48) batched by `κ_E⁴`. -/

/-- The child claim's row coordinates `p_x` (23), column coordinates `p_y` (25), coefficients `s`
(9) and value `X` (Lrend's message at 213; `FRVIRFinals4.rsvRx`, `rsvRy`, `rsvS`, `rsvX`). -/
def pxL (es : Log) (j : ℕ) : F := readF (msgAt es 213) (48 + 16 * j)
def pyL (es : Log) (j : ℕ) : F := readF (msgAt es 213) (416 + 16 * j)
def sL (es : Log) (i : ℕ) : F := readF (msgAt es 213) (816 + 16 * i)
def xL (es : Log) : F := readF (msgAt es 213) 960

/-- `m̂*` (Eend's message at 273, byte 48). -/
def mStL (es : Log) : F := readF (msgAt es 273) 48

/-- `η`: E1's coordinate 23 (for every node kind). -/
def etaL (es : Log) : F := coordAt es 214 23

/-- **The stacked matrix's extension** at a row point `p` and a column point `q` (coordinate
functions), with coefficients `s`: `Σ_κ Σ_m s_{3·κ.ix + m}·M̃_{κ,m}(p, q)`, kind `κ`'s matrices read
at its own `e2R κ` row and `ncR κ` column coordinates (RSV2 §2.1). -/
noncomputable def mStack (srcE : NodeKind → ESrc) (s : ℕ → F) (p q : ℕ → F) : F :=
  (NodeKind.all.map fun κ =>
    s (3 * κ.ix) * Eval.matMLE (srcE κ).ea (Rsv.lowA (e2R κ) p) (Rsv.lowA (ncR κ) q) +
    s (3 * κ.ix + 1) * Eval.matMLE (srcE κ).eb (Rsv.lowA (e2R κ) p) (Rsv.lowA (ncR κ) q) +
    s (3 * κ.ix + 2) * Eval.matMLE (srcE κ).ec (Rsv.lowA (e2R κ) p) (Rsv.lowA (ncR κ) q)).sum

/-- **The child claim is true** (RSV2 §2.6): `X = Σ_i s_i·M̃_i(p)`. -/
def truthChild4 (srcE : NodeKind → ESrc) (es : Log) : Prop :=
  xL es = mStack srcE (sL es) (pxL es) (pyL es)

/-- The child claim's defect `D = Σ_i s_i·M̃_i(p) − X`. -/
noncomputable def dChild (srcE : NodeKind → ESrc) (es : Log) : F :=
  mStack srcE (sL es) (pxL es) (pyL es) - xL es

/-- **The child claim is false** (after Lrend): joins `nE4` in E1's escape. -/
def ChildBad4 (srcE : NodeKind → ESrc) : Log → Log → Prop :=
  OnNode fun _ _ es => 214 ≤ es.length ∧ ¬ truthChild4 srcE es

/-- The mixed row point `x̂ = r_E2 ‖ p_x[e2R, 23)` (E2's real challenges, then the claim's). -/
def xHat (κ : NodeKind) (es : Log) : ℕ → F := Rsv.hiPt (ptOf (e2R κ) (rxs (e2R κ) 227 es)) (pxL es)

/-- E2's summand `eq(τ, x)(Az·Bz + Cz)(x) + η·eq(p_x, x)·Y(x)` (degree 3). -/
def outerExprR : Expr := .add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3))) (.mul (.var 4) (.var 5))

/-- E4's summand `W(y)·z(y) + κ_E⁴·eq(p_y, y)·C(y)` (degree 2). -/
def innerExprR : Expr := .add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))

section E
variable (R : FSrc) (srcE srcL : NodeKind → ESrc)

/-- **E's statement fails** (A.10 E1, O1): `f⁽⁰⁾` violates the node kind's M rows. -/
def nE4 : Log → Log → Prop := OnNode fun κ => RowsBadG R (srcE κ) (e2R κ) (ncR κ)

/-- **E1's doom** (RSV2 §2.6): the zerocheck polynomial plus the child term, `F̃(τ) + η·D`, is
nonzero at the drawn `(τ, η)`. -/
def ZCwE4 : Log → Log → Prop := OnNode fun κ L es =>
  mle (residual (entMat (srcE κ).ea (e2R κ) (ncR κ)) (entMat (srcE κ).eb (e2R κ) (ncR κ))
      (entMat (srcE κ).ec (e2R κ) (ncR κ)) (zCG R (ncR κ) L es)) (ptOf (e2R κ) (tauS (e2R κ) 214 es)) +
    etaL es * dChild srcE es ≠ 0

/-- **E2's tables**: the outer ones (`eq(τ, ·)`, `Az`, `Bz`, `Cz`), then `η·eq(p_x, ·)` and
`Y(x) = Σ_i s_i·M̃_i(x ‖ p_x[e2R, 23), p_y) − X`. -/
noncomputable def T3E4 (κ : NodeKind) (L es : Log) : Array (Array F) :=
  #[eqTable (tauS (e2R κ) 214 es),
    Array.ofFn (matVec (entMat (srcE κ).ea (e2R κ) (ncR κ)) (zCG R (ncR κ) L es)),
    Array.ofFn (matVec (entMat (srcE κ).eb (e2R κ) (ncR κ)) (zCG R (ncR κ) L es)),
    Array.ofFn (matVec (entMat (srcE κ).ec (e2R κ) (ncR κ)) (zCG R (ncR κ) L es)),
    Array.ofFn fun x : Fin (2 ^ e2R κ) => etaL es * eq (Rsv.lowA (e2R κ) (pxL es)) (cube x),
    Array.ofFn fun x : Fin (2 ^ e2R κ) =>
      mStack srcE (sL es) (Rsv.hiPt (cube x) (pxL es)) (pyL es) - xL es]

/-- **E2's doom** (the outer rounds over E2's tables, claim `0`). -/
def D3E4 : Log → Log → Prop :=
  OnNode fun κ => D3 227 (fun _ _ => 0) (fun _ => e2R κ) outerExprR (T3E4 R srcE κ)

/-- `m̂*`'s true value: the stacked extension at the mixed point `(x̂, p_y)`. -/
noncomputable def mHatT (κ : NodeKind) (es : Log) : F := mStack srcE (sL es) (xHat κ es) (pyL es)

/-- **A wrong quadruple** after Eend (273): `(â, b̂, ĉ)` or `m̂*`. -/
noncomputable def EndBadE4 : Log → Log → Prop := OnNode fun κ L es =>
  273 < es.length ∧ ((vEnd 23 227 es 0, vEnd 23 227 es 1, vEnd 23 227 es 2) ≠
    triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es ∨ mStL es ≠ mHatT srcE κ es)

/-- **E4's initial claim** (`finE` (iii″)): `â_M + κ_E b̂_M + κ_E² ĉ_M + κ_E³ v_L + κ_E⁴ m̂*`. -/
def c4E4 (L es : Log) : F :=
  c4 23 227 L es + kapB 23 227 es ^ 3 * c4 17 179 L es + kapB 23 227 es ^ 4 * mStL es

/-- **E4's weight** (`evalM`, `evalL` at `r′`): M's batched by `κ_E`, plus `κ_E³` times Lr's batched
by `κ_L`. -/
noncomputable def wEb4 (κ : NodeKind) (es : Log) (y : Fin (2 ^ ncR κ)) : F :=
  wInn (entMat (srcE κ).ea (e2R κ) (ncR κ)) (entMat (srcE κ).eb (e2R κ) (ncR κ))
      (entMat (srcE κ).ec (e2R κ) (ncR κ)) (ptOf (e2R κ) (rxs (e2R κ) 227 es)) (kapB 23 227 es) y +
    kapB 23 227 es ^ 3 * wInn (entMat (srcL κ).ea (lrR κ) (ncR κ))
      (entMat (srcL κ).eb (lrR κ) (ncR κ)) (entMat (srcL κ).ec (lrR κ) (ncR κ))
      (ptOf (lrR κ) (rxs (lrR κ) 179 es)) (kapB 17 179 es) y

/-- E4's child table `C(y) = Σ_i s_i·M̃_i(x̂, y ‖ p_y[ncR, 25))`. -/
noncomputable def cTab4 (κ : NodeKind) (es : Log) (y : Fin (2 ^ ncR κ)) : F :=
  mStack srcE (sL es) (xHat κ es) (Rsv.hiPt (cube y) (pyL es))

/-- E4's tables `[wEb4, z, κ_E⁴·eq(p_y, ·), C]`. -/
noncomputable def TEb4 (κ : NodeKind) (L es : Log) : Array (Array F) :=
  #[Array.ofFn (wEb4 srcE srcL κ es), Array.ofFn (zCG R (ncR κ) L es),
    Array.ofFn fun y : Fin (2 ^ ncR κ) => kapB 23 227 es ^ 4 * eq (Rsv.lowA (ncR κ) (pyL es)) (cube y),
    Array.ofFn (cTab4 srcE κ es)]

/-- **E3's doom**: the batched claim is false after `κ_E`. -/
noncomputable def BatBadE4 : Log → Log → Prop :=
  OnNode fun κ L es => 274 < es.length ∧ c4E4 L es ≠ trueSum innerExprR (TEb4 R srcE srcL κ L es) (ncR κ)

/-- E4's rounds at node kind `κ` (F, degree 2, from 275, `ncR κ` real rounds). -/
abbrev D2Eb4 (κ : NodeKind) : Log → Log → Prop :=
  D2 275 16 readF (fun d => chF d 0) c4E4 (fun _ => ncR κ) innerExprR (TEb4 R srcE srcL κ)

/-- **E4's doom**. -/
def D4E4 : Log → Log → Prop := OnNode (D2Eb4 R srcE srcL)

end E

/-- **E's end check** (`finE` (ii″); Eend at 273): the outer claim after `e2R κ` rounds is not
`eq(τ, r)·(â b̂ + ĉ) + η·eq(p_x, r)·(m̂* − X)`. -/
def RejEndE4 : Log → Log → Prop := OnNode fun κ L es =>
  273 < es.length ∧ clR 227 (fun _ _ => 0) L es (e2R κ) ≠
    eq (ptOf (e2R κ) (tauS (e2R κ) 214 es)) (ptOf (e2R κ) (rxs (e2R κ) 227 es)) *
      (vEnd 23 227 es 0 * vEnd 23 227 es 1 + vEnd 23 227 es 2) +
    etaL es * eq (Rsv.lowA (e2R κ) (pxL es)) (ptOf (e2R κ) (rxs (e2R κ) 227 es)) * (mStL es - xL es)

/-- **E4's round checks fail** (`finE`'s rounds: `g(0) + g(1)` against the running claim). -/
def RejInE4 : Log → Log → Prop :=
  OnNode fun κ L es => ∃ l < ncR κ, 275 + 2 * l < es.length ∧
    ¬ Chk2 275 16 readF (fun d => chF d 0) c4E4 L es l

/-- The binding of E's RS claim (`finE` (v)): its value is E4 end's message. -/
def okE4 (es : Log) (v : F) : Prop := v = readF (msgAt es 325) 0

/-- E4's point `r′` (the real rounds' challenges). -/
def rPt4 (κ : NodeKind) (es : Log) : List F := rchs2 275 (fun d => chF d 0) es (ncR κ)

/-- **`finE` (iv″) fails** (from 326): E4's last claim is not
`W(r′)·α_E + κ_E⁴·eq(p_y, r′)·Σ_i s_i·M̃_i(x̂, ŷ)`, `ŷ = r′ ‖ p_y[ncR, 25)`. -/
noncomputable def RejFinE4 (srcE srcL : NodeKind → ESrc) : Log → Log → Prop :=
  OnNode fun κ L es => 326 ≤ es.length ∧
    clR2 275 16 readF (fun d => chF d 0) c4E4 L es (ncR κ) ≠
      mle (wEb4 srcE srcL κ es) (ptOf (ncR κ) (rPt4 κ es)) * readF (msgAt es 325) 0 +
      kapB 23 227 es ^ 4 * eq (Rsv.lowA (ncR κ) (pyL es)) (ptOf (ncR κ) (rPt4 κ es)) *
        mStack srcE (sL es) (xHat κ es) (Rsv.hiPt (ptOf (ncR κ) (rPt4 κ es)) (pyL es))

/-- **E's pending claim is false** (after E4 end): its value is not `ẑ(r′)`. -/
noncomputable def PendE4 (R : FSrc) : Log → Log → Prop :=
  OnNode fun κ L es => 325 < es.length ∧ ¬ okE4 es (mle (zCG R (ncR κ) L es) (ptOf (ncR κ) (rPt4 κ es)))

/-! ## RS0 (326) and the claims' bindings -/

/-- Sh's low point: S2's challenges `m − 14 … m − 8`. -/
def xSL4 (κ : CKind) (es : Log) : List F := (List.range 7).map fun l => rch 114 es (κ.m - 14 + l)

/-- The inner weights `c_{j,i}` on the log (`cwF`). -/
def cwL4 (κ : CKind) (es : Log) (j i : ℕ) : F := cwF (fAt es 14 0) (xLL es) (xSL4 κ es) j i

/-- E4's claim point: its `n` real challenges. -/
def ePtL4 (n : ℕ) (es : Log) : List F := (List.range n).map (rch 275 es)

/-- **The RS claim points** (`gPfPts`' claims at the kind's `m`): Z, Lc, Sh; E4's `r′` on a node. -/
def rsPtsL4 (κ : CKind) (es : Log) : List (List F) :=
  [zPtL κ.m es, lcPtL κ.m es, shPtL κ.m es] ++
    match κ with
    | .node ν => [ePtL4 (ncR ν) es]
    | .seg _ => []

/-- Slice `i` of RS claim `j` (RS0's message at 326). -/
def sliceL4 (es : Log) (j i : ℕ) : F := readF (msgAt es 326) (rsOff j i)

/-- Claim `j`'s slices (`0` for a segment's fourth claim). -/
def sL4 (κ : CKind) (es : Log) (j : Fin 4) (i : Fin 128) : F :=
  if j.val < (rsPtsL4 κ es).length then sliceL4 es j i else 0

/-- **Claim `j`'s value from RS0's slices** (`rsAlpha`). -/
def alphaL4 (κ : CKind) (es : Log) (j : Fin 4) : F := ∑ i : Fin 128, cwL4 κ es j i * sL4 κ es j i

/-- **RS0's bindings**: Z's, Lc's, Sh's are parameters (P4a's `finZ`, `finLc`, `finSh`); E's is
`okE4`. -/
def okRS4 (oZ oLc oSh : CKind → Log → F → Prop) (κ : CKind) (es : Log) (j : ℕ) (v : F) : Prop :=
  match j with
  | 0 => oZ κ es v
  | 1 => oLc κ es v
  | 2 => oSh κ es v
  | _ => okE4 es v

/-- **`RejF`'s slice part** (from 327): some claim's binding fails at the slices' value. -/
def RejRS4 (ok : CKind → Log → ℕ → F → Prop) (_L es : Log) : Prop :=
  327 ≤ es.length ∧ ∃ j : Fin 4, j.val < (rsPtsL4 (kindOfC es) es).length ∧
    ¬ ok (kindOfC es) es j (alphaL4 (kindOfC es) es j)

/-! ## Controls -/

/-- (+) 3.x's end check is the generic one at `A = a`, under 3.x's gate. -/
theorem rejEnd_eq_G {a s0 b2 : ℕ} {on : Kind → Bool} (L es : Log) :
    RejEnd a on s0 b2 L es ↔ on (kindOf es) = true ∧ RejEndG a s0 b2 a L es := Iff.rfl

/-- (+) 3.x's wrong triple is the generic one at `src3` and its row list. -/
theorem endBad_eq_G {rows : List Circ.Row} {a nc b2 : ℕ} {on : Kind → Bool} (L es : Log) :
    EndBad rows a nc on b2 L es ↔
      on (kindOf es) = true ∧ EndBadG src3 (ESrc.ofRows rows) a nc b2 a L es := Iff.rfl

/-- (+) 3.x's statement doom is the generic one. -/
theorem rowsBad_eq_G {rows : List Circ.Row} {a nc : ℕ} {on : Kind → Bool} (L es : Log) :
    RowsBad rows a nc on L es ↔ on (kindOf es) = true ∧ RowsBadG src3 (ESrc.ofRows rows) a nc L es :=
  Iff.rfl

/-- (+) The dims per node kind (`coords_eq`, `NodeKind.dims`). -/
theorem dims_ctrl : (lrR .N2, e2R .N2, ncR .N2) = (16, 22, 24) ∧
    (lrR .N4, e2R .N4, ncR .N4) = (17, 23, 25) ∧ (lrR .N8, e2R .N8, ncR .N8) = (17, 23, 25) :=
  ⟨rfl, rfl, rfl⟩

/-- (+) Every real count fits `seq4`'s slots (Lr 17, E2 23, E4 25). -/
theorem dims_le (κ : NodeKind) : lrR κ ≤ seq4.lr ∧ e2R κ ≤ seq4.e2 ∧ ncR κ ≤ seq4.e4 := by
  rw [seq4_eq]; cases κ <;> decide

/-- (−) On a segment's chain every gated doom and check is false. -/
theorem not_onNode_seg {P : NodeKind → Log → Log → Prop} {L es : Log} {σ : SegKind}
    (h : kindOfC es = .seg σ) : ¬ OnNode P L es := by
  rintro ⟨κ, hk, -⟩; rw [h] at hk; cases hk

/-- (+) On a node's chain the gate is the kind's doom. -/
theorem onNode_iff {P : NodeKind → Log → Log → Prop} {L es : Log} {κ : NodeKind}
    (h : kindOfC es = .node κ) : OnNode P L es ↔ P κ L es :=
  ⟨fun ⟨ν, hν, hp⟩ => by rw [h] at hν; cases hν; exact hp, fun hp => ⟨κ, h, hp⟩⟩

/-- (+/−) A node's four RS claims, a segment's three. -/
theorem rsPtsL4_length (κ : CKind) (es : Log) :
    (rsPtsL4 κ es).length = if κ.isNode then 4 else 3 := by
  cases κ <;> rfl

/-- (+) E4's claim point has the kind's real count of coordinates (`N2`: 24, not `seq4`'s 25). -/
theorem rPt4_length (κ : NodeKind) (es : Log) : (rPt4 κ es).length = ncR κ := by
  simp [rPt4, rchs2]

end FR.Snd.P4b

end G6_FRSoundness4P4bNames

section G6_FRSoundness4P4bRows

-- New for `flock-recursive` (BLUEPRINT A.10 rows Lr1–Lr3 and E1–E4, §5.2; stage P4b): the row
-- Spartan unit of `FRSoundnessRows` over an entries source, an abstract `FSrc` and separate real
-- and slot counts, and O1 (the E truth over indexed rows, as `evalMS` reads `nodeIRows`).

/-!
# The row Spartan unit over an entries source (P4b), and O1

The unit's dooms (`FRSoundness4P4bNames`: `RowsBadG`, `ZCwG`, `D3G`, `EndBadG`, `BatBadG`, the check
`RejEndG`) with their obligations, as `FRSoundnessRows` proves them for 3.x, now over any `FSrc` `R`
and entries source `E`, `a` real rows' bits, `nc` cell bits, the zerocheck after `s0`, `A` outer
slots from `b2` (end absorb at `b2 + 2A`, `a ≤ A`):

* **reads** (`ReadsS`): `rowsBadG_reads`, `zcwG_reads`, `endBadG_reads`, `batBadG_reads`,
  `D3G_reads` (once every slot is answered), `rejEndG_reads`; locality `T3G_local`;
* **the zerocheck's charge** `zcG_count` (`ml_round_le`, `≤ a/2^128`): the count of any phase doom
  whose escapes clear `ZCwG`, from `RowsBadG` at the phase's entry;
* **the handoffs**: `habsG_outer` (into the rounds), `habsG_end` (at the end absorb: `RejEndG` or a
  wrong triple), `singleG_batch` (`≤ 2·2^128` answers at `κ`), `singleG_outer`, `outerG_append`;
* **checks**: `RejLog4` (monotone, unchanged at a `seq4` squeeze, independent of the charging log),
  `rejEndG_log`.

**O1** (ruling S-N1 O1, S-G12′ F3): **`truthEI rows w`** (every indexed row holds at `w`) and
**`sat_entMatI_iff`**: on indexed rows that fit (`RowsFitI`: indices distinct and `< 2^a`, cells
`< 2^b`), the R1CS of `ESrc.ofIRows rows`, the matrices `evalMS` evaluates, is "every row holds".
`matMle_entMat` (the unit's `matMle` is `Eval.matMLE`, `evalMS`'s value) and `mle_wInn` bridge the
E4 weight to the verifier's `evalM`/`evalL`. 3.x instances: `truthE3_iffI` (the E truth at
`nodeIRows (planOf fin)`) and `sat_ofRows_iff` (3.x's `sat_rowMat_iff` at `ESrc.ofRows`).
-/

namespace FR.Snd.P4b
open RecursionFast FR.Merkle FR.Rev4 Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## `ReadsS` -/

section ReadsS
variable {R : FSrc} {p : ℕ} {P Q : Log → Log → Prop}

theorem ReadsS.mono (h : ReadsS R p P) {q : ℕ} (hq : p ≤ q) : ReadsS R q P :=
  fun L es L' es' h1 h2 hS => h L es L' es' (by omega) (by omega) (R.mono hS hq)

theorem ReadsS.or (hP : ReadsS R p P) (hQ : ReadsS R p Q) : ReadsS R p fun L es => P L es ∨ Q L es :=
  fun L es L' es' h1 h2 hS => or_congr (hP L es L' es' h1 h2 hS) (hQ L es L' es' h1 h2 hS)

theorem ReadsS.not (hP : ReadsS R p P) : ReadsS R p fun L es => ¬ P L es :=
  fun L es L' es' h1 h2 hS => not_congr (hP L es L' es' h1 h2 hS)

/-- Appending to a chain of at least `p` entries does not change `P`. -/
theorem ReadsS.append (h : ReadsS R p P) (L es xs : Log) (hp : p ≤ es.length) :
    P L (es ++ xs) ↔ P L es :=
  h L _ L es (by simp; omega) hp (R.ofAgree L (agree_append es xs hp))

/-- A predicate of the log alone reads at any `R`. -/
theorem readsS_of_agree (h : ∀ L es L' es', Agree es es' p → (P L es ↔ P L' es')) : ReadsS R p P :=
  fun L es L' es' _ _ hS => h L es L' es' (R.agree hS)

end ReadsS

/-! ## Checks that read only the log -/

/-- **A check at revision 4.1** (T4's `RejOK` without its `stab`, which a log-only check meets for
any charging log): monotone, unchanged by an entry at a `seq4` squeeze, independent of `L`. -/
structure RejLog4 (Rej : Log → Log → Prop) : Prop where
  mono : ∀ L es x, Rej L es → Rej L (es ++ [x])
  sq : ∀ L es x, fsItems4[es.length]? = some .squeeze → (Rej L (es ++ [x]) ↔ Rej L es)
  log : ∀ L L' es, Rej L es ↔ Rej L' es

/-- A check that reads the log before `q` and whose position `q − 1` is not a squeeze. -/
theorem rejLog4_of {Rej : Log → Log → Prop} {q : ℕ} (hq : 1 ≤ q)
    (hlen : ∀ L es, Rej L es → q ≤ es.length)
    (hreads : ∀ L es L' es', q ≤ es.length → q ≤ es'.length → Agree es es' q →
      (Rej L es ↔ Rej L' es'))
    (hpe : fsItems4[q - 1]? ≠ some .squeeze) : RejLog4 Rej where
  mono L es x h := (hreads L (es ++ [x]) L es (by simp; have := hlen L es h; omega) (hlen L es h)
    (agree_append es [x] (hlen L es h))).mpr h
  sq L es x hit := by
    by_cases hle : q ≤ es.length
    · exact hreads L (es ++ [x]) L es (by simp; omega) hle (agree_append es [x] hle)
    · constructor
      · intro h
        have h1 := hlen L _ h
        simp only [List.length_append, List.length_singleton] at h1
        rw [show es.length = q - 1 by omega] at hit
        exact absurd hit hpe
      · intro h; exact absurd (hlen L es h) hle
  log L L' es := by
    by_cases hle : q ≤ es.length
    · exact hreads L es L' es hle hle (fun _ _ => rfl)
    · exact ⟨fun h => absurd (hlen L es h) hle, fun h => absurd (hlen L' es h) hle⟩

/-! ## The unit's lemmas -/

section Unit
variable (R : FSrc) (E : ESrc) (a nc : ℕ)

theorem zCG_same {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp : 3 ≤ p) :
    zCG R nc L es = zCG R nc L' es' := by
  funext y; simp only [zCG, R.fz_same h hp]

theorem rowsBadG_reads : ReadsS R 3 (RowsBadG R E a nc) :=
  fun L es L' es' _ _ h => by simp only [RowsBadG, zCG_same R nc h le_rfl]

variable (s0 b2 A : ℕ)

theorem zcwG_reads (hp : 3 ≤ s0 + 1 + (a + 1) / 2) :
    ReadsS R (s0 + 1 + (a + 1) / 2) (ZCwG R E a nc s0) :=
  fun L es L' es' _ _ h => by
    simp only [ZCwG, zCG_same R nc h hp, tauS_agree (R.agree h) le_rfl]

theorem T3G_same {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp3 : 3 ≤ p)
    (hs : s0 + 1 + (a + 1) / 2 ≤ p) : T3G R E a nc s0 L es = T3G R E a nc s0 L' es' := by
  simp only [T3G, zCG_same R nc h hp3, tauS_agree (R.agree h) hs]

/-- The outer tables read the entries before `b2`. -/
theorem T3G_local (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) :
    TruthLocal b2 (fun _ _ => 0) (T3G R E a nc s0) := fun L _ _ h =>
  ⟨T3G_same R E a nc s0 (R.ofAgree L h) h3 hs, rfl⟩

theorem T3G_size (L es : Log) :
    ∀ t ∈ T3G R E a nc s0 L es, t.size = 2 ^ (fun _ : Kind => a) (kindOf es) :=
  outer_sizes _ (by simp [tauS]) _ _ _ _

theorem triTG_same {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp3 : 3 ≤ p)
    (hp : b2 + 2 * a ≤ p) : triTG R E a nc b2 L es = triTG R E a nc b2 L' es' := by
  simp only [triTG, zCG_same R nc h hp3, rxs_agree (R.agree h) hp]

theorem endBadG_reads (h3 : 3 ≤ b2) (haA : a ≤ A) :
    ReadsS R (b2 + 2 * A + 1) (EndBadG R E a nc b2 A) := fun L es L' es' h1 h2 h => by
  simp only [EndBadG, triTG_same R E a nc b2 h (by omega) (by omega : b2 + 2 * a ≤ b2 + 2 * A + 1),
    vEnd_agree (R.agree h) le_rfl]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

theorem T4G_same {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp3 : 3 ≤ p)
    (haA : a ≤ A) (hp : b2 + 2 * A + 2 ≤ p) :
    T4G R E a nc b2 A L es = T4G R E a nc b2 A L' es' := by
  simp only [T4G, zCG_same R nc h hp3, rxs_agree (R.agree h) (by omega : b2 + 2 * a ≤ p),
    kapB_agree (R.agree h) hp]

theorem batBadG_reads (h3 : 3 ≤ b2) (haA : a ≤ A) :
    ReadsS R (b2 + 2 * A + 2) (BatBadG R E a nc b2 A) := fun L es L' es' h1 h2 h => by
  simp only [BatBadG, T4G_same R E a nc b2 A h (by omega) haA le_rfl,
    c4_agree (L := L) (L' := L') (R.agree h) le_rfl]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

/-! ### The zerocheck's charge -/

open Classical in
/-- **The zerocheck's charge** (A.10 Lr1/E1, `ml_round_le`): if the statement fails at the phase's
entry and every escape of `D` over the phase's `r` squeezes clears `ZCwG`, the phase costs at most
`a/2^128`. -/
theorem zcG_count {D : Log → Log → Prop} {L es₀ : Log} {r : ℕ} (hl : es₀.length = s0 + 1)
    (h2 : 2 ≤ s0) (ha : a ≤ r * 2) (hd : RowsBadG R E a nc L es₀)
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      ¬ ZCwG R E a nc s0 L (ext es₀ as)) :
    condCount D L es₀ r [] ≤ (a : ℝ≥0) / 2 ^ 128 := by
  set t := Array.ofFn (residual (entMat E.ea a nc) (entMat E.eb a nc) (entMat E.ec a nc)
    (zCG R nc L es₀))
  have ht : t.size = 2 ^ a := by simp [t]
  refine ml_round_le hl ha ht (zc_start hd) fun as has he => ?_
  have hnf := hesc as has he
  obtain ⟨ys, hy⟩ := ext_eq_append es₀ as
  have hag : Agree (ext es₀ as) es₀ (s0 + 1) := by rw [hy, ← hl]; exact agree_append es₀ ys le_rfl
  have hz : zCG R nc L (ext es₀ as) = zCG R nc L es₀ := zCG_same R nc (R.ofAgree L hag) (by omega)
  have hlen : a ≤ (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j).length := by
    simp; omega
  rw [mlDoom_full t ht _ hlen, tbl_ofFn]
  intro hm
  apply hnf
  unfold ZCwG
  rw [hz]
  rwa [take_ofFn_coord (ext es₀ as) ha] at hm

/-! ### The handoffs -/

/-- **Into the outer rounds** (`habs` at `b2`). -/
theorem habsG_outer (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) {L es : Log}
    (x : ByteArray × Digest) (hl : es.length = b2) (hz : ZCwG R E a nc s0 L es) :
    D3G R E a nc s0 b2 L (es ++ [x]) := by
  refine ⟨by simp; omega, ?_⟩
  have ha0 : ans3 b2 (fun _ => a) (es ++ [x]) = 0 := by
    simp only [ans3, List.length_append, List.length_singleton, hl]
    rw [show b2 + 1 - b2 = 1 by omega]; simp
  rw [ha0]
  simp only [Wrong3, clR, rchs, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [T3G_same R E a nc s0 (R.ofAgree L (agree_append es [x] le_rfl)) (by omega) (by omega)]
  exact outer_start _ (by simp [tauS]) hz

/-- **At the end absorb** (`habs` at `b2 + 2A`): with every real round answered, a doomed outer
claim gives the end check's failure or a wrong triple. -/
theorem habsG_end (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) (haA : a ≤ A) {L es : Log}
    (x : ByteArray × Digest) (hl : es.length = b2 + 2 * A)
    (hd : D3G R E a nc s0 b2 L es) :
    RejEndG a s0 b2 A L (es ++ [x]) ∨ EndBadG R E a nc b2 A L (es ++ [x]) := by
  obtain ⟨-, hw⟩ := hd
  have ha : ans3 b2 (fun _ => a) es = a := by
    simp only [ans3, hl]; rw [show b2 + 2 * A - b2 = 2 * A by omega]; omega
  rw [ha] at hw
  unfold Wrong3 at hw
  have hfin : trueSum outerExpr (bindAll (T3G R E a nc s0 L es) (rchs b2 es a)) (a - a) =
      eq (ptOf a (tauS a s0 es)) (ptOf a (rxs a b2 es)) *
        ((triTG R E a nc b2 L es).1 * (triTG R E a nc b2 L es).2.1 +
          (triTG R E a nc b2 L es).2.2) := by
    simp only [T3G, Nat.sub_self]
    exact outer_final _ _ (by simp [tauS]) (by simp [rchs]) _ _ _ _
  rw [hfin] at hw
  have hag := agree_append es [x] (le_of_eq hl.symm)
  have hc : clR b2 (fun _ _ => 0) L (es ++ [x]) a = clR b2 (fun _ _ => 0) L es a :=
    clR_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L) (es := es ++ [x]) (es' := es) rfl
      (l := a) (hag.mono (by omega))
  have hτ := tauS_agree (a := a) (s0 := s0) hag (by omega)
  have hr := rxs_agree (a := a) (b2 := b2) hag (by omega)
  by_cases hrej : RejEndG a s0 b2 A L (es ++ [x])
  · exact Or.inl hrej
  right
  refine ⟨by simp; omega, ?_⟩
  have hchk : clR b2 (fun _ _ => 0) L (es ++ [x]) a =
      eq (ptOf a (tauS a s0 (es ++ [x]))) (ptOf a (rxs a b2 (es ++ [x]))) *
        (vEnd A b2 (es ++ [x]) 0 * vEnd A b2 (es ++ [x]) 1 + vEnd A b2 (es ++ [x]) 2) := by
    by_contra hne; exact hrej ⟨by simp; omega, hne⟩
  rw [triTG_same R E a nc b2 (R.ofAgree L hag) (by omega) (by omega)]
  rw [hc, hτ, hr] at hchk
  intro heq
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  apply hw
  rw [hchk, heq.1, heq.2.1, heq.2.2]

open Classical in
/-- **At the batching squeeze** (`hsingle` at `b2 + 2A + 1`, `batch_escape_le`): from a wrong
triple, at most `2·2^128` answers make the batched claim true. -/
theorem singleG_batch (h3 : 3 ≤ b2) (haA : a ≤ A) (L es : Log) (hl : es.length = b2 + 2 * A + 1) :
    (univ.filter fun d => EndBadG R E a nc b2 A L es ∧
      ¬ BatBadG R E a nc b2 A L (ext1 es d)).card ≤ 2 * 2 ^ 128 := by
  by_cases hd : EndBadG R E a nc b2 A L es
  swap
  · rw [filter_false_of_mem fun d _ h => hd h.1]; simp
  obtain ⟨-, hne⟩ := hd
  set S := univ.filter fun ρ : F => vEnd A b2 es 0 + ρ * vEnd A b2 es 1 + ρ ^ 2 * vEnd A b2 es 2 =
    trueSum innerExpr (innerTables (ptOf a (rxs a b2 es)) ρ (entMat E.ea a nc) (entMat E.eb a nc)
      (entMat E.ec a nc) (zCG R nc L es)) nc
  have hSc : S.card ≤ 2 := batch_escape_le _ _ _ _ _ (by unfold triTG at hne; exact hne)
  refine le_trans (card_le_card (t := univ.filter fun d : Digest => chF d 0 ∈ S)
    fun d hd' => ?_) (by rw [card_chF_fiber]; exact Nat.mul_le_mul_right _ hSc)
  simp only [mem_filter, mem_univ, true_and] at hd' ⊢
  obtain ⟨-, hnb⟩ := hd'
  simp only [S, mem_filter, mem_univ, true_and]
  have hag : Agree (ext1 es d) es es.length := agree_append es _ le_rfl
  have hκ : kapB A b2 (ext1 es d) = chF d 0 := by
    simp only [kapB, fAt, ansAt, ← hl]
    exact congrArg (chF · 0) (entAt_ext1 es d)
  by_contra hc
  apply hnb
  refine ⟨by simp [ext1]; omega, ?_⟩
  have hr := rxs_agree (a := a) (b2 := b2) hag (by omega)
  have hv := fun j => vEnd_agree (a := A) (b2 := b2) hag (by omega) j
  have hz := zCG_same R nc (R.ofAgree L hag) (by omega)
  unfold c4 T4G
  rw [hκ, hz, hr, hv 0, hv 1, hv 2]
  exact hc

open Classical in
/-- **An outer round's squeeze** (`D3_single`): at most `3·2^128` answers escape. -/
theorem singleG_outer (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) (L es : Log) :
    (univ.filter fun d => D3G R E a nc s0 b2 L es ∧ ¬ D3G R E a nc s0 b2 L (ext1 es d)).card ≤
      3 * 2 ^ 128 :=
  D3_single (by omega) (T3G_local R E a nc s0 b2 hs h3) outerExpr_deg (T3G_size R E a nc s0) L es

/-- An outer round's absorb, or a dummy slot's items, keeps the outer doom. -/
theorem outerG_append (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) {L es : Log}
    (x : ByteArray × Digest) (hlen : b2 < es.length)
    (hc : (es.length - b2) % 2 = 0 ∨ a ≤ (es.length - b2) / 2) :
    D3G R E a nc s0 b2 L (es ++ [x]) ↔ D3G R E a nc s0 b2 L es :=
  D3_append_iff (by omega) (T3G_local R E a nc s0 b2 hs h3) x hlen hc

/-- The outer doom reads the same off two logs whose words agree (`hstab`). -/
theorem D3G_same {L L' X : Log} {p : ℕ} (h : R.Sm L X L' X p) (hp3 : 3 ≤ p)
    (hs : s0 + 1 + (a + 1) / 2 ≤ p) :
    D3G R E a nc s0 b2 L X ↔ D3G R E a nc s0 b2 L' X :=
  (D3_log_congr (b := b2) (c0 := fun _ _ => (0 : F)) (nr := fun _ => a) (e := outerExpr)
    (T3G_same R E a nc s0 h hp3 hs).symm rfl).symm

/-- **Once every real round is answered, the outer doom reads before `b2 + 2a + 1`.** -/
theorem D3G_reads (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) :
    ReadsS R (b2 + 2 * a + 1) (D3G R E a nc s0 b2) := fun L es L' es' h1 h2 h => by
  have hans : ∀ Y : Log, b2 + 2 * a ≤ Y.length → ans3 b2 (fun _ => a) Y = a := fun Y hY => by
    unfold ans3; simp; omega
  unfold D3G D3 Wrong3
  rw [hans es (by omega), hans es' (by omega), T3G_same R E a nc s0 h (by omega) (by omega),
    clR_log_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (L' := L) rfl,
    clR_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (es := es) (es' := es') rfl
      ((R.agree h).mono (by omega)),
    rchs_congr ((R.agree h).mono (by omega))]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

end Unit

/-! ## The end check -/

theorem rejEndG_agree {a s0 b2 A : ℕ} (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (haA : a ≤ A) {L es L' es' : Log}
    (h : Agree es es' (b2 + 2 * A + 1)) (hl : b2 + 2 * A + 1 ≤ es.length)
    (hl' : b2 + 2 * A + 1 ≤ es'.length) :
    RejEndG a s0 b2 A L es ↔ RejEndG a s0 b2 A L' es' := by
  have hc : clR b2 (fun _ _ => (0 : F)) L es a = clR b2 (fun _ _ => 0) L' es' a :=
    (clR_log_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (L' := L) rfl a).trans
      (clR_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (es := es) (es' := es') rfl
        (l := a) (h.mono (by omega)))
  have hτ := tauS_agree (a := a) (s0 := s0) h (by omega)
  have hr := rxs_agree (a := a) (b2 := b2) h (by omega)
  have hv := fun j => vEnd_agree (a := A) (b2 := b2) h le_rfl j
  unfold RejEndG
  rw [hc, hτ, hr, hv 0, hv 1, hv 2]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

/-- **The end check is a revision 4.1 check** (its absorb at `b2 + 2A` is not a squeeze). -/
theorem rejEndG_log {a s0 b2 A : ℕ} (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (haA : a ≤ A)
    (hpe : fsItems4[b2 + 2 * A]? ≠ some .squeeze) : RejLog4 (RejEndG a s0 b2 A) :=
  rejLog4_of (q := b2 + 2 * A + 1) (by omega) (fun _ _ h => by have := h.1; omega)
    (fun _ _ _ _ h1 h2 h => rejEndG_agree hs haA h h1 h2) (by simpa using hpe)

/-! ## O1: the E truth over indexed rows -/

section O1
open Circ

/-- **Indexed rows fit** `2^a` rows and `2^b` cells, with **distinct** row indices (two rows at one
index would add up into one matrix row). -/
def RowsFitI (rows : List (ℕ × Row)) (a b : ℕ) : Prop :=
  (rows.map Prod.fst).Nodup ∧ (∀ p ∈ rows, p.1 < 2 ^ a) ∧
    ∀ p ∈ rows, ∀ t ∈ p.2.a ++ p.2.b ++ p.2.c, t.1 < 2 ^ b

/-- **The E truth over indexed rows**: every row holds at `w`. -/
def truthEI (rows : List (ℕ × Row)) (w : Asg) : Prop := ∀ p ∈ rows, p.2.Holds w

theorem sum_ite_none {β : Type*} (g : ℕ × β → F) (x : ℕ) :
    ∀ rows : List (ℕ × β), (∀ q ∈ rows, q.1 ≠ x) →
      (rows.map fun q => if q.1 = x then g q else 0).sum = 0
  | [], _ => by simp
  | q :: rs, h => by
    simp only [List.map_cons, List.sum_cons, ite_neg' (h q List.mem_cons_self),
      sum_ite_none g x rs fun q' hq' => h q' (List.mem_cons_of_mem _ hq'), add_zero]

theorem sum_ite_key {β : Type*} (g : ℕ × β → F) :
    ∀ rows : List (ℕ × β), (rows.map Prod.fst).Nodup → ∀ p ∈ rows,
      (rows.map fun q => if q.1 = p.1 then g q else 0).sum = g p
  | [], _, p, hp => by simp at hp
  | q :: rs, hnd, p, hp => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [ite_pos' rfl, sum_ite_none g _ rs fun q' hq' h => hnd.1 ⟨q', hq', h⟩, add_zero]
    · have hne : q.1 ≠ p.1 := fun h => hnd.1 ⟨p, hp, h.symm⟩
      rw [ite_neg' hne, zero_add, sum_ite_key g rs hnd.2 p hp]

theorem sum_entriesI (s : TEval.Mat) (w : Asg) (x : ℕ) :
    ∀ rows : List (ℕ × Row),
      ((TEval.entriesI s rows).map fun e => if e.1 = x then e.2.2 * w e.2.1 else 0).sum =
        (rows.map fun q => if q.1 = x then (s.r q.2).ev w else 0).sum
  | [] => by simp [TEval.entriesI]
  | q :: rs => by
    have ih := sum_entriesI s w x rs
    simp only [TEval.entriesI, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    congr 1
    by_cases hq : q.1 = x
    · simp [hq, Lin.ev, Function.comp_def]
    · simp [hq, Function.comp_def]

/-- **The matrix product of indexed rows**: on rows whose cells fit, `(M w)(x)` is the sum of the
forms of the rows at index `x`. -/
theorem matVec_entMatI (s : TEval.Mat) (rows : List (ℕ × Row)) {a b : ℕ}
    (hc : ∀ p ∈ rows, ∀ t ∈ s.r p.2, t.1 < 2 ^ b) (w : Asg) (x : Fin (2 ^ a)) :
    matVec (entMat (TEval.entriesI s rows) a b) (fun y => w y) x =
      (rows.map fun q => if q.1 = x.val then (s.r q.2).ev w else 0).sum := by
  have hE : ∀ e ∈ TEval.entriesI s rows, e.2.1 < 2 ^ b := by
    intro e he
    simp only [TEval.entriesI, List.mem_flatMap, List.mem_map] at he
    obtain ⟨p, hp, t, ht, rfl⟩ := he
    exact hc p hp t ht
  rw [matVec]
  exact (sum_entry_mul _ _ w hE).trans (sum_entriesI s w x rows)

/-- **O1: the R1CS of the indexed rows is "every row holds"** (`evalMS`'s matrices). -/
theorem sat_entMatI_iff (rows : List (ℕ × Row)) {a b : ℕ} (hf : RowsFitI rows a b) (w : Asg) :
    Sat (entMat (ESrc.ofIRows rows).ea a b) (entMat (ESrc.ofIRows rows).eb a b)
      (entMat (ESrc.ofIRows rows).ec a b) (fun y => w y) ↔ truthEI rows w := by
  have hc : ∀ s : TEval.Mat, ∀ p ∈ rows, ∀ t ∈ s.r p.2, t.1 < 2 ^ b := by
    intro s p hp t ht
    refine hf.2.2 p hp t ?_
    cases s <;> simp_all [TEval.Mat.r]
  unfold Sat
  simp only [ESrc.ofIRows, matVec_entMatI _ _ (hc _)]
  constructor
  · intro h p hp
    have := h ⟨p.1, hf.2.1 p hp⟩
    simp only [sum_ite_key _ rows hf.1 p hp] at this
    exact this
  · intro h x
    by_cases hx : ∃ p ∈ rows, p.1 = x.val
    · obtain ⟨p, hp, hpx⟩ := hx
      rw [← hpx, sum_ite_key _ rows hf.1 p hp, sum_ite_key _ rows hf.1 p hp,
        sum_ite_key _ rows hf.1 p hp]
      exact h p hp
    · push Not at hx
      rw [sum_ite_none _ _ rows hx, sum_ite_none _ _ rows hx, sum_ite_none _ _ rows hx, zero_mul]

/-- `¬ RowsBadG` over indexed rows is the E truth at `f⁽⁰⁾`. -/
theorem rowsBadG_ofIRows_iff (R : FSrc) (rows : List (ℕ × Row)) {a nc : ℕ}
    (hf : RowsFitI rows a nc) (L es : Log) :
    RowsBadG R (ESrc.ofIRows rows) a nc L es ↔ ¬ truthEI rows (R.fz L es) :=
  not_congr (sat_entMatI_iff rows hf (R.fz L es))

/-- **3.x's row list is an instance** (`sat_rowMat_iff` at `ESrc.ofRows`). -/
theorem sat_ofRows_iff (rows : List Row) {a b : ℕ} (hf : RowsFit rows a b) (w : Asg) :
    Sat (entMat (ESrc.ofRows rows).ea a b) (entMat (ESrc.ofRows rows).eb a b)
      (entMat (ESrc.ofRows rows).ec a b) (fun y => w y) ↔ ∀ r ∈ rows, r.Holds w :=
  sat_rowMat_iff rows hf w

/-- **O1 at 3.x**: the E truth at the templated, indexed rows `evalMS` reads
(`nodeIRows (planOf fin)`, 21 row bits, 23 cells), given that they fit (`hfit`). -/
theorem truthE3_iffI (fin : Finals) (hfit : RowsFitI (TEval.nodeIRows (TEval.planOf fin)) 21 23)
    (κ : Kind) (L es : Log) :
    truthEI (TEval.nodeIRows (TEval.planOf fin)) (fF κ L es) ↔
      Sat (entMat (ESrc.ofIRows (TEval.nodeIRows (TEval.planOf fin))).ea 21 23)
        (entMat (ESrc.ofIRows (TEval.nodeIRows (TEval.planOf fin))).eb 21 23)
        (entMat (ESrc.ofIRows (TEval.nodeIRows (TEval.planOf fin))).ec 21 23) (fun y => fF κ L es y) :=
  (sat_entMatI_iff _ hfit _).symm

/-- **The unit's matrix MLE is `evalMS`'s** (`Eval.matMLE`). -/
theorem matMle_entMat (E : Eval.Entries) {a b : ℕ} (τ : Fin a → F) (σ : Fin b → F) :
    matMle (entMat E a b) τ σ = Eval.matMLE E τ σ := rfl

/-- **E4's weight at `r′`** is the three matrix MLEs at `(r_x, r′)`, batched by `ρ`. -/
theorem mle_wInn {a nc : ℕ} (A B C : Fin (2 ^ a) → Fin (2 ^ nc) → F) (rx : Fin a → F) (ρ : F)
    (r : Fin nc → F) :
    mle (wInn A B C rx ρ) r = matMle A rx r + ρ * matMle B rx r + ρ ^ 2 * matMle C rx r := by
  have h := mle_comb (fun y => matMle A rx (cube y)) (fun y => matMle B rx (cube y))
    (fun y => matMle C rx (cube y)) ρ r
  simp only [mle_matMle] at h
  exact h

end O1

/-! ## Controls -/

/-- (−) Two rows at one index do not fit (`RowsFitI` asks for distinct indices). -/
theorem not_rowsFitI_dup (r : Circ.Row) : ¬ RowsFitI [(0, r), (0, r)] 1 1 := fun h => by
  simp [RowsFitI] at h

/-- (+) The empty indexed row list is satisfied by every assignment. -/
theorem sat_entMatI_nil (a b : ℕ) (w : Circ.Asg) :
    Sat (entMat (ESrc.ofIRows []).ea a b) (entMat (ESrc.ofIRows []).eb a b)
      (entMat (ESrc.ofIRows []).ec a b) (fun y => w y) :=
  (sat_entMatI_iff [] ⟨by simp, by simp, by simp⟩ w).mpr (by simp [truthEI])

/-- (−) An indexed row `1 · 1 = 0` at index 1 makes the R1CS fail. -/
theorem not_sat_entMatI_one (w : Circ.Asg) (hw : w 0 = 1) :
    ¬ Sat (entMat (ESrc.ofIRows [(1, ⟨Circ.Lin.cell 0, Circ.Lin.cell 0, []⟩)]).ea 1 1)
      (entMat (ESrc.ofIRows [(1, ⟨Circ.Lin.cell 0, Circ.Lin.cell 0, []⟩)]).eb 1 1)
      (entMat (ESrc.ofIRows [(1, ⟨Circ.Lin.cell 0, Circ.Lin.cell 0, []⟩)]).ec 1 1) (fun y => w y) := by
  rw [sat_entMatI_iff _ ⟨by simp, by simp, by simp [Circ.Lin.cell]⟩]
  intro h
  have := h _ List.mem_cons_self
  simp [Circ.Row.Holds, hw] at this

end FR.Snd.P4b

end G6_FRSoundness4P4bRows

section G6_FRNodeCircuit4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-13, §4.3 `node_sound`, A.6/A.7 per kind;
-- R-4-m2; stage S-E12a). 3.x templates: `FRNodeCircuit` (`node_sound`, `SlotHolds`, `PubCells`),
-- `FRNodeSoundA` (`NodeResid`, `rel_readWit`), `FRSoundnessExtAll` (`hRes`).

/-!
# The revision 4.1 node relation and `node_sound4`

A node of kind `κ` (`N2`/`N4`/`N8`) has two **signed children** `σ ∈ {0, 1}` (`N2`/`N4`: the
previous node, then the aggregate leaf; `N8`: two aggregates) and `κ.vslots` **verifier slots**
(`N2`/`N4`: slot 0 the previous node, slots `1 + i` the aggregate's segments; `N8`: slots `4a + i`
aggregate `a`'s segments). Aggregate `a` (signed child `aggChild κ a`) has `k_a` segments, read from
its header (`kA`): sub-slots `i < k_a` are active, the rest inactive.

* **`StmtN4`** (what the PIOP's truths give on `f⁽⁰⁾ = w`): `truthZ4` (every non-free block meets its
  kind's R1CS with its target, `nodeKind4`), `truthS4` (the chain mask `chainLk4` and the WOTS link
  families, rebased), the L rows, the M rows (indexed, `truthEI`), `PubCells4` (`cells4` carry
  `1, vk, c₁, vk, c₂`).
* **`SlotIface4`**: what S-E12b's compiled rows provide per verifier slot: three predicates (the
  imports `imp`, the replay `rep`, the templates `tpl`), the kind selectors, and the two soundness
  facts `soundN`/`soundS` (rows + imports + R + templates ⇒ the slot's program accepts its input on
  its trace).
* **`Read4`**: the pack map's read of the children from `w` (signed children; slots' proofs and
  traces).
* **`NodeResid4`**: everything the M/L rows must still certify, item by item (the JOURNAL's §0):
  `imp`, `rep`, `tpl`, `selP`, `slotP`, `selA`, `pack`, `chainMsg`, `aggFmt`, `aggTr`, `aggChk`,
  `kOk` (`childOk4`), `aggPad` (R-4-m2's `k`-gated padding), `wots`.
* **`DigLemma4 κ`**: the H side's BLAKE2s chain fact (the digest computed in H, `hDig4`, is the
  trace digest), from `truthZ4`/`truthS4`, the chain's bytes and `AggPad4`. A theorem obligation of
  the H side (3.x: `Stream.blake2s_chain`), a hypothesis here.
* **`node_sound4`**: `StmtN4` + `NodeResid4` + `DigLemma4` give a witness of the relation
  `Rel (accV4 Vseg Vnode vk)` for `nodeStmt c₁ c₂` with both read children, and `childOk4` of
  both. **`nodeSoundLog4_of`**, **`nodeExtLog4_of`**: the node laws of `FRSoundness4Frame` from
  the PIOP's per-run truths (`hRun`) and the residual (`hRes`).
* **`HFit4`**: `RowsFitI` per node kind over S-E12b's indexed rows (parametric), with
  `rowsFitI_of_sorted` (strictly increasing indices give distinctness: the generator's
  certificate).
-/

namespace FR
namespace N4c
open RecursionFast Rev4 Circ

/-! ## The H bits and digests -/

/-- Bit `b` of `f` (A.7: element `⌊b/128⌋`, bit `b mod 128`). -/
noncomputable def zW4 (w : Asg) (b : ℕ) : F := unpack (w (b / 128)) ⟨b % 128, Nat.mod_lt _ (by norm_num)⟩

/-- Block `blk`'s positions. -/
noncomputable def zB4 (w : Asg) (blk : ℕ) : Block.Pos → F := fun k => zW4 w (blk * 2 ^ 14 + k.val)

/-- Block `blk`'s position `p`. -/
noncomputable def zN4 (w : Asg) (blk p : ℕ) : F := zW4 w (blk * 2 ^ 14 + p)

/-- Block `blk`'s bits as Booleans. -/
noncomputable def bitsB4 (w : Asg) (blk : ℕ) : Block.Pos → Bool := fun k => decide (zB4 w blk k = 1)

/-- **The block where signed child `σ`'s chain ends** with `k` segments: an aggregate of `k < maxK`
ends at its candidate final block `F_{a,k}`, otherwise at its main chain's last block. -/
def finBlk (κ : NodeKind) (σ k : ℕ) : ℕ :=
  if isAgg κ σ ∧ k < κ.maxK then finB κ (aggOf κ σ) + (k - 1) else chBase κ σ + chLen κ σ - 1

/-- Blocks and bytes of signed child `σ`'s stream with `k` segments. -/
def streamL (κ : NodeKind) (σ k : ℕ) : ℕ := if isAgg κ σ then aggL k else cLen
def streamB (κ : NodeKind) (σ k : ℕ) : ℕ := if isAgg κ σ then aggB k else segB

/-- **The digest computed in H**: `h_out` of the final block. -/
noncomputable def hDig4 (κ : NodeKind) (σ k : ℕ) (w : Asg) : Digest :=
  Block.readDigest (bitsB4 w (finBlk κ σ k)) 256

/-- Stream block `i` of signed child `σ`'s chain with `k` segments: the main chain's block `i`,
except the last, which is the final block (`finBlk`). -/
def blkOf (κ : NodeKind) (σ k i : ℕ) : ℕ := if i + 1 = streamL κ σ k then finBlk κ σ k else chBase κ σ + i

/-- The chain's blocks as Boolean blocks, in stream order. -/
noncomputable def chainW4 (κ : NodeKind) (σ k : ℕ) (w : Asg) : ℕ → Block.Pos → Bool :=
  fun i => bitsB4 w (blkOf κ σ k i)

/-- **The bytes the chain hashes**: byte `p` is message byte `p mod 64` of stream block `⌊p/64⌋`
(`Stream.streamBytes`). -/
noncomputable def chainBytes4 (κ : NodeKind) (σ k : ℕ) (w : Asg) : List UInt8 :=
  Stream.streamBytes (chainW4 κ σ k w) (streamB κ σ k)

/-- **R-4-m2's `k`-gated last block** of aggregate `a` with `k` segments. With `j = aggL k` blocks
and `r = aggB k − 64 (j − 1)` bytes in the last: if `k < maxK`, the candidate final block's `h_in`
is the main chain's block `j − 2`'s `h_out` and its first `r` message bytes are the main chain's
block `j − 1`'s; in every case the final block's message bytes `r … 63` are zero. -/
def AggPad4 (κ : NodeKind) (a k : ℕ) (w : Asg) : Prop :=
  let σ := aggChild κ a
  let j := aggL k
  let r := aggB k - 64 * (j - 1)
  (k < κ.maxK →
    (∀ x < 256, zN4 w (finBlk κ σ k) x = zN4 w (chBase κ σ + j - 2) (256 + x)) ∧
    ∀ x < 8 * r, zN4 w (finBlk κ σ k) (512 + x) = zN4 w (chBase κ σ + j - 1) (512 + x)) ∧
  ∀ x, 8 * r ≤ x → x < 512 → zN4 w (finBlk κ σ k) (512 + x) = 0

/-! ## The statement (the PIOP's truths on `f⁽⁰⁾`) -/

/-- **Z**: every non-free block meets its kind's R1CS with its public target. -/
def truthZ4 (κ : NodeKind) (w : Asg) : Prop :=
  ∀ blk < κ.blocks, ∀ tgt, nodeKind4 κ blk = some tgt →
    Block.HoldsE (Block.blockR1CS tgt) (Block.targetVal F tgt) (zB4 w blk)

/-- **S**: the chain mask's links and the WOTS link families (A.8, rebased). -/
def truthS4 (κ : NodeKind) (w : Asg) : Prop :=
  (∀ y, chainLk4 κ y = true → ∀ j < 256, zN4 w (y + 1) j = zN4 w y (256 + j)) ∧
    ∀ f < nLinkFam, ∀ σ < 2, ∀ t < (NodeT.fam f).n, ∀ s < NodeT.fbits f,
      zN4 w (srcB4 κ σ f t) (NodeT.fpos f s) = zN4 w (mirB4 κ σ f t) (NodeT.mpos f t s)

/-- **The public cells** (A.7 per kind): `1`, then `vk` and `c_σ`'s halves per signed child. -/
def PubCells4 (κ : NodeKind) (w : Asg) (vk c₁ c₂ : Digest) : Prop :=
  (cells4 κ).map w = Node.pubVals vk c₁ c₂

/-- **The reserve's public cells** (revision 4.4.2; RSV2 §2.4: the V side's 60 cells after the nine,
`Rev4.rsvCells`): slot 0's stacked `evalM` call, its row point's 23 coordinates `x̂`, its column point's
25 `ŷ`, its nine coefficients `s` and its three outputs `X₃`, hold the node's own proof's child claim
`ch` (`fLrEnd`'s `p_x ‖ p_y ‖ s ‖ X₃`, read by `finB′`). Empty for `N8`. Not yet a conjunct of `StmtN4` (the soundness track's). -/
def PubCellsR4 (κ : NodeKind) (w : Asg) (ch : List F) : Prop :=
  (Rev4.rsvCells κ).map w = ch

/-- **`StmtN4`**: the node's truths on `w`, with the L rows `lr` and the indexed M rows `er`. -/
def StmtN4 (κ : NodeKind) (lr : List Row) (er : List (ℕ × Row)) (vk c₁ c₂ : Digest) (w : Asg) : Prop :=
  truthZ4 κ w ∧ truthS4 κ w ∧ (∀ r ∈ lr, r.Holds w) ∧ Snd.P4b.truthEI er w ∧ PubCells4 κ w vk c₁ c₂

/-! ## The slots, the reader, the residual -/

/-- **What the compiled rows provide per verifier slot** (S-E12b): the node kind's L and M rows,
three predicates of slot `v` (imports, the replay `R`, the templates), the kind selectors of the
two kind groups, and the slot's soundness under each. -/
structure SlotIface4 (Vseg : SegProgs) (Vnode : NodeProgs) where
  lrows : NodeKind → List Row
  irows : NodeKind → List (ℕ × Row)
  imp : NodeKind → ℕ → Asg → Input → Trace → Prop
  rep : NodeKind → ℕ → Asg → Input → Trace → Prop
  tpl : NodeKind → ℕ → Asg → Prop
  selN : NodeKind → ℕ → Asg → NodeKind → Prop
  selS : NodeKind → ℕ → Asg → SegKind → Prop
  soundN : ∀ κ v w inp tr κ', (∀ r ∈ lrows κ, r.Holds w) → Snd.P4b.truthEI (irows κ) w →
    selN κ v w κ' → imp κ v w inp tr → rep κ v w inp tr → tpl κ v w →
    (Vnode κ' inp.vk inp.c inp.π).runSeq tr = some true
  soundS : ∀ κ v w inp tr κ', (∀ r ∈ lrows κ, r.Holds w) → Snd.P4b.truthEI (irows κ) w →
    selS κ v w κ' → imp κ v w inp tr → rep κ v w inp tr → tpl κ v w →
    (Vseg κ' inp.vk inp.c inp.π).runSeq tr = some true

/-- **The pack map's read** of a node's children from `w`. -/
structure Read4 where
  /-- Signed child `σ`: proof, trace, signature. -/
  sgn : NodeKind → ℕ → Asg → Signed
  /-- Verifier slot `v`'s proof and trace. -/
  slotπ : NodeKind → ℕ → Asg → Proof
  slotTr : NodeKind → ℕ → Asg → Trace

/-- Aggregate `a`'s segments (its header's byte 1). -/
def kA (rd : Read4) (κ : NodeKind) (w : Asg) (a : ℕ) : ℕ := (byteAt (rd.sgn κ (aggChild κ a) w).π 1).toNat

/-- Aggregate `a`'s sub-slot `i`. -/
def sub (κ : NodeKind) (a i : ℕ) : ℕ := if κ.hasPrev then 1 + i else 4 * a + i

/-- Signed child `σ`'s statement. -/
def stOf (c₁ c₂ : Digest) (σ : ℕ) : Digest := if σ = 0 then c₁ else c₂

/-- Signed child `σ`'s segment count (`0` for a previous node). -/
def kOf (rd : Read4) (κ : NodeKind) (w : Asg) (σ : ℕ) : ℕ := if isAgg κ σ then kA rd κ w (aggOf κ σ) else 0

/-- Verifier slot `v` is active: the previous node's, or a sub-slot below its aggregate's `k`. -/
def Active4 (rd : Read4) (κ : NodeKind) (w : Asg) (v : ℕ) : Prop :=
  (κ.hasPrev = true ∧ v = 0) ∨ ∃ a < nAgg κ, ∃ i < kA rd κ w a, v = sub κ a i

/-- **Slot `v`'s input**: the previous node's `(vk, c₁, π₁)`; a segment's `(vk, cᵢ, πᵢ)` with its
statement `cᵢ = leafStmt eᵢ nᵢ` (`segC`) from its proof's view. -/
def slotIn (rd : Read4) (κ : NodeKind) (vk c₁ : Digest) (w : Asg) (v : ℕ) : Input :=
  if κ.hasPrev = true ∧ v = 0 then ⟨vk, c₁, rd.slotπ κ v w⟩
  else ⟨vk, ((segView (rd.slotπ κ v w)).map segC).getD 0, rd.slotπ κ v w⟩

/-- **The node's residual** (per item; the JOURNAL's §0): what `StmtN4` does not give and the M/L
rows (S-E12b) must certify. -/
structure NodeResid4 {Vseg : SegProgs} {Vnode : NodeProgs} (I : SlotIface4 Vseg Vnode) (rd : Read4)
    (κ : NodeKind) (vk c₁ c₂ : Digest) (w : Asg) : Prop where
  /-- Imports of every active slot (the pack map into M, `vk`, `c`, trace cells, L bits). -/
  imp : ∀ v, Active4 rd κ w v → I.imp κ v w (slotIn rd κ vk c₁ w v) (rd.slotTr κ v w)
  /-- The replay `R` of every active slot. -/
  rep : ∀ v, Active4 rd κ w v → I.rep κ v w (slotIn rd κ vk c₁ w v) (rd.slotTr κ v w)
  /-- The template rows of every active slot. -/
  tpl : ∀ v, Active4 rd κ w v → I.tpl κ v w
  /-- The previous node's slot selects its kind `κ'`, and its proof is a `κ'` node proof. -/
  selP : κ.hasPrev = true → ∃ κ', I.selN κ 0 w κ' ∧ kindOf4 (rd.sgn κ 0 w).π = .node κ'
  /-- The previous node's slot reads signed child 0. -/
  slotP : κ.hasPrev = true → rd.slotπ κ 0 w = (rd.sgn κ 0 w).π ∧ rd.slotTr κ 0 w = (rd.sgn κ 0 w).tr
  /-- An active sub-slot selects its segment's kind. -/
  selA : ∀ a < nAgg κ, ∀ i < kA rd κ w a, ∃ v : SegView,
    segView (rd.slotπ κ (sub κ a i) w) = some v ∧ I.selS κ (sub κ a i) w v.kind
  /-- The signed children's format (`acc`'s word, query and size conjuncts). -/
  pack : ∀ σ < 2, (rd.sgn κ σ w).π.size < 2 ^ 64 ∧ (rd.sgn κ σ w).tr.length ≤ qV4 ∧
    ∀ e ∈ (rd.sgn κ σ w).tr, e.1.size ≤ queryCap
  /-- The chain hashes the child's stream `0x54 ‖ traceBytes tr`. -/
  chainMsg : ∀ σ < 2, chainBytes4 κ σ (kOf rd κ w σ) w = tagTrace :: traceBytes (rd.sgn κ σ w).tr
  /-- `π_A`'s parse: size, kind byte, zero bytes 2–7, its segments are the active sub-slots'. -/
  aggFmt : ∀ a < nAgg κ, (rd.sgn κ (aggChild κ a) w).π.size = 48 + kA rd κ w a * piSizeOf seq4 ∧
    byteAt (rd.sgn κ (aggChild κ a) w).π 0 = aggByte ∧
    bytesAt (rd.sgn κ (aggChild κ a) w).π 2 6 = Vector.replicate 6 0 ∧
    aggSegs (piSizeOf seq4) (kA rd κ w a) (rd.sgn κ (aggChild κ a) w).π =
      (List.range (kA rd κ w a)).map fun i => rd.slotπ κ (sub κ a i) w
  /-- `tr_A` is `V_A`'s trace (R-A′): the active sub-slots' traces in order, the spacer's entry
  `(spacerQ, ans i)` before sub-slot `i ≥ 1`. -/
  aggTr : ∀ a < nAgg κ, ∃ ans, (rd.sgn κ (aggChild κ a) w).tr =
    aggTrace ans ((List.range (kA rd κ w a)).map fun i => rd.slotTr κ (sub κ a i) w)
  /-- `V_A`'s checks against the aggregate's statement `c_A` (the `hashA` block, O-1). -/
  aggChk : ∀ a < nAgg κ, ∃ vs, (aggSegs (piSizeOf seq4) (kA rd κ w a)
      (rd.sgn κ (aggChild κ a) w).π).mapM segView = some vs ∧
    aggChecks (stOf c₁ c₂ (aggChild κ a)) (rdLE64 (rd.sgn κ (aggChild κ a) w).π 8)
      (bytesAt (rd.sgn κ (aggChild κ a) w).π 16 32) vs = true
  /-- **`childOk4`** (R-4-m2): at most `maxK` segments. -/
  kOk : ∀ a < nAgg κ, kA rd κ w a ≤ κ.maxK
  /-- **R-4-m2**: the `k`-gated last block. -/
  aggPad : ∀ a < nAgg κ, AggPad4 κ a (kA rd κ w a) w
  /-- WOTS verifies the digest selected by `k` (the `k`-mux, the digits, the mirrors: O2b). -/
  wots : ∀ σ < 2, SigOk vk (hDig4 κ σ (kOf rd κ w σ) w) (rd.sgn κ σ w).σ = true

/-- **The H side's chain fact** (the BLAKE2s chain over the blocks; 3.x `Stream.blake2s_chain`):
on Z/S truths, a chain whose bytes are `0x54 ‖ traceBytes tr` (and, for an aggregate of `k`
segments, `1 ≤ k ≤ maxK` and `AggPad4`) computes `traceDigest tr`. -/
def DigLemma4 (κ : NodeKind) : Prop :=
  ∀ w σ k tr, σ < 2 → truthZ4 κ w → truthS4 κ w →
    (isAgg κ σ = true → 1 ≤ k ∧ k ≤ κ.maxK ∧ AggPad4 κ (aggOf κ σ) k w) →
    chainBytes4 κ σ k w = tagTrace :: traceBytes tr → hDig4 κ σ k w = traceDigest tr

/-! ## `node_sound4` -/

section Sound
variable {Vseg : SegProgs} {Vnode : NodeProgs}

theorem aggChild_lt (κ : NodeKind) {a : ℕ} (ha : a < nAgg κ) : aggChild κ a < 2 := by
  cases κ <;> simp_all [aggChild, nAgg, NodeKind.hasPrev]

theorem isAgg_aggChild (κ : NodeKind) (a : ℕ) : isAgg κ (aggChild κ a) = true := by
  cases κ <;> simp [isAgg, aggChild, NodeKind.hasPrev]

theorem aggOf_aggChild (κ : NodeKind) {a : ℕ} (ha : a < nAgg κ) : aggOf κ (aggChild κ a) = a := by
  cases κ <;> simp_all [aggOf, aggChild, nAgg, NodeKind.hasPrev]

/-- Every aggregate child is some aggregate's. -/
theorem agg_of_isAgg (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) (h : isAgg κ σ = true) :
    aggOf κ σ < nAgg κ ∧ aggChild κ (aggOf κ σ) = σ := by
  cases κ <;> simp_all [isAgg, aggOf, aggChild, nAgg, NodeKind.hasPrev] <;> omega

theorem sub_active (rd : Read4) (κ : NodeKind) (w : Asg) {a i : ℕ} (ha : a < nAgg κ) (hi : i < kA rd κ w a) :
    Active4 rd κ w (sub κ a i) := .inr ⟨a, ha, i, hi, rfl⟩

theorem slotIn_sub (rd : Read4) (κ : NodeKind) (vk c₁ : Digest) (w : Asg) (a i : ℕ) :
    slotIn rd κ vk c₁ w (sub κ a i) =
      ⟨vk, ((segView (rd.slotπ κ (sub κ a i) w)).map segC).getD 0, rd.slotπ κ (sub κ a i) w⟩ := by
  by_cases hp : κ.hasPrev = true <;> simp [slotIn, sub, hp]

theorem mapM_forall₂4 {l : List Proof} {vs : List SegView} (h : l.mapM segView = some vs) :
    List.Forall₂ (fun p v => segView p = some v) l vs := by
  induction l generalizing vs with
  | nil => simp at h; subst h; exact .nil
  | cons p l ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs', rfl⟩ := h
    exact .cons hv (ih hvs')

variable {I : SlotIface4 Vseg Vnode} {rd : Read4} {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}

/-- **Acceptance of a signed child** from its run: the format (`pack`), the signature over its
trace digest (`wots` and the H side's chain fact `DigLemma4`, with `kOk`/`aggPad` for an
aggregate). -/
theorem sig_of (hS : StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w) (hR : NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : DigLemma4 κ) {σ : ℕ} (hσ : σ < 2) {v : Unit → OProg Bool}
    (hrun : (v ()).runSeq (rd.sgn κ σ w).tr = some true) :
    accWith4 vk (rd.sgn κ σ w) v = true := by
  have hagg : isAgg κ σ = true → 1 ≤ kOf rd κ w σ ∧ kOf rd κ w σ ≤ κ.maxK ∧
      AggPad4 κ (aggOf κ σ) (kOf rd κ w σ) w := fun h => by
    obtain ⟨ha, hc⟩ := agg_of_isAgg κ hσ h
    have hk : kOf rd κ w σ = kA rd κ w (aggOf κ σ) := by simp [kOf, h]
    obtain ⟨vs, hvs, hck⟩ := hR.aggChk _ ha
    refine ⟨?_, hk ▸ hR.kOk _ ha, hk ▸ hR.aggPad _ ha⟩
    have h1 : 1 ≤ vs.length := by
      simp only [aggChecks, Bool.and_eq_true, decide_eq_true_eq] at hck; exact hck.1.1.1.1.2.1
    have h2 := (mapM_forall₂4 hvs).length_eq
    rw [aggSegs, List.length_map, List.length_range] at h2
    rw [hk]; omega
  have hd := hD w σ _ _ hσ hS.1 hS.2.1 hagg (hR.chainMsg σ hσ)
  have hw := hR.wots σ hσ
  rw [hd] at hw
  obtain ⟨h1, h2, h3⟩ := hR.pack σ hσ
  simp only [accWith4, SigOkF_eq, traceDigestF_eq, hw, h1, h2, hrun, decide_true, Bool.true_and,
    Bool.and_true, decide_eq_true_eq]
  exact h3

/-- **An aggregate child is accepted** (`V_A` through `VA_complete`): its parse (`aggFmt`), the
checks (`aggChk`), and every active sub-slot's segment program accepting its trace (`soundS` with
`selA`, `imp`, `rep`, `tpl`), on `tr_A` (`aggTr`: the spacer entries between them). -/
theorem agg_acc (hS : StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w) (hR : NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : DigLemma4 κ) {a : ℕ} (ha : a < nAgg κ) :
    accV4 Vseg Vnode vk (stOf c₁ c₂ (aggChild κ a)) (rd.sgn κ (aggChild κ a) w) = true ∧
      childOk4 κ (rd.sgn κ (aggChild κ a) w).π = true := by
  obtain ⟨hsz, h0, hpad, hsegs⟩ := hR.aggFmt a ha
  obtain ⟨vs, hvs, hck⟩ := hR.aggChk a ha
  have hkind : kindOf4 (rd.sgn κ (aggChild κ a) w).π = .agg := by
    show (if byteAt _ 0 = aggByte then _ else _) = _
    rw [if_pos h0]
  refine ⟨sig_of hS hR hD (aggChild_lt κ ha) ?_, ?_⟩
  · obtain ⟨ans, htr⟩ := hR.aggTr a ha
    rw [V4_agg Vseg Vnode vk _ _ hkind, htr]
    refine VA_complete hsz h0 hpad hvs hck ?_ ans
    change List.Forall₂ _ (segProgs Vseg vk (aggSegs (piSizeOf seq4) (kA rd κ w a) _) vs) _
    rw [hsegs] at hvs ⊢
    have hF := mapM_forall₂4 hvs
    have hl := hF.length_eq
    simp only [List.length_map, List.length_range] at hl
    refine List.forall₂_iff_get.2 ⟨by simp [segProgs, ← hl], fun i h₁ h₂ => ?_⟩
    have hi : i < kA rd κ w a := by simpa using h₂
    have hv := (List.forall₂_iff_get.1 hF).2 i (by simpa using hi) (by rw [← hl]; exact hi)
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at hv
    obtain ⟨v, hv', hsel⟩ := hR.selA a ha i hi
    rw [hv] at hv'
    cases hv'
    simp only [segProgs, List.get_eq_getElem, List.getElem_map, List.getElem_zip, List.getElem_range]
    have hact := sub_active rd κ w ha hi
    have := I.soundS κ (sub κ a i) w _ _ _ hS.2.2.1 hS.2.2.2.1 hsel (hR.imp _ hact) (hR.rep _ hact)
      (hR.tpl _ hact)
    rw [slotIn_sub] at this
    simpa [hv] using this
  · unfold childOk4; rw [hkind]
    exact decide_eq_true (hR.kOk a ha)

/-- **The previous node is accepted**: its slot's kind `κ'` (`selP`), the node program `Vnode κ'`
accepting its trace (`soundN`), the format and the signature. -/
theorem prev_acc (hS : StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w) (hR : NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : DigLemma4 κ) (hp : κ.hasPrev = true) :
    accV4 Vseg Vnode vk c₁ (rd.sgn κ 0 w) = true ∧ childOk4 κ (rd.sgn κ 0 w).π = true := by
  obtain ⟨κ', hsel, hkind⟩ := hR.selP hp
  obtain ⟨hπ, htr⟩ := hR.slotP hp
  have hact : Active4 rd κ w 0 := .inl ⟨hp, rfl⟩
  have hin : slotIn rd κ vk c₁ w 0 = ⟨vk, c₁, (rd.sgn κ 0 w).π⟩ := by simp [slotIn, hp, hπ]
  refine ⟨sig_of hS hR hD (by norm_num) ?_, ?_⟩
  · rw [V4_node Vseg Vnode vk _ _ hkind]
    have := I.soundN κ 0 w _ _ _ hS.2.2.1 hS.2.2.2.1 hsel (hR.imp _ hact) (hR.rep _ hact) (hR.tpl _ hact)
    rw [hin, htr] at this
    exact this
  · unfold childOk4; rw [hkind]

/-- **`node_sound4`** (§4.3 at revision 4.1): the node's truths `StmtN4`, the residual
`NodeResid4` and the H side's chain fact give a witness of the relation for `nodeStmt c₁ c₂`:
both read signed children are accepted (`accV4`), and both pass `childOk4 κ`. -/
theorem node_sound4 (hS : StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w) (hR : NodeResid4 I rd κ vk c₁ c₂ w)
    (hD : DigLemma4 κ) :
    Rel (accV4 Vseg Vnode vk) (nodeStmt c₁ c₂) (.node c₁ c₂ (rd.sgn κ 0 w) (rd.sgn κ 1 w)) ∧
      ∀ σ < 2, childOk4 κ (rd.sgn κ σ w).π = true := by
  have hch : ∀ σ < 2, accV4 Vseg Vnode vk (stOf c₁ c₂ σ) (rd.sgn κ σ w) = true ∧
      childOk4 κ (rd.sgn κ σ w).π = true := fun σ hσ => by
    by_cases hA : isAgg κ σ = true
    · obtain ⟨ha, hc⟩ := agg_of_isAgg κ hσ hA
      rw [← hc]; exact agg_acc hS hR hD ha
    · have hp : κ.hasPrev = true ∧ σ = 0 := by
        cases κ <;> simp_all [isAgg, NodeKind.hasPrev]
      obtain ⟨hp, rfl⟩ := hp
      exact prev_acc hS hR hD hp
  exact ⟨⟨rfl, (hch 0 (by norm_num)).1, (hch 1 (by norm_num)).1⟩, fun σ hσ => (hch σ hσ).2⟩

end Sound

/-! ## The node laws of `FRSoundness4Frame` -/

section Laws
variable {Vseg : SegProgs} {Vnode : NodeProgs}

/-- **`NodeSoundLog` from the node circuit**: if an accepted node run on a good log carries the key
and its truths `StmtN4` hold on some `f⁽⁰⁾` for `c = nodeStmt c₁ c₂` (`hRun`: the PIOP's per-run
soundness, X4/S-G), and the truths give the residual (`hRes`: S-E12b's rows), then the statement has
a witness (`node_sound4`). Revision 4.4.2: the per-run statement is any `St` that implies `StmtN4`
(`hSt`), e.g. the reserve's `StmtN4R`; `hRes` may use all of it. -/
theorem nodeSoundLog4_of (I : SlotIface4 Vseg Vnode) (rd : Read4) {vk : Digest} {Good : Log → Prop}
    {St : NodeKind → Asg → Digest → Digest → Prop}
    (hSt : ∀ κ w c₁ c₂, St κ w c₁ c₂ → StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w)
    (hD : ∀ κ, DigLemma4 κ)
    (hRun : ∀ κ L c π, Good L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
      X.vkOf π = vk ∧ ∃ w c₁ c₂, c = nodeStmt c₁ c₂ ∧ St κ w c₁ c₂)
    (hRes : ∀ κ w c₁ c₂, St κ w c₁ c₂ → NodeResid4 I rd κ vk c₁ c₂ w) :
    NodeSoundLog Vnode vk Good (Rel (accV4 Vseg Vnode vk)) := fun κ L c π hG hk h => by
  obtain ⟨hvk, w, c₁, c₂, rfl, hS⟩ := hRun κ L c π hG hk h
  exact ⟨hvk, _, (node_sound4 (hSt κ w c₁ c₂ hS) (hRes κ w c₁ c₂ hS) (hD κ)).1⟩

/-- **`NodeExtLog`** for an extractor that, on an accepted node run on a good log with the run's
key, returns a witness whenever one exists (S-H3's interface, a parameter: `hE`). -/
theorem nodeExtLog4_of (I : SlotIface4 Vseg Vnode) (rd : Read4) {vk : Digest} {Good : Log → Prop}
    {St : NodeKind → Asg → Digest → Digest → Prop}
    (hSt : ∀ κ w c₁ c₂, St κ w c₁ c₂ → StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w)
    {E : Digest → Proof → Log → Option Wit} (hD : ∀ κ, DigLemma4 κ)
    (hRun : ∀ κ L c π, Good L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
      X.vkOf π = vk ∧ ∃ w c₁ c₂, c = nodeStmt c₁ c₂ ∧ St κ w c₁ c₂)
    (hRes : ∀ κ w c₁ c₂, St κ w c₁ c₂ → NodeResid4 I rd κ vk c₁ c₂ w)
    (hE : ∀ κ L c π, Good L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
      X.vkOf π = vk → (∃ w, Rel (accV4 Vseg Vnode vk) c w) →
        ∃ w, E c π L = some w ∧ Rel (accV4 Vseg Vnode vk) c w) :
    NodeExtLog Vnode vk Good E (Rel (accV4 Vseg Vnode vk)) := fun κ L c π hG hk h => by
  obtain ⟨hvk, hw⟩ := nodeSoundLog4_of I rd hSt hD hRun hRes κ L c π hG hk h
  exact hE κ L c π hG hk h hvk hw

/-- **At the concrete verifier** (`VC4`, `acc_eqC4`): `NodeSoundLog` with the submission's `acc`,
and `NodeExtLog` at the specification extractor `E4 S.acc` (`nodeExt_E4`), the forms `ks4_of`/
`ks4_E4` take. -/
theorem nodeLaws4C (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ)
    (S : Submission) (vk : Digest) (hV : S.V = VC4 impl₀ implN cells) (hq : S.qV = qV4)
    {Good : Log → Prop} (I : SlotIface4 (VsegC impl₀) (VnodeC implN cells)) (rd : Read4)
    {St : NodeKind → Asg → Digest → Digest → Prop}
    (hSt : ∀ κ w c₁ c₂, St κ w c₁ c₂ → StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w)
    (hD : ∀ κ, DigLemma4 κ)
    (hRun : ∀ κ L c π, Good L → kindOf4 π = .node κ → (VnodeC implN cells κ vk c π).runLog L = some true →
      X.vkOf π = vk ∧ ∃ w c₁ c₂, c = nodeStmt c₁ c₂ ∧ St κ w c₁ c₂)
    (hRes : ∀ κ w c₁ c₂, St κ w c₁ c₂ → NodeResid4 I rd κ vk c₁ c₂ w) :
    NodeSoundLog (VnodeC implN cells) vk Good (Rel (S.acc vk)) ∧
      NodeExtLog (VnodeC implN cells) vk Good (E4 S.acc) (Rel (S.acc vk)) := by
  have h : NodeSoundLog (VnodeC implN cells) vk Good (Rel (S.acc vk)) := by
    rw [acc_eqC4 impl₀ implN cells S hV hq]; exact nodeSoundLog4_of I rd hSt hD hRun hRes
  exact ⟨h, nodeExt_E4 hq h⟩

end Laws

/-! ## The PIOP's node parameters (P4a's `zlm4`) -/

/-- **`zlm4 indN4 etN4` meets `IndKinds`**: a node has no `chain` block. -/
theorem zlm4_indKinds : (Snd.P4a.zlm4 indN4 etN4).IndKinds := fun κ t => by
  cases κ with
  | seg σ => exact ⟨fun h => by simp [Snd.CKind.isNode] at h, fun _ j hj => by
      simp [Snd.P4a.zlm4, hj]⟩
  | node ν => exact ⟨fun _ => indN4_chain ν t, fun h => by simp [Snd.CKind.isNode] at h⟩

/-- The node indicators and targets are bits (`ZLM4.Bits`' node half). -/
theorem indN4_etN4_bits (κ : NodeKind) (j : Fin 9) (t : ℕ) (p : Fin (2 ^ 14)) :
    (indN4 κ j t = 0 ∨ indN4 κ j t = 1) ∧ (etN4 κ t p = 0 ∨ etN4 κ t p = 1) := by
  refine ⟨by unfold indN4; split_ifs <;> simp, ?_⟩
  unfold etN4 NodeT.tgtE NodeT.bF
  split <;> (try split) <;> simp

/-- **P4b's `hcells`** at `cells4` (the `cells` parameter of `single_B4`, and of `VC4`'s node
finals `nodeFinP κ (cells κ)`). -/
theorem hcells4P4b : ∀ ν, (cells4 ν).length = 9 ∧ ∀ c ∈ cells4 ν, c < 2 ^ Snd.P4b.ncR ν :=
  fun ν => ⟨(hcells4 ν).1, (hcells4 ν).2.1⟩

/-! ## `hfit` per node kind (P4b's O1 over S-E12b's indexed rows) -/

/-- **`hfit4`**: per node kind, the indexed M rows fit `evalM`'s `e2R κ` row and `ncR κ` cell
variables with distinct indices (P4b F1). Parametric in S-E12b's rows. -/
def HFit4 (irows : NodeKind → List (ℕ × Row)) : Prop :=
  ∀ κ, Snd.P4b.RowsFitI (irows κ) (Snd.P4b.e2R κ) (Snd.P4b.ncR κ)

/-- **The generator's certificate**: strictly increasing indices (by construction) give the
distinct indices `RowsFitI` asks; with the last index and every cell in range. -/
theorem rowsFitI_of_sorted {rows : List (ℕ × Row)} {a b : ℕ}
    (hs : (rows.map Prod.fst).Pairwise (· < ·)) (ha : ∀ p ∈ rows, p.1 < 2 ^ a)
    (hb : ∀ p ∈ rows, ∀ t ∈ p.2.a ++ p.2.b ++ p.2.c, t.1 < 2 ^ b) : Snd.P4b.RowsFitI rows a b :=
  ⟨hs.imp fun h => Nat.ne_of_lt h, ha, hb⟩

/-- `HFit4` from the per-kind certificates. -/
theorem hfit4_of {irows : NodeKind → List (ℕ × Row)}
    (hs : ∀ κ, ((irows κ).map Prod.fst).Pairwise (· < ·))
    (ha : ∀ κ, ∀ p ∈ irows κ, p.1 < 2 ^ Snd.P4b.e2R κ)
    (hb : ∀ κ, ∀ p ∈ irows κ, ∀ t ∈ p.2.a ++ p.2.b ++ p.2.c, t.1 < 2 ^ Snd.P4b.ncR κ) : HFit4 irows :=
  fun κ => rowsFitI_of_sorted (hs κ) (ha κ) (hb κ)

/-! ## Controls -/

/-- (−) `PubCells4` is not trivial: the zero assignment fails it (the `one` cell must be `1`). -/
theorem not_pubCells4_zero (κ : NodeKind) (vk c₁ c₂ : Digest) : ¬ PubCells4 κ (fun _ => 0) vk c₁ c₂ := by
  intro h
  have := congrArg List.head? h
  simp [cells4, Node.pubVals] at this

/-- (+/−) **The reserve's cells** (revision 4.4.2): 52 for `N2`/`N4` (slot 0's E2 and E4
challenges, `evalM`'s outputs, the kind element), none for `N8`; inside `f` and slot 0's M region,
distinct, and disjoint from the nine public cells. -/
theorem rsvCells_ctl : (Rev4.rsvCells .N2).length = 60 ∧ (Rev4.rsvCells .N4).length = 60 ∧
    Rev4.rsvCells .N8 = [] ∧
    (∀ κ, ∀ c ∈ Rev4.rsvCells κ, κ.oneCell ≤ c ∧ c < κ.oneCell + 2 ^ 20 ∧ c < 2 ^ (κ.m - 7)) ∧
    (∀ κ, (Rev4.rsvCells κ).Nodup ∧ ∀ c ∈ Rev4.rsvCells κ, c ∉ cells4 κ) := by
  refine ⟨rfl, rfl, rfl, fun κ => ?_, fun κ => ?_⟩ <;> cases κ <;> decide

/-- (+) `AggPad4` holds on the zero assignment (every bit `0`: the links and the padding). -/
theorem aggPad4_zero (κ : NodeKind) (a k : ℕ) : AggPad4 κ a k (fun _ => 0) := by
  have h0 : ∀ b, zN4 (fun _ => 0) b = fun _ => 0 := fun b => by
    funext p; simp [zN4, zW4, unpack, bitF_zero]
  simp only [AggPad4, h0, implies_true, and_self]

/-- (−) `AggPad4` binds the padding: a nonzero padding bit of the final block fails it. -/
theorem not_aggPad4 {κ : NodeKind} {a k x : ℕ} {w : Asg}
    (hx : 8 * (aggB k - 64 * (aggL k - 1)) ≤ x) (hx' : x < 512)
    (h : zN4 w (finBlk κ (aggChild κ a) k) (512 + x) ≠ 0) : ¬ AggPad4 κ a k w :=
  fun hp => h (hp.2 x hx hx')

/-- (−) `NodeResid4` binds `childOk4` (R-4-m2): an `N2` node whose aggregate has 3 segments has no
residual. -/
theorem not_resid_N2_k3 {Vseg : SegProgs} {Vnode : NodeProgs} {I : SlotIface4 Vseg Vnode} {rd : Read4}
    {vk c₁ c₂ : Digest} {w : Asg} (hk : kA rd .N2 w 0 = 3) : ¬ NodeResid4 I rd .N2 vk c₁ c₂ w := fun hR => by
  have := hR.kOk 0 (by decide); rw [hk] at this; exact absurd this (by decide)

/-- (+/−) The active slots: an `N2` node with a 2-segment aggregate uses slots 0, 1, 2; an `N8`
node's slot 5 is aggregate 1's second sub-slot (and inactive if that aggregate has one segment and
aggregate 0 at most `maxK = 4`, as `kOk` asks). -/
theorem active4_ctrl (rd : Read4) (w : Asg) (h2 : kA rd .N2 w 0 = 2) (h1 : kA rd .N8 w 1 = 1)
    (h0 : kA rd .N8 w 0 ≤ 4) :
    Active4 rd .N2 w 0 ∧ Active4 rd .N2 w 2 ∧ ¬ Active4 rd .N2 w 3 ∧ sub .N8 1 1 = 5 ∧
      ¬ Active4 rd .N8 w 5 := by
  refine ⟨.inl ⟨rfl, rfl⟩, .inr ⟨0, by decide, 1, by omega, rfl⟩, ?_, rfl, ?_⟩
  · rintro (⟨-, h⟩ | ⟨a, ha, i, hi, h⟩)
    · cases h
    · simp only [nAgg, NodeKind.hasPrev, if_true] at ha
      obtain rfl : a = 0 := by omega
      simp only [sub, NodeKind.hasPrev, if_true] at h; omega
  · rintro (⟨h, -⟩ | ⟨a, ha, i, hi, h⟩)
    · cases h
    · simp only [nAgg, NodeKind.hasPrev, Bool.false_eq_true, if_false] at ha
      simp only [sub, NodeKind.hasPrev, Bool.false_eq_true, if_false] at h
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · simp at h; omega
      · rw [h1] at hi; simp at h; omega

end N4c
end FR

end G6_FRNodeCircuit4
