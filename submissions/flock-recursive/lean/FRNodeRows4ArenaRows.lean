-- New for `flock-recursive` (PACK-4.4.1 §5.2–§5.3 as PK-M3 corrected; stage B2′, track L-circ).
import FRNodeRows4Arena
import FRNodeRows4Pack

/-!
# The two arenas: rows, what they give, and their closed-form values

PACK-4.4.1 §5.2 (PK-M3: every arena in the region of the slot whose prototype reads it). A slot's
stream (its first H block `b0`, `N` elements: `sCell b0 e`, `FRNodeRows4Pack`) is copied into M:

* **arena₁**: cell `A₁ + e` holds element `e`, by the row `R₁ + e`: `one·(M(A₁+e) − H(sCell b0 e)) = 0`
  (`a1Rows`);
* **the binding** (B2″, B2′'s option (a): arena₂ has no cells of its own): per level `i` (an
  `ALv`: `t` positions, `S` elements a position, the rows at a `2^a` stride from `B`, the level's
  first element `E`; the **consumers' import cells**: position `p`'s window at `C + p·2^c`, element
  `q` at the offset `off q` in it), the row `R₂ + B + p·2^a + q` ties the import cell
  `A₂ + C + p·2^c + off q` to arena₁'s `A₁ + E + S·p + q`:
  `one·(M(A₂ + C + p·2^c + off q) − M(A₁ + E + S·p + q)) = 0` (`a2Rows`);
* **bits** (`bitRows`): row `R_b + j` is `x·x = x` on the cell `B_t + j`, so it holds a bit.

**What the rows give** (the interface for B3/B4, `a1_cells`, `a2_cells`, `arena_elem`, `bit_cells`):
with `w one = 1`, the import cell of position `p`, element `q` is the stream element `E + S·p + q`,
i.e. the H cell `sCell b0 (E + S·p + q)`. Which import class reads which element (`E`, `S`, `off`)
is B3/B4's; `FRNodeRows4ArenaPlace` places arena₁, the binding's rows and the bits.

**Their values** (the matrices' MLEs at `(t, u)`, `rowsVal`): `a1_val` and `a2_val` state them as
diagonal sums, and `a1V`, `a2V` evaluate those by the carry automaton (`FRNodeRows4Arena.dRun`,
`O(log)` products, `a1V_eq`, `a2V_eq`). The H side of arena₁ is a shift by the constant `4·b0` on the
cell point without its coordinates 2–6 (`gN_sCell`). Nothing here evaluates a layout in the kernel.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Finset

/-! ## The rows -/

/-- The copy row `one·(M(x) − M(y)) = 0`. -/
def cpRow (one x y : ℕ) : Row := ⟨Lin.cell one, (Lin.cell x).sub (Lin.cell y), []⟩

theorem cpRow_holds {w : Asg} {one x y : ℕ} (hone : w one = 1) (h : (cpRow one x y).Holds w) :
    w x = w y := by
  simp only [cpRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_nil, hone, one_mul] at h
  exact sub_eq_zero.1 h

/-- **Arena₁'s rows**: row `R₁ + e` copies stream element `e` (`sCell b0 e`) to `A₁ + e`, `e < N`. -/
def a1Rows (one A1 R1 b0 N : ℕ) : List (ℕ × Row) :=
  (List.range N).map fun e => (R1 + e, cpRow one (A1 + e) (sCell b0 e))

/-- **A level of the binding** (B2″): `t` positions of `S` elements; their rows at a `2^a` stride from
`B`; their import cells, position `p`'s window at `C + p·2^c`, element `q` at `off q`; the level's
first element `E` (in arena₁). -/
structure ALv where
  t : ℕ
  S : ℕ
  a : ℕ
  B : ℕ
  c : ℕ
  C : ℕ
  off : ℕ → ℕ
  E : ℕ

/-- The import cell of position `p`, element `q` (from the base `A₂`). -/
def aCell (A2 : ℕ) (v : ALv) (p q : ℕ) : ℕ := A2 + v.C + p * 2 ^ v.c + v.off q

/-- **The binding's rows of a level**: row `R₂ + B + p·2^a + q` copies arena₁'s `A₁ + E + S·p + q`
to the import cell `aCell A₂ v p q`. -/
def a2Rows (one A1 A2 R2 : ℕ) (v : ALv) : List (ℕ × Row) :=
  (List.range v.t).flatMap fun p => (List.range v.S).map fun q =>
    (R2 + v.B + p * 2 ^ v.a + q, cpRow one (aCell A2 v p q) (A1 + v.E + v.S * p + q))

/-- The bit row `x·x = x`. -/
def bitRow (x : ℕ) : Row := ⟨Lin.cell x, Lin.cell x, Lin.cell x⟩

/-- **The bits' rows**: row `R_b + j` makes the cell `B_t + j` a bit, `j < n`. -/
def bitRows (Bt Rb n : ℕ) : List (ℕ × Row) := (List.range n).map fun j => (Rb + j, bitRow (Bt + j))

/-! ## What they give (B3/B4's interface) -/

/-- **Arena₁ holds the stream**: its rows give `M(A₁ + e) = H(sCell b0 e)`. -/
theorem a1_cells {w : Asg} {one A1 R1 b0 N : ℕ} (hone : w one = 1)
    (h : ∀ p ∈ a1Rows one A1 R1 b0 N, p.2.Holds w) {e : ℕ} (he : e < N) : w (A1 + e) = w (sCell b0 e) :=
  cpRow_holds hone (h (R1 + e, cpRow one (A1 + e) (sCell b0 e))
    (List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩))

/-- **An import cell holds arena₁'s element**: `M(aCell A₂ v p q) = M(A₁ + E + S·p + q)`. -/
theorem a2_cells {w : Asg} {one A1 A2 R2 : ℕ} {v : ALv} (hone : w one = 1)
    (h : ∀ p ∈ a2Rows one A1 A2 R2 v, p.2.Holds w) {p q : ℕ} (hp : p < v.t) (hq : q < v.S) :
    w (aCell A2 v p q) = w (A1 + v.E + v.S * p + q) :=
  cpRow_holds hone (h (R2 + v.B + p * 2 ^ v.a + q, cpRow one (aCell A2 v p q) (A1 + v.E + v.S * p + q))
    (List.mem_flatMap.2 ⟨p, List.mem_range.2 hp, List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩⟩))

/-- **An import cell is its stream element** (the binding's and arena₁'s rows hold, the element in
arena₁). -/
theorem arena_elem {w : Asg} {one A1 R1 b0 N A2 R2 : ℕ} {v : ALv} (hone : w one = 1)
    (h1 : ∀ p ∈ a1Rows one A1 R1 b0 N, p.2.Holds w) (h2 : ∀ p ∈ a2Rows one A1 A2 R2 v, p.2.Holds w)
    {p q : ℕ} (hp : p < v.t) (hq : q < v.S) (hN : v.E + v.S * p + q < N) :
    w (aCell A2 v p q) = w (sCell b0 (v.E + v.S * p + q)) := by
  rw [a2_cells hone h2 hp hq, show A1 + v.E + v.S * p + q = A1 + (v.E + v.S * p + q) by ring]
  exact a1_cells hone h1 hN

/-- **The bits' cells are bits.** -/
theorem bit_cells {w : Asg} {Bt Rb n : ℕ} (h : ∀ p ∈ bitRows Bt Rb n, p.2.Holds w) {j : ℕ} (hj : j < n) :
    w (Bt + j) = 0 ∨ w (Bt + j) = 1 := by
  have := h (Rb + j, bitRow (Bt + j)) (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  simp only [bitRow, Row.Holds, Lin.ev_cell] at this
  have h2 : w (Bt + j) * (w (Bt + j) - 1) = 0 := by rw [mul_sub, this, mul_one, sub_self]
  rcases mul_eq_zero.1 h2 with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

/-- (−) Not vacuous: the bit row fails at `y` (`F`'s generator, `y² ≠ y`); (+) it holds at `0` and `1`. -/
theorem bitRow_ctl : ¬ (bitRow 0).Holds (fun _ => F.y) ∧ (bitRow 0).Holds (fun _ => 0) ∧
    (bitRow 0).Holds (fun _ => 1) := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · simp only [bitRow, Row.Holds, Lin.ev_cell] at h
    exact (by decide +kernel : F.y * F.y ≠ F.y) h
  · simp [bitRow, Row.Holds, Lin.ev_cell]
  · simp [bitRow, Row.Holds, Lin.ev_cell]

/-- (+) The offset map places a level's elements: position 1's element 2 of a level with windows of
`2^4` cells at `C = 32` and `off q = 2·q + 1` is the import cell `32 + 16 + 5`, tied to arena₁'s
`E + S + 2`; (−) not to the unshifted `32 + 16 + 2`. -/
theorem aCell_ctl : aCell 0 ⟨2, 3, 2, 0, 4, 32, fun q => 2 * q + 1, 7⟩ 1 2 = 53 ∧
    aCell 0 ⟨2, 3, 2, 0, 4, 32, fun q => 2 * q + 1, 7⟩ 1 2 ≠ 50 ∧
    (a2Rows 0 100 0 1000 ⟨2, 3, 2, 0, 4, 32, fun q => 2 * q + 1, 7⟩).map (·.1) =
      [1000, 1001, 1002, 1004, 1005, 1006] := by
  refine ⟨rfl, by decide, by decide⟩

/-- (−) Not vacuous: a copy row with `M(x) ≠ M(y)` fails (`one = 1`, `x ↦ 1`, `y ↦ 0`). -/
theorem cpRow_ctl : ¬ (cpRow 0 1 2).Holds (fun i => if i ≤ 1 then 1 else 0) ∧
    (cpRow 0 1 2).Holds (fun _ => 1) := by
  simp [cpRow, Row.Holds, Lin.ev_sub]

/-! ## Their values -/

/-- A copy row's matrices at `(t, u)`: `a` the `one`, `b` the difference, `c` empty. -/
theorem linE_cp (m : ℕ) (u : ℕ → F) (one x y : ℕ) :
    linE (RingHom.id F) m u (Mat.r .a (cpRow one x y)) = gN m u one ∧
    linE (RingHom.id F) m u (Mat.r .b (cpRow one x y)) = gN m u x - gN m u y ∧
    linE (RingHom.id F) m u (Mat.r .c (cpRow one x y)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [linE, Mat.r, cpRow, Lin.cell]
  · simp only [linE, Mat.r, cpRow, Lin.cell, Lin.sub, Lin.smul, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.sum_cons, List.sum_nil, RingHom.id_apply]
    ring
  · simp [linE, Mat.r, cpRow]

/-- The rows' value, row by row. -/
theorem rowsVal_map {α : Type*} (s : Mat) (n m : ℕ) (t u : ℕ → F) (l : List α) (f : α → ℕ × Row) :
    rowsVal (RingHom.id F) s n m t u (l.map f) =
      (l.map fun x => gN n t (f x).1 * linE (RingHom.id F) m u (s.r (f x).2)).sum := by
  simp [rowsVal, List.map_map, Function.comp_def]

theorem list_sum_range {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ((List.range N).map f).sum = ∑ e ∈ range N, f e := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The rows' value of a `flatMap`, block by block. -/
theorem rowsVal_flatMap {α : Type*} (s : Mat) (n m : ℕ) (t u : ℕ → F) (g : α → List (ℕ × Row)) :
    ∀ l : List α, rowsVal (RingHom.id F) s n m t u (l.flatMap g) =
      (l.map fun x => rowsVal (RingHom.id F) s n m t u (g x)).sum
  | [] => by simp [rowsVal]
  | x :: l => by rw [List.flatMap_cons, rowsVal_append, rowsVal_flatMap s n m t u g l]; simp

/-- **Arena₁'s value**: `a = eq(u, one)·Σ_e eq(t, R₁+e)`, `b = Σ_e eq(t, R₁+e)·(eq(u, A₁+e) − eq(u, sCell b0 e))`,
`c = 0`. -/
theorem a1_val (n m : ℕ) (t u : ℕ → F) (one A1 R1 b0 N : ℕ) :
    rowsVal (RingHom.id F) .a n m t u (a1Rows one A1 R1 b0 N) = gN m u one * ∑ e ∈ range N, gN n t (R1 + e) ∧
    rowsVal (RingHom.id F) .b n m t u (a1Rows one A1 R1 b0 N) =
      ∑ e ∈ range N, gN n t (R1 + e) * gN m u (A1 + e) - ∑ e ∈ range N, gN n t (R1 + e) * gN m u (sCell b0 e) ∧
    rowsVal (RingHom.id F) .c n m t u (a1Rows one A1 R1 b0 N) = 0 := by
  simp only [a1Rows, rowsVal_map, (linE_cp m u _ _ _).1, (linE_cp m u _ _ _).2.1, (linE_cp m u _ _ _).2.2,
    list_sum_range, mul_zero, Finset.sum_const_zero, ← Finset.sum_sub_distrib, Finset.mul_sum, mul_sub]
  refine ⟨Finset.sum_congr rfl fun _ _ => mul_comm _ _, trivial, trivial⟩

/-! ## The H side: a shift by a constant -/

/-- `u` without its coordinates 2–6 (H's message slot `4 + e mod 4` puts `e`'s low bits at 0–1
and the block at 7 on). -/
def uH (u : ℕ → F) (l : ℕ) : F := if l < 2 then u l else u (l + 5)

/-- The constant coordinates of a message slot `4 + r` (`r < 4`): bit 2 set, 3–6 clear. -/
def kH (u : ℕ → F) : F := u 2 * ((1 - u 3) * (1 - u 4) * (1 - u 5) * (1 - u 6))

theorem eqN7_slot (u : ℕ → F) {r : ℕ} (hr : r < 4) : eqN 7 u (4 + r) = eqN 2 u r * kH u := by
  have h5 : eqN 5 (fun l => u (2 + l)) 1 = kH u := by
    have h := eqN_split (A := 1) (n := 5) (by norm_num) (fun l => u (2 + l)) 0 (j := 1) (by norm_num)
    simp only [mul_zero, zero_add] at h
    rw [h]
    simp [eqN, Finset.prod_range_succ, kH, Nat.testBit_zero]
  rw [show 4 + r = 2 ^ 2 * 1 + r by ring, eqN_split (by norm_num) u 1 (by norm_num; omega), h5]

/-- **`eq(u, sCell b0 e) = kH(u)·eq(uH u, 4·b0 + e)`** (the cells' bits 2–6 are constant). -/
theorem gN_sCell {m : ℕ} (hm : 7 ≤ m) (u : ℕ → F) (b0 e : ℕ) :
    gN m u (sCell b0 e) = kH u * gN (m - 5) (uH u) (4 * b0 + e) := by
  have hx : sCell b0 e = 2 ^ 7 * ((4 * b0 + e) / 4) + (4 + (4 * b0 + e) % 4) := by
    unfold sCell; omega
  have hy : 4 * b0 + e = 2 ^ 2 * ((4 * b0 + e) / 4) + (4 * b0 + e) % 4 := by omega
  have hr : (4 * b0 + e) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [hx, gN_split hm u _ (by omega), hy, gN_split (by omega) (uH u) _ hr, ← hy, eqN7_slot u hr]
  have h2 : eqN 2 (uH u) ((4 * b0 + e) % 4) = eqN 2 u ((4 * b0 + e) % 4) := by
    simp [eqN, Finset.prod_range_succ, uH]
  have h3 : (fun l => uH u (2 + l)) = fun l => u (7 + l) := by
    funext l; simp only [uH, show ¬ 2 + l < 2 by omega, if_false]; congr 1; omega
  rw [h2, h3, show m - 5 - 2 = m - 7 by omega]
  ring

/-! ## The automaton's evaluation -/

/-- The states' sums, by `diag_eq` for every state (`N ≤ 2^k`). -/
theorem dRun_sum (ft fu : ℕ → F) {k nt nu : ℕ} (f g : ℕ → ℕ → F) (L : List (DSt F)) (ht : k ≤ nt)
    (hu : k ≤ nu) (hN : ∀ x ∈ L, x.2.2.2 ≤ 2 ^ k)
    (hft : ∀ x, ft x = pB (nt - k) (fun l => f (k + l)) x) (hfu : ∀ x, fu x = pB (nu - k) (fun l => g (k + l)) x) :
    dRun ft fu k f g L =
      (L.map fun x => x.1 * ∑ e ∈ range x.2.2.2, pB nt f (x.2.1 + e) * pB nu g (x.2.2.1 + e)).sum := by
  rw [dRun_eq ft fu k nt nu f g L hft hfu, dTot]
  congr 1; refine List.map_congr_left fun x hx => ?_
  rw [dRec_eq k nt nu f g _ _ _ ht hu (hN x hx)]

/-- The high part's lookup at level `k` (the bit product of `t`'s coordinates from `k`). -/
def hiG (n k : ℕ) (t : ℕ → F) (x : ℕ) : F := gN (n - k) (fun l => t (k + l)) x

theorem hiG_pB (n k : ℕ) (t : ℕ → F) (x : ℕ) : hiG n k t x = pB (n - k) (fun l => eqF t (k + l)) x := by
  rw [hiG, gN_pB]; rfl

/-- The all-ones factors (a range sum's side). -/
def oneF (_ _ : ℕ) : F := 1

theorem pB_one {n : ℕ} {x : ℕ} (hx : x < 2 ^ n) : pB n oneF x = 1 := by simp [pB, hx, oneF]

/-- **Arena₁'s value by the automaton** (`k` bits of `e`: `N ≤ 2^k`, `k ≤ n`, `k + 5 ≤ m`): the range sum,
the M diagonal (`R₁`, `A₁`) and the H diagonal (`R₁`, `4·b0` on `uH u`), `O(k)` products each. -/
def a1V (n m k : ℕ) (t u : ℕ → F) (one A1 R1 b0 N : ℕ) : F3 :=
  let rs := dRun (hiG n k t) (pB 0 oneF) k (eqF t) oneF [(1, R1, 0, N)]
  let dm := dRun (hiG n k t) (hiG m k u) k (eqF t) (eqF u) [(1, R1, A1, N)]
  let dh := dRun (hiG n k t) (hiG (m - 5) k (uH u)) k (eqF t) (eqF (uH u)) [(1, R1, 4 * b0, N)]
  (gN m u one * rs, dm - kH u * dh, 0)

/-- **`a1V` is arena₁'s sparse value.** -/
theorem a1V_eq {n m k : ℕ} (hk : k ≤ n) (hm : k + 5 ≤ m) (hm7 : 7 ≤ m) (t u : ℕ → F) (one A1 R1 b0 N : ℕ)
    (hN : N ≤ 2 ^ k) :
    a1V n m k t u one A1 R1 b0 N = (rowsVal (RingHom.id F) .a n m t u (a1Rows one A1 R1 b0 N),
      rowsVal (RingHom.id F) .b n m t u (a1Rows one A1 R1 b0 N), rowsVal (RingHom.id F) .c n m t u (a1Rows one A1 R1 b0 N)) := by
  obtain ⟨ha, hb, hc⟩ := a1_val n m t u one A1 R1 b0 N
  have hs : ∀ (f g : ℕ → ℕ → F) (ft fu : ℕ → F) (nt nu a c : ℕ), k ≤ nt → k ≤ nu →
      (∀ x, ft x = pB (nt - k) (fun l => f (k + l)) x) → (∀ x, fu x = pB (nu - k) (fun l => g (k + l)) x) →
      dRun ft fu k f g [(1, a, c, N)] = ∑ e ∈ range N, pB nt f (a + e) * pB nu g (c + e) :=
    fun f g ft fu nt nu a c h1 h2 h3 h4 => diag_eq ft fu f g a c N h1 h2 hN h3 h4
  rw [ha, hb, hc]
  unfold a1V
  dsimp only
  rw [hs (eqF t) oneF (hiG n k t) (pB 0 oneF) n k R1 0 hk le_rfl (hiG_pB n k t)
      (fun x => by rw [Nat.sub_self]; rfl),
    hs (eqF t) (eqF u) (hiG n k t) (hiG m k u) n m R1 A1 hk (by omega) (hiG_pB n k t) (hiG_pB m k u),
    hs (eqF t) (eqF (uH u)) (hiG n k t) (hiG (m - 5) k (uH u)) n (m - 5) R1 (4 * b0) hk (by omega)
      (hiG_pB n k t) (hiG_pB (m - 5) k (uH u))]
  simp only [Prod.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · congr 1; refine Finset.sum_congr rfl fun e he => ?_
    rw [← gN_pB, pB_one (by have := Finset.mem_range.1 he; omega), mul_one]
  · simp only [← gN_pB, Finset.mul_sum]
    rw [sub_right_inj]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [gN_sCell (by omega)]; ring

/-- **The binding's value of a level**: per position `p`,
`Σ_q eq(t, r_p + q)·(eq(u, aCell A₂ v p q) − eq(u, A₁ + E + S·p + q))`, `r_p = R₂ + B + p·2^a`. -/
theorem a2_val (n m : ℕ) (t u : ℕ → F) (one A1 A2 R2 : ℕ) (v : ALv) :
    rowsVal (RingHom.id F) .b n m t u (a2Rows one A1 A2 R2 v) =
      ∑ p ∈ range v.t, ((∑ q ∈ range v.S, gN n t (R2 + v.B + p * 2 ^ v.a + q) * gN m u (aCell A2 v p q)) -
        ∑ q ∈ range v.S, gN n t (R2 + v.B + p * 2 ^ v.a + q) * gN m u (A1 + v.E + v.S * p + q)) := by
  rw [a2Rows, rowsVal_flatMap, list_sum_range]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [rowsVal_map, list_sum_range, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [(linE_cp m u _ _ _).2.1, mul_sub]

/-- **The import side of a level in closed form** (rows aligned to `2^a`, windows to `2^c`): the
positions' diagonal `Σ_p eq(t_{≥a}, P₀ + p)·eq(u_{≥c}, Q₀ + p)` (one automaton run, `t ≤ 2^k'`)
times the window's `Σ_q eq(t_{<a}, q)·eq(u_{<c}, off q)` (`S` products), once per level. -/
def a2M (n m k' : ℕ) (t u : ℕ → F) (A2 R2 : ℕ) (v : ALv) : F :=
  dRun (hiG (n - v.a) k' (fun l => t (v.a + l))) (hiG (m - v.c) k' (fun l => u (v.c + l))) k'
      (eqF (fun l => t (v.a + l))) (eqF (fun l => u (v.c + l)))
      [(1, (R2 + v.B) / 2 ^ v.a, (A2 + v.C) / 2 ^ v.c, v.t)] *
    ((List.range v.S).map fun q => eqN v.a t q * eqN v.c u (v.off q)).sum

/-- **The binding's value of a level by the automaton**: the import side `a2M`, minus per position
one run of the shift-window automaton on arena₁'s side (one state). -/
def a2V (n m k k' : ℕ) (t u : ℕ → F) (A1 A2 R2 : ℕ) (v : ALv) : F :=
  a2M n m k' t u A2 R2 v - ((List.range v.t).map fun p =>
    dRun (hiG n k t) (hiG m k u) k (eqF t) (eqF u) [(1, R2 + v.B + p * 2 ^ v.a, A1 + v.E + v.S * p, v.S)]).sum

/-- The import side's closed form. -/
theorem a2M_eq {n m k' : ℕ} (t u : ℕ → F) (A2 R2 : ℕ) (v : ALv) (ha : v.a ≤ n) (hc : v.c ≤ m)
    (hk1 : k' ≤ n - v.a) (hk2 : k' ≤ m - v.c) (ht : v.t ≤ 2 ^ k') (hR : 2 ^ v.a ∣ R2 + v.B)
    (hC : 2 ^ v.c ∣ A2 + v.C) (hSa : v.S ≤ 2 ^ v.a) (hoff : ∀ q < v.S, v.off q < 2 ^ v.c) :
    a2M n m k' t u A2 R2 v =
      ∑ p ∈ range v.t, ∑ q ∈ range v.S, gN n t (R2 + v.B + p * 2 ^ v.a + q) * gN m u (aCell A2 v p q) := by
  obtain ⟨P0, hP⟩ := hR
  obtain ⟨Q0, hQ⟩ := hC
  have hr : ∀ p q, q < v.S → gN n t (R2 + v.B + p * 2 ^ v.a + q) =
      eqN v.a t q * gN (n - v.a) (fun l => t (v.a + l)) (P0 + p) := fun p q hq => by
    rw [show R2 + v.B + p * 2 ^ v.a + q = 2 ^ v.a * (P0 + p) + q by rw [hP]; ring]
    exact gN_split ha t _ (by omega)
  have hu : ∀ p q, q < v.S → gN m u (aCell A2 v p q) =
      eqN v.c u (v.off q) * gN (m - v.c) (fun l => u (v.c + l)) (Q0 + p) := fun p q hq => by
    rw [aCell, show A2 + v.C + p * 2 ^ v.c + v.off q = 2 ^ v.c * (Q0 + p) + v.off q by
      rw [hQ]; ring]
    exact gN_split hc u _ (hoff q hq)
  have hd := diag_eq (hiG (n - v.a) k' (fun l => t (v.a + l))) (hiG (m - v.c) k' (fun l => u (v.c + l)))
    (eqF (fun l => t (v.a + l))) (eqF (fun l => u (v.c + l))) P0 Q0 v.t hk1 hk2 ht
    (hiG_pB (n - v.a) k' _) (hiG_pB (m - v.c) k' _)
  have h2a : 0 < 2 ^ v.a := by positivity
  have h2c : 0 < 2 ^ v.c := by positivity
  rw [a2M, show (R2 + v.B) / 2 ^ v.a = P0 by rw [hP, Nat.mul_div_cancel_left _ h2a],
    show (A2 + v.C) / 2 ^ v.c = Q0 by rw [hQ, Nat.mul_div_cancel_left _ h2c], hd, list_sum_range,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q hq => ?_
  rw [hr p q (Finset.mem_range.1 hq), hu p q (Finset.mem_range.1 hq), ← gN_pB, ← gN_pB]
  ring

/-- **`a2V` is the binding's sparse value.** -/
theorem a2V_eq {n m k k' : ℕ} (hk : k ≤ n) (hm : k ≤ m) (t u : ℕ → F) (one A1 A2 R2 : ℕ) (v : ALv)
    (hS : v.S ≤ 2 ^ k) (ha : v.a ≤ n) (hc : v.c ≤ m) (hk1 : k' ≤ n - v.a) (hk2 : k' ≤ m - v.c)
    (ht : v.t ≤ 2 ^ k') (hR : 2 ^ v.a ∣ R2 + v.B) (hC : 2 ^ v.c ∣ A2 + v.C) (hSa : v.S ≤ 2 ^ v.a)
    (hoff : ∀ q < v.S, v.off q < 2 ^ v.c) :
    a2V n m k k' t u A1 A2 R2 v = rowsVal (RingHom.id F) .b n m t u (a2Rows one A1 A2 R2 v) := by
  rw [a2_val, a2V, a2M_eq t u A2 R2 v ha hc hk1 hk2 ht hR hC hSa hoff, list_sum_range,
    Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [diag_eq _ _ _ _ _ _ _ hk hm hS (hiG_pB n k t) (hiG_pB m k u)]
  simp only [← gN_pB]

/-- **The bits' value**: each matrix is `Σ_j eq(t, R_b + j)·eq(u, B_t + j)`, one automaton run
(`n ≤ 2^k`). -/
def bitV (n m k : ℕ) (t u : ℕ → F) (Bt Rb N : ℕ) : F3 :=
  let d := dRun (hiG n k t) (hiG m k u) k (eqF t) (eqF u) [(1, Rb, Bt, N)]
  (d, d, d)

theorem bitV_eq {n m k : ℕ} (hk : k ≤ n) (hm : k ≤ m) (t u : ℕ → F) (Bt Rb N : ℕ) (hN : N ≤ 2 ^ k) :
    bitV n m k t u Bt Rb N = (rowsVal (RingHom.id F) .a n m t u (bitRows Bt Rb N),
      rowsVal (RingHom.id F) .b n m t u (bitRows Bt Rb N), rowsVal (RingHom.id F) .c n m t u (bitRows Bt Rb N)) := by
  have hd : dRun (hiG n k t) (hiG m k u) k (eqF t) (eqF u) [(1, Rb, Bt, N)] =
      ∑ j ∈ range N, gN n t (Rb + j) * gN m u (Bt + j) := by
    rw [diag_eq _ _ _ _ _ _ _ hk hm hN (hiG_pB n k t) (hiG_pB m k u)]; simp only [← gN_pB]
  have hr : ∀ s : Mat, rowsVal (RingHom.id F) s n m t u (bitRows Bt Rb N) =
      ∑ j ∈ range N, gN n t (Rb + j) * gN m u (Bt + j) := fun s => by
    rw [bitRows, rowsVal_map, list_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases s <;> simp [bitRow, Mat.r, linE, Lin.cell]
  simp only [bitV, hd, hr]

end Rev4
end FR
