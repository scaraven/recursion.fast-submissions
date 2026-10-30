-- New for `flock-recursive` (track CF: closed-form evaluation of the replay templates).
import FRVIRTplChain
import FRVIRTplKMux
import FRVIRTplEval

/-!
# Repeated patterns in a template, and their rows' MLE in closed form

A replay template's rows are evaluated by the plan as a multilinear extension: row `X + i` of the
template, its forms over the wires. Most rows of the large templates are **instances of one
pattern**: the same gates `n` times, instance `s` at local `K + s·2^p`, its inputs read through
**placeholders** (`σ s i`, a form over the template's wires per instance).

* **`rowsAt gs k`**: a gate list's rows from local `k` (`Tpl.rows = rowsAt · 0`); `rowsAt_sub`:
  substituted gates (`Gate.sub`) have the substituted rows.
* **`tm s t e X rows`**: rows `X, X+1, …` at the row point `t` (20 coordinates), the forms at the
  wires `e` (matrix `s`); `tm_sub` (substitution is a pull-back of the wires), `tm_append`.
* **`Rep`**: `n` instances of a pattern padded to `2^p` rows and locals (`Rep.gates`).
* **`tm_rep`**: the rows' value in closed form. Instance `s`'s row `r` is row
  `X + s·2^p + r = 2^p·(⌊X/2^p⌋ + s + c_r) + lo_r`: the carry `c_r` and the low part `lo_r` depend on
  `r` only, so `eq(t, ·)` splits into a pattern factor and an instance factor `T(s + c_r)` for **any**
  offset `X`; a local of instance `s` likewise. The value is one pass over the pattern's rows with,
  per wire, an instance sum (`cW`).
-/

namespace FR
namespace Tpl
open Circ TEval Finset

/-! ## Rows from a first local -/

/-- A gate list's rows, its first local at `k`. -/
def rowsAt (gs : List Gate) (k : ℕ) : List RowT := (gatesAt gs k).flatMap fun p => p.2.rows p.1

@[simp] theorem rowsAt_nil (k : ℕ) : rowsAt [] k = [] := rfl

theorem rowsAt_cons (g : Gate) (gs : List Gate) (k : ℕ) :
    rowsAt (g :: gs) k = g.rows k ++ rowsAt gs (k + g.nloc) := by
  simp [rowsAt, gatesAt]

theorem rowsAt_append (a b : List Gate) (k : ℕ) :
    rowsAt (a ++ b) k = rowsAt a k ++ rowsAt b (k + nlocs a) := by
  simp [rowsAt, gatesAt_append]

theorem tpl_rows_eq (T : Tpl) : T.rows = rowsAt T.gates 0 := rfl

/-- A gate's row count (independent of its first local). -/
def Gate.nrow : Gate → ℕ
  | .mul .. => 1
  | .inv _ => 3
  | .mulAdd .. => 1
  | .pad r _ => r

theorem Gate.rows_length (g : Gate) (k : ℕ) : (g.rows k).length = g.nrow := by
  cases g <;> simp [Gate.rows, Gate.nrow]

/-- A gate list's row count. -/
def nrows (gs : List Gate) : ℕ := (gs.map Gate.nrow).sum

theorem rowsAt_length : ∀ (gs : List Gate) (k : ℕ), (rowsAt gs k).length = nrows gs
  | [], _ => rfl
  | g :: gs, k => by
    rw [rowsAt_cons, List.length_append, Gate.rows_length, rowsAt_length gs]; simp [nrows]

theorem nrows_append (a b : List Gate) : nrows (a ++ b) = nrows a + nrows b := by simp [nrows]

theorem nlocs_app (a b : List Gate) : nlocs (a ++ b) = nlocs a + nlocs b := by simp [nlocs]

/-! ## Substitution -/

/-- A row with its forms substituted. -/
def RowT.sub (σ : ℕ → LinT) (k0 : ℕ) (r : RowT) : RowT := ⟨subW σ k0 r.a, subW σ k0 r.b, subW σ k0 r.c⟩

theorem subW_L (σ : ℕ → LinT) (k0 k : ℕ) : subW σ k0 (L k) = L (k0 + k) := rfl

theorem subW_C (σ : ℕ → LinT) (k0 : ℕ) (c : F) : subW σ k0 (C c) = C c := rfl

theorem subW_app (σ : ℕ → LinT) (k0 : ℕ) (a b : LinT) : subW σ k0 (a ++ b) = subW σ k0 a ++ subW σ k0 b := by
  simp [subW, List.flatMap_append]

theorem subW_sc (σ : ℕ → LinT) (k0 : ℕ) (c : F) : ∀ l : LinT, subW σ k0 (sc c l) = sc c (subW σ k0 l)
  | [] => rfl
  | t :: l => by
    obtain ⟨w, x⟩ := t
    have ih := subW_sc σ k0 c l
    simp only [sc, List.map_cons] at ih ⊢
    rw [subW_cons, subW_cons σ k0 (w, x), List.map_append, ih]
    congr 1
    cases w <;> simp [subW, sc, mul_assoc]

theorem Gate.rows_sub (σ : ℕ → LinT) (k0 k : ℕ) (g : Gate) :
    (g.sub σ k0).rows (k0 + k) = (g.rows k).map (RowT.sub σ k0) := by
  cases g with
  | mul a b => rfl
  | inv a =>
    simp only [Gate.sub, Gate.rows, List.map_cons, List.map_nil, RowT.sub, subW_L, subW_app, subW_C,
      subW_sc, Nat.add_assoc]
    rfl
  | mulAdd a b c =>
    simp only [Gate.sub, Gate.rows, List.map_cons, List.map_nil, RowT.sub, subW_L, subW_app, subW_sc]
  | pad r l => simp only [Gate.sub, Gate.rows, List.map_replicate]; rfl

theorem rowsAt_sub (σ : ℕ → LinT) (k0 : ℕ) :
    ∀ (gs : List Gate) (k : ℕ), rowsAt (gs.map (Gate.sub σ k0)) (k0 + k) = (rowsAt gs k).map (RowT.sub σ k0)
  | [], _ => rfl
  | g :: gs, k => by
    rw [List.map_cons, rowsAt_cons, rowsAt_cons, nloc_sub, Gate.rows_sub, Nat.add_assoc, rowsAt_sub σ k0 gs,
      List.map_append]

theorem nrows_sub (σ : ℕ → LinT) (k0 : ℕ) (gs : List Gate) : nrows (gs.map (Gate.sub σ k0)) = nrows gs := by
  simp only [nrows, List.map_map]; congr 1; exact List.map_congr_left fun g _ => by cases g <;> rfl

theorem nlocs_subL (σ : ℕ → LinT) (k0 : ℕ) (gs : List Gate) : nlocs (gs.map (Gate.sub σ k0)) = nlocs gs := by
  simp only [nlocs, List.map_map]; congr 1; exact List.map_congr_left fun g _ => nloc_sub σ k0 g

/-! ## The rows' value -/

/-- **Rows `X, X+1, …`' value** (matrix `s`): `Σ_i eq(t, X + i)·⟨form_i, e⟩` over 20 row coordinates. -/
def tm (s : Mat) (t : ℕ → F) (e : Env) : ℕ → List RowT → F
  | _, [] => 0
  | X, r :: rs => gN 20 t X * (s.t r).ev e + tm s t e (X + 1) rs

theorem tm_append (s : Mat) (t : ℕ → F) (e : Env) :
    ∀ (X : ℕ) (a b : List RowT), tm s t e X (a ++ b) = tm s t e X a + tm s t e (X + a.length) b
  | _, [], _ => by simp [tm]
  | X, r :: a, b => by
    rw [List.cons_append, tm, tm, tm_append s t e (X + 1) a b, List.length_cons]
    rw [show X + 1 + a.length = X + (a.length + 1) by omega]; ring

theorem Mat.t_sub (s : Mat) (σ : ℕ → LinT) (k0 : ℕ) (r : RowT) : s.t (r.sub σ k0) = subW σ k0 (s.t r) := by
  cases s <;> rfl

/-- **Substituted rows are the rows at the pulled-back wires.** -/
theorem tm_sub (s : Mat) (t : ℕ → F) (e : Env) (σ : ℕ → LinT) (k0 : ℕ) :
    ∀ (X : ℕ) (rows : List RowT), tm s t e X (rows.map (RowT.sub σ k0)) = tm s t (pullE e σ k0) X rows
  | _, [] => rfl
  | X, r :: rs => by rw [List.map_cons, tm, tm, Mat.t_sub, subW_ev, tm_sub s t e σ k0 (X + 1) rs]

theorem tm_eq_sum (s : Mat) (t : ℕ → F) (e : Env) :
    ∀ (X : ℕ) (rows : List RowT), tm s t e X rows = ((rows.zipIdx X).map fun q => gN 20 t q.2 * (s.t q.1).ev e).sum
  | _, [] => rfl
  | X, r :: rs => by rw [tm, tm_eq_sum s t e (X + 1) rs, List.zipIdx_cons, List.map_cons, List.sum_cons]

/-- Empty rows have value `0`. -/
theorem tm_empty (s : Mat) (t : ℕ → F) (e : Env) : ∀ (X n : ℕ), tm s t e X (List.replicate n ⟨[], [], []⟩) = 0
  | _, 0 => rfl
  | X, n + 1 => by
    rw [List.replicate_succ, tm, tm_empty s t e (X + 1) n]; cases s <;> simp [Mat.t]


/-! ## Repeated patterns -/

/-- A placeholder: one form for every instance (`cst`), or one per instance (`var`). -/
inductive Ph where
  | cst (f : LinT)
  | var (fs : Array LinT)

/-- The placeholder's form at instance `s`. -/
def Ph.at : Ph → ℕ → LinT
  | .cst f, _ => f
  | .var fs, s => fs.getD s []

/-- **A repeated pattern**: `n` instances of the gates `pat`, padded to `2^p` rows and `2^p` locals;
instance `s` reads the pattern's input `i` as the form `σ s i` (placeholder `ph[i]`). -/
structure Rep where
  n : ℕ
  p : ℕ
  pat : List Gate
  ph : Array Ph

namespace Rep
variable (R : Rep)

/-- Instance `s`'s input `i`. -/
def σ (s i : ℕ) : LinT := (R.ph.getD i (.cst [])).at s

/-- The pattern padded to `2^p` rows and locals. -/
def padP : List Gate := R.pat ++ [.pad (2 ^ R.p - nrows R.pat) (2 ^ R.p - nlocs R.pat)]

/-- The first `m` instances' gates, the first one's locals from `K`. -/
def gatesN (m K : ℕ) : List Gate :=
  (List.range m).flatMap fun s => R.padP.map (Gate.sub (R.σ s) (K + s * 2 ^ R.p))

/-- **The repeated pattern's gates**, from local `K`. -/
def gates (K : ℕ) : List Gate := R.gatesN R.n K

/-- The pattern fits its stride. -/
def Fit : Prop := nrows R.pat ≤ 2 ^ R.p ∧ nlocs R.pat ≤ 2 ^ R.p

theorem nrows_padP (h : R.Fit) : nrows R.padP = 2 ^ R.p := by
  simp only [padP, nrows_append]; simp [nrows, Gate.nrow]; have := h.1; simp only [nrows] at this; omega

theorem nlocs_padP (h : R.Fit) : nlocs R.padP = 2 ^ R.p := by
  simp only [padP, nlocs_app]; simp [nlocs, Gate.nloc]; have := h.2; simp only [nlocs] at this; omega

theorem nlocs_gatesN (K : ℕ) : ∀ m, nlocs (R.gatesN m K) = m * nlocs R.padP
  | 0 => by simp [gatesN, nlocs]
  | m + 1 => by
    simp only [gatesN, List.range_succ, List.flatMap_append, List.flatMap_singleton, nlocs_app] at *
    rw [show nlocs ((List.range m).flatMap fun s => R.padP.map (Gate.sub (R.σ s) (K + s * 2 ^ R.p))) =
      nlocs (R.gatesN m K) from rfl, nlocs_gatesN K m, nlocs_subL]; ring

theorem nrows_gatesN (K : ℕ) : ∀ m, nrows (R.gatesN m K) = m * nrows R.padP
  | 0 => by simp [gatesN, nrows]
  | m + 1 => by
    simp only [gatesN, List.range_succ, List.flatMap_append, List.flatMap_singleton, nrows_append] at *
    rw [show nrows ((List.range m).flatMap fun s => R.padP.map (Gate.sub (R.σ s) (K + s * 2 ^ R.p))) =
      nrows (R.gatesN m K) from rfl, nrows_gatesN K m, nrows_sub]; ring

/-- The rows of the first `m` instances: the pattern's rows, substituted per instance. -/
theorem rowsAt_gatesN (h : R.Fit) (K : ℕ) : ∀ m, rowsAt (R.gatesN m K) K =
    (List.range m).flatMap fun s => (rowsAt R.padP 0).map (RowT.sub (R.σ s) (K + s * 2 ^ R.p))
  | 0 => rfl
  | m + 1 => by
    have e : R.gatesN (m + 1) K = R.gatesN m K ++ R.padP.map (Gate.sub (R.σ m) (K + m * 2 ^ R.p)) := by
      simp [gatesN, List.range_succ, List.flatMap_append]
    have hs := rowsAt_sub (R.σ m) (K + m * 2 ^ R.p) R.padP 0
    rw [Nat.add_zero] at hs
    rw [e, rowsAt_append, rowsAt_gatesN h K m, nlocs_gatesN, nlocs_padP R h, hs, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

end Rep

/-- The pattern's rows are the padded pattern's, less empty rows. -/
theorem tm_padP (R : Rep) (s : Mat) (t : ℕ → F) (e : Env) (X : ℕ) :
    tm s t e X (rowsAt R.padP 0) = tm s t e X (rowsAt R.pat 0) := by
  rw [Rep.padP, rowsAt_append, tm_append, rowsAt_cons]
  simp only [Gate.rows, rowsAt_nil, List.append_nil, tm_empty, add_zero]

/-- **The rows of a repeated pattern, instance by instance**: instance `s` is the pattern's rows at
`X + s·2^p`, at the wires it sees. -/
theorem tm_repI (R : Rep) (h : R.Fit) (s : Mat) (t : ℕ → F) (e : Env) (X K : ℕ) :
    tm s t e X (rowsAt (R.gates K) K) =
      ∑ i ∈ range R.n, tm s t (pullE e (R.σ i) (K + i * 2 ^ R.p)) (X + i * 2 ^ R.p) (rowsAt R.pat 0) := by
  rw [Rep.gates, Rep.rowsAt_gatesN R h]
  have hl : ∀ i, ((rowsAt R.padP 0).map (RowT.sub (R.σ i) (K + i * 2 ^ R.p))).length = 2 ^ R.p := fun i => by
    rw [List.length_map, rowsAt_length, R.nrows_padP h]
  suffices ∀ m, tm s t e X ((List.range m).flatMap fun i => (rowsAt R.padP 0).map (RowT.sub (R.σ i) (K + i * 2 ^ R.p))) =
      ∑ i ∈ range m, tm s t (pullE e (R.σ i) (K + i * 2 ^ R.p)) (X + i * 2 ^ R.p) (rowsAt R.pat 0) from this R.n
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, tm_append, ih, Finset.sum_range_succ,
      tm_sub, tm_padP]
    congr 2
    rw [List.length_flatMap]
    simp only [hl, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

/-! ## The closed form -/

/-- The split of a row (or cell) `Y + i·2^p + r` at bit `p`: the low part and the carry depend on `r`. -/
theorem gN_spl {p : ℕ} (hp : p ≤ 20) (t : ℕ → F) (Y i r : ℕ) :
    gN 20 t (Y + i * 2 ^ p + r) = eqN p t ((Y % 2 ^ p + r) % 2 ^ p) *
      gN (20 - p) (fun l => t (p + l)) (Y / 2 ^ p + (i + (Y % 2 ^ p + r) / 2 ^ p)) := by
  have hP : 0 < 2 ^ p := Nat.two_pow_pos p
  have h1 := Nat.div_add_mod Y (2 ^ p)
  have h2 := Nat.div_add_mod (Y % 2 ^ p + r) (2 ^ p)
  have e : Y + i * 2 ^ p + r = 2 ^ p * (Y / 2 ^ p + (i + (Y % 2 ^ p + r) / 2 ^ p)) + (Y % 2 ^ p + r) % 2 ^ p := by
    rw [mul_add, mul_add]
    nlinarith [h1, h2]
  rw [e, gN_split hp t _ (Nat.mod_lt _ hP)]

/-- Sums commute with a list sum. -/
theorem sum_listSum {α : Type*} (n : ℕ) (f : ℕ → α → F) :
    ∀ l : List α, ∑ i ∈ range n, (l.map (f i)).sum = (l.map fun a => ∑ i ∈ range n, f i a).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, sum_listSum n f l]

namespace Rep
variable (R : Rep)

/-- The instance factor of the rows: `eq(t_hi, ⌊X/2^p⌋ + h)`. -/
def Tf (t : ℕ → F) (X h : ℕ) : F := gN (20 - R.p) (fun l => t (R.p + l)) (X / 2 ^ R.p + h)

/-- The carry of pattern row (or local) `r` at offset `Y`. -/
def car (Y r : ℕ) : ℕ := (Y % 2 ^ R.p + r) / 2 ^ R.p

/-- The low part of pattern row (or local) `r` at offset `Y`. -/
def low (Y r : ℕ) : ℕ := (Y % 2 ^ R.p + r) % 2 ^ R.p

/-- **A wire's instance sum** for pattern row `r`: `Σ_s T(s + c_r)·(wire at instance s)`. -/
def cW (t : ℕ → F) (e : Env) (X K r : ℕ) (w : Wire) : F :=
  ∑ i ∈ range R.n, R.Tf t X (i + R.car X r) * w.ev (pullE e (R.σ i) (K + i * 2 ^ R.p))

/-- The closed form over the pattern's rows from pattern row `r`. -/
def passV (s : Mat) (t : ℕ → F) (e : Env) (X K : ℕ) : ℕ → List RowT → F
  | _, [] => 0
  | r, row :: rows => eqN R.p t (R.low X r) * ((s.t row).map fun τ => τ.2 * R.cW t e X K r τ.1).sum +
      passV s t e X K (r + 1) rows

theorem passV_eq (hp : R.p ≤ 20) (s : Mat) (t : ℕ → F) (e : Env) (X K : ℕ) :
    ∀ (r : ℕ) (rows : List RowT), ∑ i ∈ range R.n, tm s t (pullE e (R.σ i) (K + i * 2 ^ R.p)) (X + i * 2 ^ R.p + r) rows =
      R.passV s t e X K r rows
  | _, [] => by simp [tm, passV]
  | r, row :: rows => by
    simp only [tm, passV, Finset.sum_add_distrib]
    rw [← passV_eq hp s t e X K (r + 1) rows]
    congr 1
    · simp only [gN_spl hp, LinT.ev, cW, Tf, car, low]
      rw [← List.sum_map_mul_left]
      simp only [Finset.mul_sum]
      rw [← sum_listSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← List.sum_map_mul_left]
      exact congrArg List.sum (List.map_congr_left fun τ _ => by ring)

end Rep


theorem lsum_range (n : ℕ) (f : ℕ → F) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

namespace Rep
variable (R : Rep)

/-- **The rows of a repeated pattern in closed form** (one pass over the pattern's rows). -/
theorem tm_rep (h : R.Fit) (hp : R.p ≤ 20) (s : Mat) (t : ℕ → F) (e : Env) (X K : ℕ) :
    tm s t e X (rowsAt (R.gates K) K) = R.passV s t e X K 0 (rowsAt R.pat 0) := by
  rw [tm_repI R h, ← R.passV_eq hp s t e X K 0]; simp only [Nat.add_zero]

/-! ### The wires' instance sums -/

theorem cW_one (t : ℕ → F) (e : Env) (X K r : ℕ) :
    R.cW t e X K r .one = e.one * ∑ i ∈ range R.n, R.Tf t X (i + R.car X r) := by
  simp only [cW, Wire.ev, pullE, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem cW_inp (t : ℕ → F) (e : Env) (X K r j : ℕ) :
    R.cW t e X K r (.inp j) = ∑ i ∈ range R.n, R.Tf t X (i + R.car X r) * (R.σ i j).ev e := rfl

theorem cW_loc (hp : R.p ≤ 20) (t u : ℕ → F) (e : Env) (lam : F) (cl X K r k : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) :
    R.cW t e X K r (.loc k) = lam * eqN R.p u (R.low (cl + K) k) *
      ∑ i ∈ range R.n, R.Tf t X (i + R.car X r) * R.Tf u (cl + K) (i + R.car (cl + K) k) := by
  simp only [cW, Wire.ev, pullE, he, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show cl + (K + i * 2 ^ R.p + k) = (cl + K) + i * 2 ^ R.p + k by ring, gN_spl hp]; simp only [Tf, low, car]; ring

/-! ### The evaluation: per-call sums once, then one pass over the pattern -/

/-- `Tf` at `h < n + 2` (the carries of rows and locals below `2^p` are `0` or `1`). -/
def tArr (t : ℕ → F) (X : ℕ) : Array F :=
  (Array.range (R.n + 2)).map fun h => gNL (20 - R.p) (fun l => t (R.p + l)) (X / 2 ^ R.p + h)

/-- `Tf` from the array, directly past it. -/
def tAt (A : Array F) (t : ℕ → F) (X h : ℕ) : F := if h < R.n + 2 then A.getD h 0 else R.Tf t X h

theorem tAt_eq (t : ℕ → F) (X h : ℕ) : R.tAt (R.tArr t X) t X h = R.Tf t X h := by
  unfold tAt
  split_ifs with hh
  · simp [tArr, Array.getD_eq_getD_getElem?, hh, gNL_eq, Tf]
  · rfl

def sS (A : Array F) (t : ℕ → F) (X c : ℕ) : F := sumL (fun i => R.tAt A t X (i + c)) (List.range R.n)

def sD (A B : Array F) (t u : ℕ → F) (X Y c c' : ℕ) : F :=
  sumL (fun i => R.tAt A t X (i + c) * R.tAt B u Y (i + c')) (List.range R.n)

def sZ (A : Array F) (t : ℕ → F) (e : Env) (X j c : ℕ) : F :=
  match R.ph.getD j (.cst []) with
  | .cst f => f.ev e * R.sS A t X c
  | .var fs => sumL (fun i => R.tAt A t X (i + c) * (fs.getD i []).ev e) (List.range R.n)

/-- A repeated pattern's per-call sums. -/
structure Cx where
  tA : Array F
  uA : Array F
  S0 : F
  S1 : F
  D : Array F
  Z : Array (F × F)
  tl : Array F
  ul : Array F

/-- **The per-call sums** (row point `t`, cell point `u`, wires `e` with locals `lam·eq(u, cl + ·)`,
rows from `X`, the pattern's first local `K`). -/
def ctx (t u : ℕ → F) (e : Env) (cl X K : ℕ) : Cx :=
  let tA := R.tArr t X
  let uA := R.tArr u (cl + K)
  ⟨tA, uA, R.sS tA t X 0, R.sS tA t X 1,
    #[R.sD tA uA t u X (cl + K) 0 0, R.sD tA uA t u X (cl + K) 0 1, R.sD tA uA t u X (cl + K) 1 0,
      R.sD tA uA t u X (cl + K) 1 1],
    (Array.range R.ph.size).map fun j => (R.sZ tA t e X j 0, R.sZ tA t e X j 1), loTab R.p t, loTab R.p u⟩

/-- A wire's instance sum from the context (carry `c` of its row). -/
def wv (cx : Cx) (t u : ℕ → F) (e : Env) (lam : F) (cl X K c : ℕ) : Wire → F
  | .one => e.one * (if c = 0 then cx.S0 else if c = 1 then cx.S1 else R.sS cx.tA t X c)
  | .inp j => if c < 2 ∧ j < cx.Z.size then (if c = 0 then (cx.Z.getD j (0, 0)).1 else (cx.Z.getD j (0, 0)).2)
      else R.sZ cx.tA t e X j c
  | .loc k => lam * cx.ul.getD (R.low (cl + K) k) 0 *
      (if c < 2 ∧ R.car (cl + K) k < 2 then cx.D.getD (2 * c + R.car (cl + K) k) 0
       else R.sD cx.tA cx.uA t u X (cl + K) c (R.car (cl + K) k))

/-- **One pass over the pattern's rows** (from pattern row `r`). -/
def pass (s : Mat) (cx : Cx) (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ) : ℕ → List RowT → F
  | _, [] => 0
  | r, row :: rows => cx.tl.getD (R.low X r) 0 * sumL (fun τ => τ.2 * R.wv cx t u e lam cl X K (R.car X r) τ.1) (s.t row) +
      pass s cx t u e lam cl X K (r + 1) rows

theorem sS_eq (t : ℕ → F) (X c : ℕ) : R.sS (R.tArr t X) t X c = ∑ i ∈ range R.n, R.Tf t X (i + c) := by
  simp only [sS, sumL_eq, tAt_eq, lsum_range]

theorem sD_eq (t u : ℕ → F) (X Y c c' : ℕ) :
    R.sD (R.tArr t X) (R.tArr u Y) t u X Y c c' = ∑ i ∈ range R.n, R.Tf t X (i + c) * R.Tf u Y (i + c') := by
  simp only [sD, sumL_eq, tAt_eq, lsum_range]

theorem sZ_eq (t : ℕ → F) (e : Env) (X j c : ℕ) :
    R.sZ (R.tArr t X) t e X j c = ∑ i ∈ range R.n, R.Tf t X (i + c) * (R.σ i j).ev e := by
  unfold sZ σ
  split
  · rename_i f hf
    rw [sS_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hf]; simp only [Ph.at]; ring
  · rename_i fs hf
    simp only [sumL_eq, tAt_eq, lsum_range, hf, Ph.at]

theorem wv_eq (hp : R.p ≤ 20) (t u : ℕ → F) (e : Env) (lam : F) (cl X K r : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) (w : Wire) :
    R.wv (R.ctx t u e cl X K) t u e lam cl X K (R.car X r) w = R.cW t e X K r w := by
  cases w with
  | one =>
    rw [cW_one, wv]
    congr 1
    simp only [ctx]
    split_ifs with h0 h1
    · rw [h0, sS_eq]
    · rw [h1, sS_eq]
    · rw [sS_eq]
  | inp j =>
    rw [cW_inp, wv, ← sZ_eq]
    simp only [ctx, Array.size_map, Array.size_range]
    split_ifs with h h0
    · simp [Array.getD_eq_getD_getElem?, h.2, h0]
    · have : R.car X r = 1 := by omega
      simp [Array.getD_eq_getD_getElem?, h.2, this]
    · rfl
  | loc k =>
    rw [cW_loc R hp t u e lam cl X K r k he, wv]
    simp only [ctx]
    rw [loTab_getD _ _ (show R.low (cl + K) k < 2 ^ R.p from Nat.mod_lt _ (Nat.two_pow_pos _))]
    congr 1
    rw [← sD_eq]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      interval_cases hc : R.car X r <;> interval_cases hc' : R.car (cl + K) k <;> rfl
    · rfl

theorem pass_eq (hp : R.p ≤ 20) (s : Mat) (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) :
    ∀ (r : ℕ) (rows : List RowT), R.pass s (R.ctx t u e cl X K) t u e lam cl X K r rows = R.passV s t e X K r rows
  | _, [] => rfl
  | r, row :: rows => by
    rw [pass, passV, pass_eq hp s t u e lam cl X K he (r + 1) rows, sumL_eq]
    congr 1
    rw [show (R.ctx t u e cl X K).tl = loTab R.p t from rfl,
      loTab_getD _ _ (show R.low X r < 2 ^ R.p from Nat.mod_lt _ (Nat.two_pow_pos _))]
    congr 1
    exact congrArg List.sum (List.map_congr_left fun τ _ => by rw [R.wv_eq hp t u e lam cl X K r he])

/-- **A repeated pattern's rows, evaluated** (the per-call sums, then one pass over the pattern's
rows `PR = rowsAt pat 0`). -/
theorem eval_eq (h : R.Fit) (hp : R.p ≤ 20) (s : Mat) (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) :
    R.pass s (R.ctx t u e cl X K) t u e lam cl X K 0 (rowsAt R.pat 0) = tm s t e X (rowsAt (R.gates K) K) := by
  rw [R.tm_rep h hp, R.pass_eq hp s t u e lam cl X K he]

end Rep


/-! ## Segments: irregular gates and repeated patterns -/

/-- A template segment: irregular gates, or a repeated pattern. -/
inductive SG where
  | irr (gs : List Gate)
  | rep (R : Rep)

/-- A segment's locals. -/
def SG.nl : SG → ℕ
  | .irr gs => nlocs gs
  | .rep R => R.n * nlocs R.padP

/-- A segment's gates, its first local at `K`. -/
def SG.gates : SG → ℕ → List Gate
  | .irr gs, _ => gs
  | .rep R, K => R.gates K

theorem SG.nlocs_gates (g : SG) (K : ℕ) : nlocs (g.gates K) = g.nl := by
  cases g with
  | irr gs => rfl
  | rep R => exact R.nlocs_gatesN K R.n

/-- The segments' locals. -/
def sgNl (l : List SG) : ℕ := (l.map SG.nl).sum

/-- **The segments' gates** from local `K`. -/
def sgGates : List SG → ℕ → List Gate
  | [], _ => []
  | g :: gs, K => g.gates K ++ sgGates gs (K + g.nl)

theorem nlocs_sgGates : ∀ (l : List SG) (K : ℕ), nlocs (sgGates l K) = sgNl l
  | [], _ => rfl
  | g :: gs, K => by rw [sgGates, nlocs_app, SG.nlocs_gates, nlocs_sgGates gs]; simp [sgNl]

theorem sgGates_append : ∀ (a b : List SG) (K : ℕ), sgGates (a ++ b) K = sgGates a K ++ sgGates b (K + sgNl a)
  | [], _, K => by simp [sgGates, sgNl]
  | g :: a, b, K => by
    rw [List.cons_append, sgGates, sgGates, sgGates_append a b, List.append_assoc]
    simp [sgNl, Nat.add_assoc]

/-! ## The segment builder -/

/-- **A segment builder**: from its first local, its segments and its result (as `GM`). -/
abbrev SM (α : Type) := ℕ → List SG × α

namespace SM
variable {α β : Type} {e : Env}

def ret (a : α) : SM α := fun _ => ([], a)

/-- `g`, then `f` of its result, whose locals follow `g`'s. -/
def bind (g : SM α) (f : α → SM β) : SM β := fun k =>
  ((g k).1 ++ (f (g k).2 (k + sgNl (g k).1)).1, (f (g k).2 (k + sgNl (g k).1)).2)

def map (g : SM α) (h : α → β) : SM β := fun k => ((g k).1, h (g k).2)

/-- An irregular gadget. -/
def lift (g : GM α) : SM α := fun k => ([.irr (g k).1], (g k).2)

/-- **`n` instances of the pattern `pat`** (built at local `0`, stride `2^p`), instance `s` reading its
inputs as `ph`'s forms at `s`; the result: each instance's result forms, substituted. -/
def rep (n p : ℕ) (pat : GM (List LinT)) (ph : Array Ph) : SM (ℕ → List LinT) := fun k =>
  ([.rep ⟨n, p, (pat 0).1, ph⟩], fun s => (pat 0).2.map (subW (Rep.σ ⟨n, p, (pat 0).1, ph⟩ s) (k + s * 2 ^ p)))

/-- **`g` computes `P`**: wherever its gates' equations hold at `e`, its result satisfies `P`. -/
def Ok (e : Env) (g : SM α) (P : α → Prop) : Prop := ∀ k, Eqns e (sgGates (g k).1 k) k → P (g k).2

theorem ok_ret {P : α → Prop} {a : α} (h : P a) : Ok e (ret a) P := fun _ _ => h

theorem ok_bind {g : SM α} {f : α → SM β} {P : α → Prop} {Q : β → Prop} (hg : Ok e g P)
    (hf : ∀ a, P a → Ok e (f a) Q) : Ok e (g.bind f) Q := fun k h => by
  simp only [bind, sgGates_append, Eqns.append, nlocs_sgGates] at h
  exact hf _ (hg k h.1) _ h.2

theorem ok_map {g : SM α} {h : α → β} {P : α → Prop} {Q : β → Prop} (hg : Ok e g P)
    (hh : ∀ a, P a → Q (h a)) : Ok e (g.map h) Q := fun k hk => hh _ (hg k hk)

theorem ok_mono {g : SM α} {P Q : α → Prop} (hg : Ok e g P) (h : ∀ a, P a → Q a) : Ok e g Q :=
  fun k hk => h _ (hg k hk)

theorem ok_lift {g : GM α} {P : α → Prop} (hg : GM.Ok e g P) : Ok e (lift g) P := fun k h => by
  simp only [lift, sgGates, SG.gates, List.append_nil] at h
  exact hg k h

theorem eqns_gatesN (R : Rep) (h : R.Fit) (K : ℕ) : ∀ m, Eqns e (R.gatesN m K) K →
    ∀ s < m, Eqns e (R.padP.map (Gate.sub (R.σ s) (K + s * 2 ^ R.p))) (K + s * 2 ^ R.p)
  | 0, _, s, hs => absurd hs (Nat.not_lt_zero _)
  | m + 1, hE, s, hs => by
    have e1 : R.gatesN (m + 1) K = R.gatesN m K ++ R.padP.map (Gate.sub (R.σ m) (K + m * 2 ^ R.p)) := by
      simp [Rep.gatesN, List.range_succ, List.flatMap_append]
    rw [e1, Eqns.append, R.nlocs_gatesN, R.nlocs_padP h] at hE
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · exact eqns_gatesN R h K m hE.1 s hs
    · exact hE.2

/-- **A repeated pattern computes `V s` at instance `s`**, if the pattern does at any wires whose
inputs are the placeholders' values. -/
theorem ok_rep {n p : ℕ} {pat : GM (List LinT)} {ph : Array Ph} (hfit : Rep.Fit ⟨n, p, (pat 0).1, ph⟩)
    (V : ℕ → List F)
    (hpat : ∀ s < n, ∀ e' : Env, e'.one = e.one → (∀ i, e'.inp i = (Rep.σ ⟨n, p, (pat 0).1, ph⟩ s i).ev e) →
      Eqns e' (pat 0).1 0 → (pat 0).2.map (LinT.ev e') = V s) :
    Ok e (rep n p pat ph) fun res => ∀ s < n, (res s).map (LinT.ev e) = V s := fun k hE s hs => by
  simp only [rep, sgGates, SG.gates, List.append_nil, Rep.gates] at hE
  have h1 := eqns_gatesN _ hfit k n hE s hs
  have h2 := (eqns_sub _ _ _ 0).1 (by simpa using h1)
  rw [Rep.padP, Eqns.append] at h2
  have := hpat s hs (pullE e (Rep.σ ⟨n, p, (pat 0).1, ph⟩ s) (k + s * 2 ^ p)) rfl (fun i => rfl) h2.1
  simp only [rep, List.map_map, Function.comp_def, subW_ev]
  exact this

end SM

/-! ## The segments' rows' value -/

instance (R : Rep) : Decidable R.Fit := inferInstanceAs (Decidable (_ ∧ _))

/-- **The segments' rows' value**: irregular rows sparse, a fitting repeated pattern in closed form
(`Rep.pass`). -/
def sgVal (s : Mat) (t u : ℕ → F) (e : Env) (lam : F) (cl : ℕ) : ℕ → ℕ → List SG → F
  | _, _, [] => 0
  | X, K, .irr gs :: l => tm s t e X (rowsAt gs K) + sgVal s t u e lam cl (X + nrows gs) (K + nlocs gs) l
  | X, K, .rep R :: l =>
    (if R.p ≤ 20 ∧ R.Fit then R.pass s (R.ctx t u e cl X K) t u e lam cl X K 0 (rowsAt R.pat 0)
     else tm s t e X (rowsAt (R.gates K) K)) +
      sgVal s t u e lam cl (X + R.n * nrows R.padP) (K + R.n * nlocs R.padP) l


theorem sgVal_eq (s : Mat) (t u : ℕ → F) (e : Env) (lam : F) (cl : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) :
    ∀ (X K : ℕ) (l : List SG), sgVal s t u e lam cl X K l = tm s t e X (rowsAt (sgGates l K) K)
  | _, _, [] => rfl
  | X, K, .irr gs :: l => by
    rw [sgVal, sgGates, rowsAt_append, tm_append, sgVal_eq s t u e lam cl he _ _ l, rowsAt_length]; rfl
  | X, K, .rep R :: l => by
    rw [sgVal, sgGates, rowsAt_append, tm_append, sgVal_eq s t u e lam cl he _ _ l, rowsAt_length]
    simp only [SG.gates, SG.nl, Rep.gates, R.nlocs_gatesN, R.nrows_gatesN]
    congr 1
    split_ifs with h
    · exact R.eval_eq h.2 h.1 s t u e lam cl X K he
    · rfl

end Tpl
end FR
