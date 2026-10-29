-- New for `flock-recursive` (PACK-4.4.1 §5.3; stage B2′, track L-circ): the arenas' closed forms.
import FRVIRTplEval

/-!
# The shifted diagonal: `Σ_{e<N} P(a + e)·Q(c + e)` in `O(k)` products

PACK-4.4.1 §5.3. The pack map's arena rows are diagonals: row `R + e` reads cells `A + e` and
`H(4·b0 + e)` (arena₁), or `X_p + q` (arena₂'s window at a non-aligned base). Their matrices' MLEs
are sums `Σ_{e<N} P(a + e)·Q(c + e)` where `P`, `Q` are **bit products** `pB n f x = Π_{l<n} f_l(x_l)`
on the cube (`gN` is one: `gN_pB`; a range sum takes `f ≡ 1`). Splitting `e` by its lowest bit,

`Σ_{e<N} P(a+e)·Q(c+e) = Σ_{e₀ ∈ {0,1}} f₀((a+e₀) mod 2)·g₀((c+e₀) mod 2) · Σ_{e'<N'} P'(a'+e')·Q'(c'+e')`

with `a' = ⌊(a+e₀)/2⌋`, `c' = ⌊(c+e₀)/2⌋`, `N' = ⌊(N+1−e₀)/2⌋` (`dRec`, `dRec_eq`). Over `k` levels the
pairs `(a', c', N')` take at most 8 values (the two carries and the range's borrow), so merging the
equal ones (`dRun`, a **carry automaton**) costs `O(k)` products: the shift-by-constant diagonal
and the shift-window automaton of §5.3 are this one function. `dRun_eq`: it is the sum. The kernel
never evaluates a layout: the arena rows' values are stated through these lemmas, and the
evaluator runs `dRun` at process time.
-/

namespace FR
namespace TEval
open Finset

variable {R : Type*} [CommRing R]

/-! ## Bit products -/

/-- **A bit product** on the cube: `Π_{l<n} f l (bit l of x)`, `0` off the cube. -/
def pB (n : ℕ) (f : ℕ → ℕ → R) (x : ℕ) : R :=
  if x < 2 ^ n then ∏ l ∈ range n, f l (if x.testBit l then 1 else 0) else 0

/-- The factors of `eq(t, ·)`: `t l` at a one, `1 − t l` at a zero. -/
def eqF (t : ℕ → R) (l b : ℕ) : R := if b = 1 then t l else 1 - t l

theorem gN_pB (n : ℕ) (t : ℕ → R) (x : ℕ) : gN n t x = pB n (eqF t) x := by
  unfold gN eqN pB eqF
  split_ifs
  · exact Finset.prod_congr rfl fun l _ => by by_cases h : x.testBit l <;> simp [h]
  · rfl

theorem bit_mod (x : ℕ) : (if x.testBit 0 then 1 else 0) = x % 2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [Nat.testBit_zero, h]

/-- **One level**: `pB (n+1) f x = f 0 (x mod 2) · pB n f' ⌊x/2⌋`. -/
theorem pB_succ (n : ℕ) (f : ℕ → ℕ → R) (x : ℕ) :
    pB (n + 1) f x = f 0 (x % 2) * pB n (fun l => f (l + 1)) (x / 2) := by
  unfold pB
  have hlt : x < 2 ^ (n + 1) ↔ x / 2 < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num), pow_succ]
  by_cases h : x / 2 < 2 ^ n
  · rw [if_pos (hlt.2 h), if_pos h, Finset.prod_range_succ', mul_comm, bit_mod]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← Nat.testBit_div_two]
  · rw [if_neg (fun h' => h (hlt.1 h')), if_neg h, mul_zero]

theorem pB_zero (f : ℕ → ℕ → R) (x : ℕ) : pB 0 f x = if x = 0 then 1 else 0 := by
  unfold pB; simp

/-! ## The sum, split by parity -/

theorem sum_range_parity {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ N : ℕ, ∑ e ∈ range N, f e =
      ∑ e ∈ range ((N + 1) / 2), f (2 * e) + ∑ e ∈ range (N / 2), f (2 * e + 1)
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, sum_range_parity f N]
    rcases Nat.even_or_odd' N with ⟨m, rfl | rfl⟩
    · have h1 : (2 * m + 1) / 2 = m := by omega
      have h2 : 2 * m / 2 = m := by omega
      have h3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [h1, h2, h3, Finset.sum_range_succ (fun e => f (2 * e))]; abel
    · have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      have h3 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
      rw [h1, h2, h3, Finset.sum_range_succ (fun e => f (2 * e + 1))]; abel

/-! ## The recursion -/

/-- The levels above the first. -/
def up (f : ℕ → ℕ → R) : ℕ → ℕ → R := fun l => f (l + 1)

/-- **The shifted diagonal, by the lowest bit of `e`** (`k` levels; `dRec_eq`). -/
def dRec : ℕ → ℕ → ℕ → (ℕ → ℕ → R) → (ℕ → ℕ → R) → ℕ → ℕ → ℕ → R
  | 0, nt, nu, f, g, a, c, N => if 0 < N then pB nt f a * pB nu g c else 0
  | k + 1, nt, nu, f, g, a, c, N =>
    f 0 (a % 2) * g 0 (c % 2) * dRec k (nt - 1) (nu - 1) (up f) (up g) (a / 2) (c / 2) ((N + 1) / 2) +
    f 0 ((a + 1) % 2) * g 0 ((c + 1) % 2) *
      dRec k (nt - 1) (nu - 1) (up f) (up g) ((a + 1) / 2) ((c + 1) / 2) (N / 2)

/-- **`dRec` is the diagonal sum** for `N ≤ 2^k`, `k ≤ nt`, `k ≤ nu`. -/
theorem dRec_eq : ∀ (k nt nu : ℕ) (f g : ℕ → ℕ → R) (a c N : ℕ), k ≤ nt → k ≤ nu → N ≤ 2 ^ k →
    dRec k nt nu f g a c N = ∑ e ∈ range N, pB nt f (a + e) * pB nu g (c + e)
  | 0, nt, nu, f, g, a, c, N, _, _, hN => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hN) with rfl | rfl <;> simp [dRec]
  | k + 1, nt, nu, f, g, a, c, N, ht, hu, hN => by
    obtain ⟨nt, rfl⟩ : ∃ m, nt = m + 1 := ⟨nt - 1, by omega⟩
    obtain ⟨nu, rfl⟩ : ∃ m, nu = m + 1 := ⟨nu - 1, by omega⟩
    rw [sum_range_parity, dRec, Nat.add_sub_cancel, Nat.add_sub_cancel,
      dRec_eq k nt nu _ _ _ _ _ (by omega) (by omega) (by rw [pow_succ] at hN; omega),
      dRec_eq k nt nu _ _ _ _ _ (by omega) (by omega) (by rw [pow_succ] at hN; omega),
      Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun e _ => ?_ <;> rw [pB_succ, pB_succ] <;> unfold up
    · rw [show (a + 2 * e) % 2 = a % 2 by omega, show (c + 2 * e) % 2 = c % 2 by omega,
        show (a + 2 * e) / 2 = a / 2 + e by omega, show (c + 2 * e) / 2 = c / 2 + e by omega]
      ring
    · rw [show (a + (2 * e + 1)) % 2 = (a + 1) % 2 by omega, show (c + (2 * e + 1)) % 2 = (c + 1) % 2 by omega,
        show (a + (2 * e + 1)) / 2 = (a + 1) / 2 + e by omega,
        show (c + (2 * e + 1)) / 2 = (c + 1) / 2 + e by omega]
      ring

theorem dRec_zero : ∀ (k nt nu : ℕ) (f g : ℕ → ℕ → R) (a c : ℕ), dRec k nt nu f g a c 0 = 0
  | 0, _, _, _, _, _, _ => by simp [dRec]
  | k + 1, nt, nu, f, g, a, c => by simp [dRec, dRec_zero k]

/-! ## The automaton: merged levels -/

/-- A state: its coefficient, the shifts `a`, `c` and the range `N` left. -/
abbrev DSt (R : Type*) := R × ℕ × ℕ × ℕ

/-- Add a state to a list, merging it into an equal one (`a`, `c`, `N`); a state of range `0` is
dropped (its sum is empty). -/
def dIns (x : DSt R) : List (DSt R) → List (DSt R)
  | [] => if x.2.2.2 = 0 then [] else [x]
  | y :: ys => if y.2 = x.2 then (y.1 + x.1, y.2) :: ys else y :: dIns x ys

/-- One state's two children, merged into `acc`. -/
def dStep1 (f g : ℕ → ℕ → R) (acc : List (DSt R)) (x : DSt R) : List (DSt R) :=
  dIns (x.1 * (f 0 ((x.2.1 + 1) % 2) * g 0 ((x.2.2.1 + 1) % 2)), (x.2.1 + 1) / 2, (x.2.2.1 + 1) / 2,
      x.2.2.2 / 2)
    (dIns (x.1 * (f 0 (x.2.1 % 2) * g 0 (x.2.2.1 % 2)), x.2.1 / 2, x.2.2.1 / 2, (x.2.2.2 + 1) / 2) acc)

/-- One level of the states: each state's two children, merged. -/
def dStep (f g : ℕ → ℕ → R) (L : List (DSt R)) : List (DSt R) := L.foldl (dStep1 f g) []

/-- **The automaton**: `k` merged levels, then the states' high parts by the lookups `ft`, `fu`
(`pB` of the levels above `k`: `dRun_eq`). -/
def dRun (ft fu : ℕ → R) : ℕ → (ℕ → ℕ → R) → (ℕ → ℕ → R) → List (DSt R) → R
  | 0, _, _, L => (L.map fun x => if 0 < x.2.2.2 then x.1 * (ft x.2.1 * fu x.2.2.1) else 0).sum
  | k + 1, f, g, L => dRun ft fu k (up f) (up g) (dStep f g L)

/-- The states' total: `Σ coef · dRec`. -/
def dTot (k nt nu : ℕ) (f g : ℕ → ℕ → R) (L : List (DSt R)) : R :=
  (L.map fun x => x.1 * dRec k nt nu f g x.2.1 x.2.2.1 x.2.2.2).sum

theorem dTot_ins (k nt nu : ℕ) (f g : ℕ → ℕ → R) (x : DSt R) :
    ∀ L : List (DSt R), dTot k nt nu f g (dIns x L) = x.1 * dRec k nt nu f g x.2.1 x.2.2.1 x.2.2.2 + dTot k nt nu f g L
  | [] => by
    unfold dIns; split_ifs with h
    · simp [dTot, h, dRec_zero]
    · simp [dTot]
  | y :: ys => by
    unfold dIns; split_ifs with h
    · simp only [dTot, List.map_cons, List.sum_cons]; rw [h]; ring
    · have ih := dTot_ins k nt nu f g x ys
      simp only [dTot, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; ring

theorem dTot_step (k nt nu : ℕ) (f g : ℕ → ℕ → R) (L : List (DSt R)) :
    dTot k (nt - 1) (nu - 1) (up f) (up g) (dStep f g L) = dTot (k + 1) nt nu f g L := by
  suffices h : ∀ acc, dTot k (nt - 1) (nu - 1) (up f) (up g) (L.foldl (dStep1 f g) acc) =
      dTot k (nt - 1) (nu - 1) (up f) (up g) acc + dTot (k + 1) nt nu f g L by
    rw [dStep, h]; simp [dTot]
  induction L with
  | nil => intro acc; simp [dTot]
  | cons x L ih =>
    intro acc
    rw [List.foldl_cons, ih, dStep1, dTot_ins, dTot_ins]
    simp only [dTot, List.map_cons, List.sum_cons, dRec]
    ring

/-- **The automaton is the states' total** (the lookups are the high parts' bit products). -/
theorem dRun_eq (ft fu : ℕ → R) : ∀ (k nt nu : ℕ) (f g : ℕ → ℕ → R) (L : List (DSt R)),
    (∀ x, ft x = pB (nt - k) (fun l => f (k + l)) x) → (∀ x, fu x = pB (nu - k) (fun l => g (k + l)) x) →
    dRun ft fu k f g L = dTot k nt nu f g L
  | 0, nt, nu, f, g, L, hf, hu => by
    simp only [dRun, dTot, dRec]
    congr 1; refine List.map_congr_left fun x _ => ?_
    split_ifs <;> simp [hf, hu]
  | k + 1, nt, nu, f, g, L, hf, hu => by
    rw [dRun, dRun_eq ft fu k (nt - 1) (nu - 1) (up f) (up g) (dStep f g L), dTot_step]
    · intro x; rw [hf]; unfold up; congr 1
      · omega
      · funext l; congr 1; omega
    · intro x; rw [hu]; unfold up; congr 1
      · omega
      · funext l; congr 1; omega

/-- **The shifted diagonal by the automaton**: for `N ≤ 2^k`, `k ≤ nt`, `k ≤ nu`,
`dRun ft fu k f g [(1, a, c, N)] = Σ_{e<N} pB nt f (a + e) · pB nu g (c + e)`. -/
theorem diag_eq (ft fu : ℕ → R) {k nt nu : ℕ} (f g : ℕ → ℕ → R) (a c N : ℕ) (ht : k ≤ nt) (hu : k ≤ nu)
    (hN : N ≤ 2 ^ k) (hft : ∀ x, ft x = pB (nt - k) (fun l => f (k + l)) x)
    (hfu : ∀ x, fu x = pB (nu - k) (fun l => g (k + l)) x) :
    dRun ft fu k f g [(1, a, c, N)] = ∑ e ∈ range N, pB nt f (a + e) * pB nu g (c + e) := by
  rw [dRun_eq ft fu k nt nu f g _ hft hfu, dTot, List.map_singleton, List.sum_singleton, one_mul,
    dRec_eq k nt nu f g a c N ht hu hN]

/-! ## Controls -/

/-- A bit product by lists (the controls' independent reading of `pB`). -/
def pBL (n : ℕ) (f : ℕ → ℕ → ℤ) (x : ℕ) : ℤ :=
  if x < 2 ^ n then ((List.range n).map fun l => f l (if x.testBit l then 1 else 0)).prod else 0

/-- (+) Over `ℤ`, with `f l b = 2 + b`, `g l b = 3 + 5·b` on 3 levels and the high parts' lookups
(`[x = 0]`), the automaton is the sum `Σ_{e<5} P(3 + e)·Q(6 + e)` (which leaves the cube at
`6 + e ≥ 8`); (−) it differs from the unshifted `c = 0`. -/
theorem diag_ctl :
    dRun (fun x => if x = 0 then (1 : ℤ) else 0) (fun x => if x = 0 then 1 else 0) 3
        (fun _ b => 2 + (b : ℤ)) (fun _ b => 3 + 5 * (b : ℤ)) [(1, 3, 6, 5)] =
      ((List.range 5).map fun e => pBL 3 (fun _ b => 2 + (b : ℤ)) (3 + e) *
        pBL 3 (fun _ b => 3 + 5 * (b : ℤ)) (6 + e)).sum ∧
    dRun (fun x => if x = 0 then (1 : ℤ) else 0) (fun x => if x = 0 then 1 else 0) 3
        (fun _ b => 2 + (b : ℤ)) (fun _ b => 3 + 5 * (b : ℤ)) [(1, 3, 6, 5)] ≠
      dRun (fun x => if x = 0 then (1 : ℤ) else 0) (fun x => if x = 0 then 1 else 0) 3
        (fun _ b => 2 + (b : ℤ)) (fun _ b => 3 + 5 * (b : ℤ)) [(1, 3, 0, 5)] := by
  decide

end TEval
end FR
