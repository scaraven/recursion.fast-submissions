-- G6: this module also holds the former modules `FRNodeRows4Arena`, `FRNodeRows4Pack`, `FRNodeRows4ArenaRows` (one section each, in import order).
import FRVIRTplEval
import FRNodeKinds4
import FRVIR4Mux

section G6_FRNodeRows4Arena

-- New for `flock-recursive` (PACK-4.4.1 §5.3; stage B2′, track L-circ): the arenas' closed forms.

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

end G6_FRNodeRows4Arena

section G6_FRNodeRows4Pack

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2, A.2, A.7; stage S-E13a, track L-circ):
-- the first rows of the pack map (S-N2's `Gap4`: the kind tie and `wf`).

/-!
# The pack rows' data: stream elements, the kind tie, the stream's constant elements

A child's trace is hashed by H as the stream `0x54 ‖ traceBytes tr` (`FRBlockStream`). Stream
element `e` (bytes `16e … 16e + 15`) is the H cell `sCell b0 e` of a stream whose first block is
`b0` (A.7, `elem_slot`). A linear row over cells can pin or equate **whole elements** only. Within
one trace starting at stream offset 1 the fields the rows need are whole elements:

* **element 0** is `0x54 ‖ enc64 119 ‖ "FRSEED0"`: the tag, the seed's length word, its query tag;
* every later item starts 16-aligned (`items_aligned`), so its first element is
  `enc64 |q| ‖ tag(q)` (`winB`): the length word and the query's 8-byte tag;
* **element 5** is `hdr[0…16)` (the seed query's bytes 71–86): `kind ‖ m ‖ 0¹⁴`, the constant the
  slot's program asserts (`seedOpsG`'s `const`).

**R-A′ (revision 4.4.1).** An aggregate's stream is `0x54 ‖ tr₁ ‖ sp ‖ tr₂ ‖ … ‖ sp ‖ tr_k` with
the 129-byte spacer entry `sp` (`FRAgg.spacerQ`), so segment `s` starts at `1 + s·strideB` with
`strideB = 64 · 24,238`: its elements are segment 0's shifted by `s·sBlk` blocks. Two elements per
spacer are not whole constants, because an entry ends with its (random) answer:
* the segment's **element 0** is the spacer answer's last byte, then `enc64 119 ‖ "FRSEED0"`: it is
  `seedM` plus 8 Boolean cells at bits 0–7 (`decRow`), so bytes 1–15 are pinned;
* the spacer's **element 6** is its query's last byte (`0`), then 15 answer bytes: it is 120
  Boolean cells at bits 8–127, so byte 0 is zero.
The spacer's elements 0–5 (`enc64 89 ‖ "FRABS000"`, the zero state, the message's first 48 zero
bytes) are whole constants (`spPin`). `headRows` are these rows; a stream's segment 0 has instead
its element 0 pinned whole (`seedW`).

This module has the data: `sCell`, the per-item element values (`winF`, `wfData`, the closed
`wfSeg`: every item's first element but the seed's), the pin row `pinRow`, the stream rows
`wfRows`, the head rows `headRows`, the kind constants `kConst` and the kind tie `kindRow`.
`FRNodeRows4` places them in the slots' link regions (`packRows4`); `FRNodeRows4PackSound` proves
what they give.
-/

namespace FR
namespace Rev4
open RecursionFast Circ

/-! ## Stream elements -/

/-- **The H cell of stream element `e`** of a stream whose first block is `b0`: message slot
`4 + e mod 4` of block `b0 + ⌊e/4⌋` (A.7). -/
def sCell (b0 e : ℕ) : ℕ := (b0 + e / 4) * 128 + 4 + e % 4

/-- An item's query tag (A.2): the seed's 7 bytes, every other query's 8. -/
def itemTag : Item → List UInt8
  | .seed => tagSeed
  | .absorb _ => tagAbs
  | .squeeze => tagSqz
  | .col i => tagCol i
  | .node i _ => tagNode i

/-- **The element where an item starts**, at stream offset `o`: the stream's tag if `o ≡ 1`
(the first item), the length word `enc64 |q|`, the query's tag. -/
def winB (o : ℕ) (it : Item) : List UInt8 :=
  (if o % 16 = 1 then [tagTrace] else []) ++ enc64 it.qlen ++ itemTag it

/-- The element whose bytes are `b` (zero-padded to 16). -/
def winFB (b : List UInt8) : F := F.ofBytes (Vector.ofFn fun r : Fin 16 => b.getD r 0)

/-- Its value (the byte list built once: `wfSeg` is a closed constant built at process start). -/
def winF (o : ℕ) (it : Item) : F := winFB (winB o it)

/-- **The pinned elements** of the items `its` from stream offset `o`: (element, value). -/
def wfData : ℕ → List Item → List (ℕ × F)
  | _, [] => []
  | o, it :: its => (o / 16, winF o it) :: wfData (o + it.slen) its

/-- **One trace's pinned elements past element 0** (`seq4`'s items from offset 1 but the seed's
element 0, which `headRows` binds: 8,782; a closed constant). -/
def wfSeg : List (ℕ × F) := (wfData 1 (itemsOf seq4)).tail

/-! ## The rows -/

/-- **`one · (x − c · one) = 0`**: at `one = 1`, cell `x` holds `c`. -/
def pinRow (one x : ℕ) (c : F) : Row := ⟨Lin.cell one, (Lin.cell x).sub ((Lin.cell one).smul c), []⟩

/-- **The `wf` rows of a stream at block `b0`**: each item's first element pinned. -/
def wfRows (one b0 : ℕ) : List Row := wfSeg.map fun p => pinRow one (sCell b0 p.1) p.2

/-! ## A segment's element 0 and the spacer (R-A′) -/

/-- **Element 0 of a stream's segment 0**: `0x54 ‖ enc64 119 ‖ "FRSEED0"`. -/
def seedW : F := winF 1 .seed

/-- Element 0 of a later segment with its byte 0 (the spacer answer's last byte) zero. -/
def seedM : F := winFB ([0] ++ enc64 119 ++ tagSeed)

/-- **The spacer entry's constant bytes**: `enc64 89 ‖ "FRABS000" ‖ 0^81` (`enc64 |q| ‖ q`,
`q = FRAgg.spacerQ`; `FRNodeRows4PackSound.spBytes_eq`). -/
def spBytes : List UInt8 := enc64 89 ++ tagAbs ++ List.replicate 81 0

/-- The spacer's whole constant element `j < 6`. -/
def spPin (j : ℕ) : F := winFB ((spBytes.drop (16 * j)).take 16)

/-- `c` is a bit: `c · (one − c) = 0`. -/
def boolRow (one c : ℕ) : Row := ⟨Lin.cell c, (Lin.cell one).sub (Lin.cell c), []⟩

/-- The bits `cell q` (`q < n`) at the element's bit positions `d + q`: `Σ_q x^(d+q) · cell q`. -/
def packAt (cell : ℕ → ℕ) (d n : ℕ) : Lin :=
  (List.range n).map fun q => (cell q, bitBasis ⟨(d + q) % 128, Nat.mod_lt _ (by norm_num)⟩)

/-- **`one · (x − c · one − bits) = 0`**: cell `x` is the constant `c` plus the packed bits. -/
def decRow (one x : ℕ) (c : F) (bits : Lin) : Row :=
  ⟨Lin.cell one, ((Lin.cell x).sub ((Lin.cell one).smul c)).sub bits, []⟩

/-- **The head rows of segment `s` of a stream, at block `b0`** (R-A′): for `s = 0` its element 0
pinned (`seedW`); for `s ≥ 1` the spacer before it (blocks `b0 − 2`, `b0 − 1`): elements 0–5
pinned, element 6 as 120 bits at positions 8–127 (`cell 0 … 119`), and the segment's element 0 as
`seedM` plus 8 bits at positions 0–7 (`cell 120 … 127`); 136 rows. -/
def headRows (one b0 s : ℕ) (cell : ℕ → ℕ) : List Row :=
  if s = 0 then [pinRow one (sCell b0 0) seedW]
  else (List.range 6).map (fun j => pinRow one (sCell (b0 - 2) j) (spPin j)) ++
    (List.range 128).map (fun q => boolRow one (cell q)) ++
    [decRow one (sCell (b0 - 2) 6) 0 (packAt cell 8 120),
     decRow one (sCell b0 0) seedM (packAt (fun q => cell (120 + q)) 0 8)]

/-- **Spacer `s`'s 128 bit cells** of signed child `σ` (`s ≥ 1`): L elements `11,264 + 128 (s − 1) + q`
of `σ`'s stride (S-E13b's `padRows` decomposition cells, which R-A′'s whole blocks free). -/
def spC (κ : NodeKind) (σ s q : ℕ) : ℕ := κ.lBase * 128 + σ * 2 ^ 14 + 11264 + 128 * (s - 1) + q

/-- **The kind constant** of index `ι` of group `G`: `hdr[0…16)` of a `G ι` proof, as the slot
program's seed check has it (`FRVIR4Mux.seedOpsG`). -/
def kConst (G : Grp) (ι : Kind) : F :=
  F.ofBytes (bytesAt (bytesOf ([(G ι).byte, (G ι).d.m.toUInt8] ++ List.replicate 46 0)) 0 16)

/-- **The kind tie**: stream element `h5` (`hdr[0…16)`) is `Σ_ι K_ι · s′_ι` over the slot's
selector copies `sel ι`. -/
def kindRow (one h5 : ℕ) (sel : Kind → ℕ) (G : Grp) : Row :=
  ⟨Lin.cell one, (Lin.cell h5).sub (Circ.kinds.map fun ι => (sel ι, kConst G ι)), []⟩

/-! ## Facts -/

theorem pinRow_holds {w : Asg} {one x : ℕ} {c : F} (hone : w one = 1) (h : (pinRow one x c).Holds w) :
    w x = c := by
  simp only [pinRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_smul, hone, one_mul, mul_one,
    Lin.ev_nil] at h
  exact sub_eq_zero.1 h

theorem pinRow_ctl (w : Asg) (one x : ℕ) (c : F) (hone : w one = 1) :
    (pinRow one x c).Holds w ↔ w x = c :=
  ⟨pinRow_holds hone, fun h => by
    simp only [pinRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_smul, hone, h, one_mul, mul_one,
      sub_self, Lin.ev_nil]⟩

theorem kindRow_holds {w : Asg} {one h5 : ℕ} {sel : Kind → ℕ} {G : Grp} (hone : w one = 1)
    (h : (kindRow one h5 sel G).Holds w) :
    w h5 = kConst G .L32 * w (sel .L32) + kConst G .P30 * w (sel .P30) + kConst G .N30 * w (sel .N30) := by
  simp only [kindRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, hone, one_mul, Lin.ev_nil] at h
  have h' := sub_eq_zero.1 h
  rw [h']
  simp [Circ.kinds, Lin.ev]
  ring

theorem wfData_length : ∀ (o : ℕ) (its : List Item), (wfData o its).length = its.length
  | _, [] => rfl
  | o, _ :: its => by simp [wfData, wfData_length _ its]

theorem wfSeg_length : wfSeg.length = 8782 := by
  rw [wfSeg, List.length_tail, wfData_length, itemsOf_seq4_length]

/-- The bytes an item's stream occupies. -/
def slenL (its : List Item) : ℕ := (its.map Item.slen).sum

/-- **Every pinned element lies inside the items' bytes.** -/
theorem wfData_lt : ∀ (o : ℕ) (its : List Item), ∀ q ∈ wfData o its, 16 * q.1 < o + slenL its := by
  intro o its
  induction its generalizing o with
  | nil => simp [wfData]
  | cons it its ih =>
    intro q hq
    simp only [wfData, List.mem_cons] at hq
    have hs : slenL (it :: its) = it.slen + slenL its := by simp [slenL]
    have : 0 < it.slen := by simp [Item.slen]
    rcases hq with rfl | hq
    · dsimp only; omega
    · have := ih (o + it.slen) q hq; omega

/-- (+) A pinned element of a segment lies below the segment's `segB` bytes. -/
theorem wfSeg_lt : ∀ p ∈ wfSeg, 16 * p.1 < N4c.segB := fun p hp => by
  have hb : 1 + slenL (itemsOf seq4) = N4c.segB := by
    rw [N4c.segB_eq, streamBytesOf, slenL]
    congr 2
  have := wfData_lt 1 (itemsOf seq4) p (List.mem_of_mem_tail hp)
  omega

theorem headRows_length (one b0 s : ℕ) (cell : ℕ → ℕ) :
    (headRows one b0 s cell).length = if s = 0 then 1 else 136 := by
  unfold headRows; split_ifs <;> simp

/-- (+) The kind constants' first byte is the kind byte (node group, segment group). -/
theorem kConst_byte (ι : Kind) :
    (F.toBytes (kConst nodeGrp ι))[0] = (nodeAt ι).byte ∧ (F.toBytes (kConst segGrp ι))[0] = (segAt ι).byte := by
  simp only [kConst, F.toBytes_ofBytes]
  cases ι <;> decide

/-- (−) The three node constants are distinct (so the tie fixes the index, not only the group). -/
theorem kConst_ne : kConst nodeGrp .L32 ≠ kConst nodeGrp .P30 ∧ kConst nodeGrp .P30 ≠ kConst nodeGrp .N30 ∧
    kConst segGrp .L32 ≠ kConst segGrp .N30 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  · have := congrArg (fun a => (F.toBytes a)[0]) h
    simp only [kConst, F.toBytes_ofBytes] at this
    revert this; decide

/-- (+) The first element of a trace's stream: `0x54 ‖ enc64 119 ‖ "FRSEED0"`; (−) a later
absorb's element has no `0x54`. -/
theorem winB_ctl : winB 1 .seed = [0x54] ++ enc64 119 ++ tagSeed ∧ (winB 1 .seed).length = 16 ∧
    (winB 160 (.absorb 128)).length = 16 ∧ (winB 160 (.absorb 128)).head? ≠ some 0x54 := by
  refine ⟨rfl, by decide, by decide, by decide⟩

end Rev4
end FR

end G6_FRNodeRows4Pack

section G6_FRNodeRows4ArenaRows

-- New for `flock-recursive` (PACK-4.4.1 §5.2–§5.3 as PK-M3 corrected; stage B2′, track L-circ).

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

end G6_FRNodeRows4ArenaRows

section G6_FRNodeRows4ArenaPlace

-- New for `flock-recursive` (PACK-4.4.1 §5.2 as PK-M3 corrected, B2′'s option (a); stage B2″, track
-- L-circ).

/-!
# The arenas placed: arena₁, the binding's rows and the bits in each slot's own region

PK-M3: the arenas sit in the region of the slot whose prototype reads them, at the **same
M-relative addresses in both prototypes**. B2″'s cell packing (`FRVIRTplSet.fitCells`, `packOf`)
freed the cells between the skeleton (277,102 cells in both prototypes) and the lowest template
instance (414,016 / 441,152; `logs/B2pp/cellfit-3.log`); B2′'s option (a) drops arena₂'s own cells
(the binding's rows write the consumers' import cells, `FRNodeRows4ArenaRows.a2Rows`).

| | M-relative cells (region `σ`: `+ σ·2^20`) | rows (region `σ`: `+ σ·2^20`) |
|---|---|---|
| arena₁, `arN = 4·chainLenOf seq4` elements | `[arA1, arA1 + arN)` = `[290,816, 387,752)` | `[arR1, arR1 + arN)` = `[852,992, 949,928)` |
| the binding (import cells: B3/B4's) | — | `[arR2, arR2 + arR2N)` = `[720,896, 852,992)` |
| bits, `arNb` | `[arBt, arBt + arNb)` = `[389,120, 397,440)` | `[arRb, arRb + arNb)` = `[950,272, 958,592)` |

The rows lie above both prototypes' rows (700,160 / 686,080 in the region, `logs/B2pp/nodedump4-run.log`)
and below the link region (`arena_rows`); the cells between the skeleton's and the templates'
(`arena_cells`; the gap itself is the compile's, checked on the dump: `logs/B2pp/arenafit.log`). Rows
and cells as placed are what B4 folds into `nodeIRows4`; nothing here changes a statement of the
soundness chain.

**What the placed rows give** (B3/B4's interface: an ask's answer and operand cells are stream
elements): `a1_cells4`, `arena_elem4`, `bit_cells4`; **their values**: `a1V4_eq`, `a2V4_eq`,
`bitV4_eq` (the automaton runs at the placed addresses, absolute cells: `κ.oneCell + ·`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval

/-! ## The addresses (M-relative, in a slot's own region) -/

/-- Arena₁'s elements: the segment's H chain, four a block (`4·chainLenOf seq4`: 96,944 at RSV2's
`|π|`; taken from the format, so that a format change moves it without a proof change). -/
def arN : ℕ := 4 * chainLenOf seq4
/-- `arN` at today's format (one rewrite: a proof that compares `arN` inside arithmetic makes the kernel
evaluate `chainLenOf seq4`, ≈ 2.4 s each). -/
theorem arN_eq : arN = 96944 := by rw [arN, chainLenOf_seq4.1]

/-- Arena₁'s first cell: above the skeleton's 277,102 cells (both prototypes), with a margin of 13.7 k
cells below and 16.6 k above the bits (`logs/B2pp/arenafit.log`). -/
def arA1 : ℕ := 290816
/-- The bits' first cell, after arena₁. -/
def arBt : ℕ := 389120
/-- The bits (PACK-4.4.1 §5.2: the 62 answers' 256 bits tied to 8,320 M Boolean cells). -/
def arNb : ℕ := 16384
/-- The binding's first row: above both prototypes' rows (700,160 in the region; a margin of 20.7 k
rows). -/
def arR2 : ℕ := 720896
/-- The binding's rows (index space: the levels' positions at their `2^a` strides, PACK-4.4.1
§5.2's 132,096 allocated, 85,946 used; SEG-R2: cut to the template rows' used extent, 154,333 with SIB's
siblings at prototype 1, `2^8`-aligned, so that band B of the segment's replay rows starts at the bits'
end). -/
def arR2N : ℕ := 154368
/-- Arena₁'s first row, after the binding's. -/
def arR1 : ℕ := arR2 + arR2N
/-- The bits' first row, after arena₁'s (aligned to `2^8`). -/
def arRb : ℕ := 972288

/-- **The rows are ordered and below the link region**: the binding, arena₁, the bits, then
`linkN = 2^15` rows (`FRNodeRows4`). -/
theorem arena_rows : arR2 + arR2N = arR1 ∧ arR1 + arN ≤ arRb ∧ arRb + arNb + 2 ^ 15 ≤ slotM4 := by
  -- (`rw` keeps the statement's form: `simp` would make the kernel evaluate `arN`)
  refine ⟨rfl, by rw [arN_eq]; decide, by decide⟩

/-- **The cells are ordered and inside the region**: arena₁, then the bits; arena₁ fits the automaton's
17 bits. -/
theorem arena_cells : arA1 + arN ≤ arBt ∧ arBt + arNb ≤ slotM4 ∧ arN ≤ 2 ^ 17 ∧ arNb ≤ 2 ^ 14 := by
  refine ⟨by rw [arN_eq]; decide, by decide, by rw [arN_eq]; decide, by decide⟩

/-! ## The rows of slot `σ` (absolute cells, M's rows) -/

/-- **Arena₁'s rows of slot `σ`** (stream block `b0`: `packB κ σ`'s). -/
def a1Rows4 (κ : NodeKind) (σ b0 : ℕ) : List (ℕ × Row) :=
  a1Rows κ.oneCell (κ.oneCell + σ * slotM4 + arA1) (σ * slotM4 + arR1) b0 arN

/-- **The binding's rows of a level in slot `σ`** (the level's import cells and rows relative to the
region: `v.C`, `v.B`). -/
def a2Rows4 (κ : NodeKind) (σ : ℕ) (v : ALv) : List (ℕ × Row) :=
  a2Rows κ.oneCell (κ.oneCell + σ * slotM4 + arA1) (κ.oneCell + σ * slotM4) (σ * slotM4 + arR2) v

/-- **The bits' rows of slot `σ`.** -/
def bitRows4 (κ : NodeKind) (σ : ℕ) : List (ℕ × Row) :=
  bitRows (κ.oneCell + σ * slotM4 + arBt) (σ * slotM4 + arRb) arNb

/-- A level's rows lie in the binding's range (`B`, its positions at the `2^a` stride). -/
def LvIn (v : ALv) : Prop := v.S ≤ 2 ^ v.a ∧ v.B + v.t * 2 ^ v.a ≤ arR2N

/-! ## What they give -/

/-- **Arena₁'s cell `e` of slot `σ` is stream element `e`.** -/
theorem a1_cells4 {w : Asg} {κ : NodeKind} {σ b0 : ℕ} (hone : w κ.oneCell = 1)
    (h : ∀ p ∈ a1Rows4 κ σ b0, p.2.Holds w) {e : ℕ} (he : e < arN) :
    w (κ.oneCell + σ * slotM4 + arA1 + e) = w (sCell b0 e) :=
  a1_cells hone h he

/-- **An import cell of slot `σ` is its stream element**: position `p`, element `q` of a level `v`
is element `E + S·p + q` of the slot's stream (`sCell b0 ·`). -/
theorem arena_elem4 {w : Asg} {κ : NodeKind} {σ b0 : ℕ} {v : ALv} (hone : w κ.oneCell = 1)
    (h1 : ∀ p ∈ a1Rows4 κ σ b0, p.2.Holds w) (h2 : ∀ p ∈ a2Rows4 κ σ v, p.2.Holds w) {p q : ℕ}
    (hp : p < v.t) (hq : q < v.S) (hN : v.E + v.S * p + q < arN) :
    w (κ.oneCell + σ * slotM4 + v.C + p * 2 ^ v.c + v.off q) = w (sCell b0 (v.E + v.S * p + q)) :=
  arena_elem hone h1 h2 hp hq hN

/-- **The bits' cells of slot `σ` are bits.** -/
theorem bit_cells4 {w : Asg} {κ : NodeKind} {σ : ℕ} (h : ∀ p ∈ bitRows4 κ σ, p.2.Holds w) {j : ℕ}
    (hj : j < arNb) : w (κ.oneCell + σ * slotM4 + arBt + j) = 0 ∨ w (κ.oneCell + σ * slotM4 + arBt + j) = 1 :=
  bit_cells h hj

/-- (+) Element 5 of slot 1's arena₁ is the cell `oneCell + 2^20 + 290,821`, its row `2^20 + 875,269`;
(−) not slot 0's. -/
theorem a1Rows4_ctl (κ : NodeKind) :
    (a1Rows4 κ 1 0)[5]?.map (fun p => (p.1, p.2.b)) =
      some (2 ^ 20 + 875269, (Lin.cell (κ.oneCell + 2 ^ 20 + 290821)).sub (Lin.cell (sCell 0 5))) ∧
    (a1Rows4 κ 1 0)[5]?.map Prod.fst ≠ some 875269 := by
  have h : 5 < arN := by rw [arN_eq]; norm_num
  simp only [a1Rows4, a1Rows, List.getElem?_map, List.getElem?_range h, Option.map_some, cpRow, slotM4,
    arA1, arR1, arR2, arR2N]
  refine ⟨by norm_num [add_assoc], by norm_num⟩

/-! ## Their values at the placed addresses (absolute cells; `n`, `m` the matrix's row and cell
coordinates) -/

/-- Arena₁'s value of slot `σ`: three automaton runs over 17 bits (`a1V`). -/
def a1V4 (n m : ℕ) (t u : ℕ → F) (κ : NodeKind) (σ b0 : ℕ) : F3 :=
  a1V n m 17 t u κ.oneCell (κ.oneCell + σ * slotM4 + arA1) (σ * slotM4 + arR1) b0 arN

theorem a1V4_eq {n m : ℕ} (hn : 17 ≤ n) (hm : 22 ≤ m) (t u : ℕ → F) (κ : NodeKind) (σ b0 : ℕ) :
    a1V4 n m t u κ σ b0 = (rowsVal (RingHom.id F) .a n m t u (a1Rows4 κ σ b0),
      rowsVal (RingHom.id F) .b n m t u (a1Rows4 κ σ b0), rowsVal (RingHom.id F) .c n m t u (a1Rows4 κ σ b0)) :=
  a1V_eq hn (by omega) (by omega) t u _ _ _ _ _ arena_cells.2.2.1

/-- The binding's value of a level in slot `σ` (`a2V`: the import side once per level, one run per
position on arena₁'s side). -/
def a2V4 (n m k k' : ℕ) (t u : ℕ → F) (κ : NodeKind) (σ : ℕ) (v : ALv) : F :=
  a2V n m k k' t u (κ.oneCell + σ * slotM4 + arA1) (κ.oneCell + σ * slotM4) (σ * slotM4 + arR2) v

theorem a2V4_eq {n m k k' : ℕ} (hk : k ≤ n) (hm : k ≤ m) (t u : ℕ → F) (κ : NodeKind) (σ : ℕ) (v : ALv)
    (hS : v.S ≤ 2 ^ k) (ha : v.a ≤ n) (hc : v.c ≤ m) (hk1 : k' ≤ n - v.a) (hk2 : k' ≤ m - v.c)
    (ht : v.t ≤ 2 ^ k') (hR : 2 ^ v.a ∣ σ * slotM4 + arR2 + v.B) (hC : 2 ^ v.c ∣ κ.oneCell + σ * slotM4 + v.C)
    (hv : LvIn v) (hoff : ∀ q < v.S, v.off q < 2 ^ v.c) :
    a2V4 n m k k' t u κ σ v = rowsVal (RingHom.id F) .b n m t u (a2Rows4 κ σ v) :=
  a2V_eq hk hm t u κ.oneCell _ _ _ v hS ha hc hk1 hk2 ht hR hC hv.1 hoff

/-- The bits' value of slot `σ`: one automaton run over 14 bits. -/
def bitV4 (n m : ℕ) (t u : ℕ → F) (κ : NodeKind) (σ : ℕ) : F3 :=
  bitV n m 14 t u (κ.oneCell + σ * slotM4 + arBt) (σ * slotM4 + arRb) arNb

theorem bitV4_eq {n m : ℕ} (hn : 14 ≤ n) (hm : 14 ≤ m) (t u : ℕ → F) (κ : NodeKind) (σ : ℕ) :
    bitV4 n m t u κ σ = (rowsVal (RingHom.id F) .a n m t u (bitRows4 κ σ),
      rowsVal (RingHom.id F) .b n m t u (bitRows4 κ σ), rowsVal (RingHom.id F) .c n m t u (bitRows4 κ σ)) :=
  bitV_eq hn hm t u _ _ _ arena_cells.2.2.2

end Rev4
end FR

end G6_FRNodeRows4ArenaPlace
