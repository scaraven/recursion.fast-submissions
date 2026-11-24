-- New for lvm6 (WP MA): multiaffine weights, coordinate by coordinate, for WP S's
-- `StackClaim6.Multiaffine` (W1 F-3), and `RetAll` (every value a program returns satisfies `Q`).
import Lvm6StmtPhase
import Lvm6MbProg
import LvmE2VBaseLemmas

/-!
# Multiaffine weights

WP S's `StackClaim6.Multiaffine μ c` says a claim's weight is, at every point of `μ` coordinates,
the multilinear extension of its values on the cube. Every phase builds its weights from
equality products, slot selectors and linear combinations; this module proves those generic
facts once.

* **`IsMA μ f`**: `f` is affine in its first coordinate on points of length `μ`, and its two
  restrictions (first coordinate `0`, `1`) are `IsMA (μ - 1)`. **`IsMA.sum_eq`**: such an `f` is
  the multilinear extension of its cube values, so `IsMA.multiaffine` gives S's predicate.
* Closure: constants, sums, scalar multiples, agreement on points of length `μ` (`IsMA.congr`),
  products over disjoint coordinates (`IsMA.mul_split`: the first `k` and the rest), `take`/`drop`.
* Instances: `eqPt a`, `eqEvalF a`, `eqAtF · n`, `eqAboveG p` (every length), a block weight
  `eqAboveG p x * w (x.take p.variableCount)` (`isMA_above`), claims `(eqPt a, v)`.
* **`RetAll Q p`** (WP ASM's definition on `lvm6/ASM-ma`, `Lvm6AsmRing`, same statement and name:
  one copy only at integration, e.g. `Lvm6AsmRing` imports this light module) with `bind`, `of_forall`, `after`, `ret`, and `mono` (new here); `RetAll.ret` is exactly the
  hypothesis of `Spec.retInv`.
-/

set_option autoImplicit false

namespace Lvm6

open LeanVM.Parameters LeanVM.Protocol.EndToEnd.Front Lvm.E2V Finset
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-! ## Multiaffine, coordinate by coordinate -/

/-- **`f` is multiaffine on `μ` coordinates**: affine in the first coordinate (characteristic 2:
`f(t, p) = (1 + t) f(0, p) + t f(1, p)`), and so are its two restrictions on the rest. -/
def IsMA : ℕ → (List E2 → E2) → Prop
  | 0, _ => True
  | μ + 1, f => (∀ t p, p.length = μ → f (t :: p) = (1 + t) * f (0 :: p) + t * f (1 :: p)) ∧
      IsMA μ (fun p ↦ f (0 :: p)) ∧ IsMA μ (fun p ↦ f (1 :: p))

theorem two_eq_zero_E2 : (2 : E2) = 0 := CharTwo.two_eq_zero

theorem boolPt_succ (μ x : ℕ) :
    boolPt (μ + 1) x = (if x % 2 = 1 then 1 else 0) :: boolPt μ (x / 2) := by
  simp only [boolPt, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp [Nat.testBit_zero]
  · refine List.map_congr_left fun i _ ↦ ?_
    simp [Function.comp, Nat.testBit_succ]

theorem eqPt_cons (r t : E2) (a p : List E2) :
    eqPt (r :: a) (t :: p) = (r * t + (1 + r) * (1 + t)) * eqPt a p := by
  simp only [eqPt, List.zipWith_cons_cons, List.prod_cons]

theorem sum_range_two_mul {M : Type} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ x ∈ range (2 * n), g x = ∑ y ∈ range n, (g (2 * y) + g (2 * y + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- **A multiaffine function is the multilinear extension of its cube values.** -/
theorem IsMA.sum_eq : ∀ {μ : ℕ} {f : List E2 → E2}, IsMA μ f → ∀ pt : List E2, pt.length = μ →
    f pt = ∑ x : Fin (2 ^ μ), f (boolPt μ x) * eqPt (boolPt μ x) pt
  | 0, f, _, pt, hp => by
    rw [List.length_eq_zero_iff.mp hp]
    simp [boolPt, eqPt]
  | μ + 1, f, h, pt, hp => by
    obtain ⟨haff, h0, h1⟩ := h
    obtain ⟨t, p, rfl⟩ : ∃ t p, pt = t :: p := by
      cases pt with
      | nil => simp at hp
      | cons t p => exact ⟨t, p, rfl⟩
    have hp' : p.length = μ := by simpa using hp
    have key : ∀ y : ℕ,
        f (boolPt (μ + 1) (2 * y)) * eqPt (boolPt (μ + 1) (2 * y)) (t :: p) +
          f (boolPt (μ + 1) (2 * y + 1)) * eqPt (boolPt (μ + 1) (2 * y + 1)) (t :: p) =
        (1 + t) * (f (0 :: boolPt μ y) * eqPt (boolPt μ y) p) +
          t * (f (1 :: boolPt μ y) * eqPt (boolPt μ y) p) := by
      intro y
      have e0 : (2 * y) % 2 = 0 := by omega
      have e1 : (2 * y + 1) % 2 = 1 := by omega
      have d0 : 2 * y / 2 = y := by omega
      have d1 : (2 * y + 1) / 2 = y := by omega
      rw [boolPt_succ, boolPt_succ, e0, e1, d0, d1, eqPt_cons, eqPt_cons]
      rw [if_neg (show (0 : ℕ) ≠ 1 by norm_num), if_pos (show (1 : ℕ) = 1 from rfl)]
      linear_combination (f (1 :: boolPt μ y) * (1 + t) * eqPt (boolPt μ y) p) * two_eq_zero_E2
    have e0 : f (0 :: p) = ∑ x : Fin (2 ^ μ), f (0 :: boolPt μ x) * eqPt (boolPt μ x) p :=
      IsMA.sum_eq h0 p hp'
    have e1 : f (1 :: p) = ∑ x : Fin (2 ^ μ), f (1 :: boolPt μ x) * eqPt (boolPt μ x) p :=
      IsMA.sum_eq h1 p hp'
    rw [haff t p hp', e0, e1, mul_sum, mul_sum,
      ← sum_add_distrib,
      Fin.sum_univ_eq_sum_range (fun y : ℕ ↦ (1 + t) * (f (0 :: boolPt μ y) * eqPt (boolPt μ y) p) +
        t * (f (1 :: boolPt μ y) * eqPt (boolPt μ y) p)) (2 ^ μ),
      Fin.sum_univ_eq_sum_range (fun x : ℕ ↦ f (boolPt (μ + 1) x) * eqPt (boolPt (μ + 1) x) (t :: p))
        (2 ^ (μ + 1)), pow_succ', sum_range_two_mul]
    exact sum_congr rfl fun y _ ↦ (key y).symm

/-- **S's predicate** from `IsMA`. -/
theorem IsMA.multiaffine {μ : ℕ} {c : StackClaim6} (h : IsMA μ c.1) : c.Multiaffine μ :=
  fun pt hp ↦ h.sum_eq pt hp

/-! ## Closure -/

/-- Agreement on the points of length `μ`. -/
theorem IsMA.congr : ∀ {μ : ℕ} {f g : List E2 → E2}, IsMA μ f →
    (∀ p : List E2, p.length = μ → f p = g p) → IsMA μ g
  | 0, _, _, _, _ => trivial
  | μ + 1, f, g, h, hfg => by
    obtain ⟨haff, h0, h1⟩ := h
    refine ⟨fun t p hp ↦ ?_, h0.congr fun p hp ↦ hfg _ (by simp [hp]),
      h1.congr fun p hp ↦ hfg _ (by simp [hp])⟩
    rw [← hfg _ (by simp [hp]), ← hfg _ (by simp [hp]), ← hfg _ (by simp [hp])]
    exact haff t p hp

theorem isMA_const (c : E2) : ∀ μ : ℕ, IsMA μ (fun _ ↦ c)
  | 0 => trivial
  | μ + 1 => ⟨fun t _ _ ↦ by linear_combination (-(t * c)) * two_eq_zero_E2,
      isMA_const c μ, isMA_const c μ⟩

theorem IsMA.add : ∀ {μ : ℕ} {f g : List E2 → E2}, IsMA μ f → IsMA μ g →
    IsMA μ (fun p ↦ f p + g p)
  | 0, _, _, _, _ => trivial
  | μ + 1, _, _, ⟨hf, hf0, hf1⟩, ⟨hg, hg0, hg1⟩ =>
    ⟨fun t p hp ↦ by beta_reduce; rw [hf t p hp, hg t p hp]; ring, hf0.add hg0, hf1.add hg1⟩

theorem IsMA.smul (a : E2) : ∀ {μ : ℕ} {f : List E2 → E2}, IsMA μ f → IsMA μ (fun p ↦ a * f p)
  | 0, _, _ => trivial
  | μ + 1, _, ⟨hf, hf0, hf1⟩ => ⟨fun t p hp ↦ by beta_reduce; rw [hf t p hp]; ring, hf0.smul a, hf1.smul a⟩

theorem isMA_listSum {α : Type} {μ : ℕ} (F : α → List E2 → E2) :
    ∀ l : List α, (∀ a ∈ l, IsMA μ (F a)) → IsMA μ (fun p ↦ (l.map fun a ↦ F a p).sum)
  | [], _ => by simpa using isMA_const 0 μ
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (isMA_listSum F l fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

/-- **Products over disjoint coordinates**: `f` on the first `k`, `g` on the other `m`. -/
theorem IsMA.mul_split {m : ℕ} {g : List E2 → E2} (hg : IsMA m g) (k : ℕ) :
    ∀ {f : List E2 → E2}, IsMA k f → IsMA (k + m) (fun p ↦ f (p.take k) * g (p.drop k)) := by
  induction k with
  | zero =>
    intro f _
    rw [Nat.zero_add]
    exact (hg.smul (f [])).congr fun p _ ↦ by simp
  | succ k ih =>
    intro f hf
    obtain ⟨haff, h0, h1⟩ := hf
    rw [show k + 1 + m = (k + m) + 1 by omega]
    refine ⟨fun t p hp ↦ ?_, (ih h0).congr fun p _ ↦ ?_, (ih h1).congr fun p _ ↦ ?_⟩
    · simp only [List.take_succ_cons, List.drop_succ_cons]
      rw [haff t (p.take k) (by simp [hp])]
      ring
    · simp only [List.take_succ_cons, List.drop_succ_cons]
    · simp only [List.take_succ_cons, List.drop_succ_cons]

/-- A function of the first `k` coordinates. -/
theorem IsMA.take {k μ : ℕ} {f : List E2 → E2} (hf : IsMA k f) (hk : k ≤ μ) :
    IsMA μ (fun p ↦ f (p.take k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, μ = k + m := ⟨μ - k, by omega⟩
  exact (IsMA.mul_split (isMA_const 1 m) k hf).congr fun p _ ↦ mul_one _

/-- A function of the coordinates after the first `k`. -/
theorem IsMA.drop {k m : ℕ} {g : List E2 → E2} (hg : IsMA m g) :
    IsMA (k + m) (fun p ↦ g (p.drop k)) :=
  (IsMA.mul_split hg k (isMA_const 1 k)).congr fun p _ ↦ one_mul _

/-- A function multiaffine at every length, of the first `k` coordinates, at any length. -/
theorem isMA_take {f : List E2 → E2} (hf : ∀ ν, IsMA ν f) (k μ : ℕ) :
    IsMA μ (fun p ↦ f (p.take k)) := by
  rcases le_total k μ with hk | hk
  · exact (hf k).take hk
  · exact (hf μ).congr fun p hp ↦ by rw [List.take_of_length_le (by omega)]

/-! ## Equality products -/

/-- A product of coordinate factors, each affine in the point's coordinate. -/
theorem isMA_zipProd (e : E2 → E2 → E2) (he : ∀ r t, e r t = (1 + t) * e r 0 + t * e r 1) :
    ∀ (μ : ℕ) (a : List E2), IsMA μ (fun p ↦ (List.zipWith e a p).prod)
  | 0, _ => trivial
  | μ + 1, [] => by simpa using isMA_const 1 (μ + 1)
  | μ + 1, r :: a => by
    refine ⟨fun t p _ ↦ ?_, ?_, ?_⟩
    · simp only [List.zipWith_cons_cons, List.prod_cons]
      rw [he r t]
      ring
    · simpa only [List.zipWith_cons_cons, List.prod_cons] using
        (isMA_zipProd e he μ a).smul (e r 0)
    · simpa only [List.zipWith_cons_cons, List.prod_cons] using
        (isMA_zipProd e he μ a).smul (e r 1)

theorem isMA_eqPt (a : List E2) (μ : ℕ) : IsMA μ (fun p ↦ eqPt a p) :=
  isMA_zipProd _ (fun r t ↦ by linear_combination (-(t * (1 + r))) * two_eq_zero_E2) μ a

private theorem foldl_mul_one (l : List E2) (a : E2) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

theorem isMA_eqEvalF (a : List E2) (μ : ℕ) : IsMA μ (fun p ↦ eqEvalF a p) :=
  (isMA_zipProd (fun x z ↦ 1 + x + z) (fun r t ↦ by
    linear_combination (-(t * r) - t) * two_eq_zero_E2) μ a).congr fun p _ ↦ by
    rw [eqEvalF, foldl_mul_one, one_mul]

theorem isMA_eqAtF : ∀ (μ n : ℕ), IsMA μ (fun p ↦ eqAtF p n)
  | 0, _ => trivial
  | μ + 1, n => by
    refine ⟨fun t p _ ↦ ?_, ?_, ?_⟩
    · simp only [eqAtF]
      split_ifs
      · ring
      · linear_combination (-(t * eqAtF p (n / 2))) * two_eq_zero_E2
    · simpa only [eqAtF] using (isMA_eqAtF μ (n / 2)).smul (if n % 2 = 1 then 0 else 1 + 0)
    · simpa only [eqAtF] using (isMA_eqAtF μ (n / 2)).smul (if n % 2 = 1 then 1 else 1 + 1)

/-- A claim `(eq(a, ·), v)` is multiaffine (claim 0 of §6.1, the tree's and the sponge's). -/
theorem eqClaim_multiaffine (μ : ℕ) (a : List E2) (v : E2) :
    StackClaim6.Multiaffine μ (fun pt ↦ eqPt a pt, v) :=
  (isMA_eqPt a μ).multiaffine

/-- Claims `(eq(a, ·), v)` from a list of points and values. -/
theorem eqClaims_multiaffine (μ : ℕ) (l : List (List E2 × E2)) :
    ∀ c ∈ l.map (fun c ↦ ((fun pt ↦ eqPt c.1 pt), c.2)), StackClaim6.Multiaffine μ c := by
  intro c hc
  obtain ⟨c', _, rfl⟩ := List.mem_map.mp hc
  exact eqClaim_multiaffine μ c'.1 c'.2

/-! ## Slot selectors -/

open Lvm6.Mb in
theorem isMA_eqAboveG (pl : LeanVM.Protocol.Verifier.Placement) (μ : ℕ) :
    IsMA μ (eqAboveG pl) := by
  rcases le_total pl.variableCount μ with hk | hk
  · obtain ⟨m, rfl⟩ : ∃ m, μ = pl.variableCount + m := ⟨μ - pl.variableCount, by omega⟩
    refine (IsMA.drop (k := pl.variableCount)
      (isMA_eqEvalF (selPtF (pl.index >>> pl.variableCount) m) m)).congr fun p hp ↦ ?_
    simp only [eqAboveG, hp, Nat.add_sub_cancel_left]
  · refine (isMA_const (eqEvalF (selPtF (pl.index >>> pl.variableCount) 0) ([] : List E2))
      μ).congr fun p hp ↦ ?_
    simp only [eqAboveG, hp, List.drop_eq_nil_of_le (show p.length ≤ pl.variableCount by omega),
      show μ - pl.variableCount = 0 by omega]

open Lvm6.Mb in
/-- **A block weight** `eq_above(p, x)·w(x[..ν])` (`BClaimG.onStack`, `recClaim`) is multiaffine
at every length when `w` is. -/
theorem isMA_above (pl : LeanVM.Protocol.Verifier.Placement) {w : List E2 → E2}
    (hw : ∀ ν, IsMA ν w) (μ : ℕ) :
    IsMA μ (fun x ↦ eqAboveG pl x * w (x.take pl.variableCount)) := by
  rcases le_total pl.variableCount μ with hk | hk
  · obtain ⟨m, rfl⟩ : ∃ m, μ = pl.variableCount + m := ⟨μ - pl.variableCount, by omega⟩
    refine (IsMA.mul_split (isMA_eqEvalF (selPtF (pl.index >>> pl.variableCount) m) m)
      pl.variableCount (hw pl.variableCount)).congr fun p hp ↦ ?_
    simp only [eqAboveG, hp, Nat.add_sub_cancel_left]
    ring
  · refine ((hw μ).smul (eqEvalF (selPtF (pl.index >>> pl.variableCount) 0) ([] : List E2))).congr
      fun p hp ↦ ?_
    simp only [eqAboveG, hp, List.drop_eq_nil_of_le (show p.length ≤ pl.variableCount by omega),
      show μ - pl.variableCount = 0 by omega, List.take_of_length_le (show p.length ≤
        pl.variableCount by omega)]

/-! ## Every returned value -/

/-- Every value `p` can return satisfies `Q`. -/
def RetAll {α : Type} (Q : α → Prop) : VerifierProgram α → Prop
  | .ret a => Q a
  | .fail => True
  | .read k => ∀ x, RetAll Q (k x)
  | .sample k => ∀ c, RetAll Q (k c)
  | .grind _ k => RetAll Q k
  | .commit _ _ k => RetAll Q k
  | .query _ _ k => ∀ r, RetAll Q (k r)

section RetAll

variable {α β : Type}

theorem RetAll.bind {Q : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : RetAll (fun a ↦ RetAll Q (f a)) p) : RetAll Q (p >>= f) := by
  show RetAll Q (p.bind f)
  induction p with
  | ret a => exact hp
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact ih hp
  | query i ps k ih => exact fun r ↦ ih r (hp r)

theorem RetAll.of_forall {Q : α → Prop} (hQ : ∀ a, Q a) : ∀ p : VerifierProgram α, RetAll Q p
  | .ret a => hQ a
  | .fail => trivial
  | .read k => fun x ↦ RetAll.of_forall hQ (k x)
  | .sample k => fun c ↦ RetAll.of_forall hQ (k c)
  | .grind _ k => RetAll.of_forall hQ k
  | .commit _ _ k => RetAll.of_forall hQ k
  | .query _ _ k => fun r ↦ RetAll.of_forall hQ (k r)

theorem RetAll.after {Q : α → Prop} {p q : VerifierProgram α} (hp : RetAll Q p) {l : List Ev}
    (h : p.after l = some q) : RetAll Q q := by
  induction l generalizing p with
  | nil => cases p <;> (cases h; exact hp)
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | exact ih (hp _) h
      | (refine ih ?_ h; exact hp)
      | (split_ifs at h; refine ih ?_ h; exact hp)

theorem RetAll.mono {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) :
    ∀ {p : VerifierProgram α}, RetAll P p → RetAll Q p
  | .ret a, h => hPQ a h
  | .fail, _ => trivial
  | .read k, h => fun x ↦ RetAll.mono hPQ (h x)
  | .sample k, h => fun c ↦ RetAll.mono hPQ (h c)
  | .grind _ k, h => RetAll.mono hPQ (p := k) h
  | .commit _ _ k, h => RetAll.mono hPQ (p := k) h
  | .query _ _ k, h => fun r ↦ RetAll.mono hPQ (h r)

/-- A returned value satisfies `Q` (for `Spec.retInv`). -/
theorem RetAll.ret {Q : α → Prop} {p : VerifierProgram α} (hp : RetAll Q p) (l : List Ev) (a : α)
    (h : p.after l = some (.ret a)) : Q a :=
  RetAll.after hp h

end RetAll

end Lvm6
