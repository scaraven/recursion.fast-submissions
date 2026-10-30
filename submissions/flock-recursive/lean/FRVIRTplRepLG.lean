-- New for `flock-recursive` (track CF2): shifted diagonal sums of bit products by a carry automaton.
import FRVIRTplChain
import FRVIRTplEval

/-!
# Shifted diagonal sums by a carry automaton

`PF f L x` is a product of per-bit factors over `L` bits (`0` from `2^L`); with
`f l b = if b then t l else 1 − t l` it is `gN L t x`. **`GS fa fb L n A B`** splits
`Σ_{j<n} PF fa L (A + j) · PF fb L (B + j)` at the lowest bit (`j = 2j' + d`): two terms, each the
lowest bit's factors times the same sum one bit up (**`GS_eq`**). At every bit the arguments
`(n, A, B)` reachable from one start are within one of `(⌊n/2^l⌋, ⌊A/2^l⌋, ⌊B/2^l⌋)`, so a
memoized evaluation has at most 8 states per bit and start.

**`autoG`** is that evaluation as gates: per bit (top bit first), the four factor products and two
products per state; **`ok_autoG`**: each start state's form is its `GS` value.
-/

namespace FR
namespace Tpl
open Finset Circ TEval

/-! ## The sums -/

/-- A product of per-bit factors over `L` bits (`0` from `2^L`). -/
def PF (f : ℕ → Bool → F) (L x : ℕ) : F := if x < 2 ^ L then ∏ l ∈ range L, f l (x.testBit l) else 0

/-- The factors one bit up. -/
def shF (f : ℕ → Bool → F) : ℕ → Bool → F := fun l b => f (l + 1) b

theorem PF_zero (f : ℕ → Bool → F) (x : ℕ) : PF f 0 x = if x = 0 then 1 else 0 := by
  unfold PF; simp [Nat.lt_one_iff]

theorem PF_succ (f : ℕ → Bool → F) (L x : ℕ) :
    PF f (L + 1) x = f 0 (decide (x % 2 = 1)) * PF (shF f) L (x / 2) := by
  unfold PF shF
  have h : x < 2 ^ (L + 1) ↔ x / 2 < 2 ^ L := by
    rw [pow_succ, Nat.div_lt_iff_lt_mul (by norm_num)]
  by_cases hx : x / 2 < 2 ^ L
  · rw [if_pos (h.2 hx), if_pos hx, prod_range_succ', mul_comm]
    congr 1
    · rw [Nat.testBit_zero]
    · exact prod_congr rfl fun l _ => by rw [show x / 2 = x / 2 ^ 1 by norm_num, Nat.testBit_div_two_pow]
  · rw [if_neg (mt h.1 hx), if_neg hx, mul_zero]

/-- `gN` is `PF` with `eq` factors. -/
def eqF (t : ℕ → F) : ℕ → Bool → F := fun l b => if b then t l else 1 - t l

theorem gN_PF (L : ℕ) (t : ℕ → F) (x : ℕ) : gN L t x = PF (eqF t) L x := rfl

/-- A sum over `j < n` by parity. -/
theorem sum_parity (g : ℕ → F) : ∀ n : ℕ,
    ∑ j ∈ range n, g j = ∑ j ∈ range ((n + 1) / 2), g (2 * j) + ∑ j ∈ range (n / 2), g (2 * j + 1)
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, sum_parity g n]
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [show (m + m + 1 + 1) / 2 = m + 1 by omega, show (m + m + 1) / 2 = m by omega,
        show (m + m) / 2 = m by omega, sum_range_succ, show 2 * m = m + m by ring]
      ring
    · rw [show (2 * m + 1 + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
        show (2 * m + 1) / 2 = m by omega, sum_range_succ (fun j => g (2 * j + 1))]
      ring

/-- **The automaton's recursion** (`Σ_{j<n} PF fa L (A+j) · PF fb L (B+j)`, `GS_eq`). -/
def GS (fa fb : ℕ → Bool → F) : ℕ → ℕ → ℕ → ℕ → F
  | 0, n, A, B => if 0 < n ∧ A = 0 ∧ B = 0 then 1 else 0
  | L + 1, n, A, B =>
    fa 0 (decide (A % 2 = 1)) * fb 0 (decide (B % 2 = 1)) * GS (shF fa) (shF fb) L ((n + 1) / 2) (A / 2) (B / 2) +
    fa 0 (decide ((A + 1) % 2 = 1)) * fb 0 (decide ((B + 1) % 2 = 1)) *
      GS (shF fa) (shF fb) L (n / 2) ((A + 1) / 2) ((B + 1) / 2)

theorem GS_zero (fa fb : ℕ → Bool → F) (n A B : ℕ) :
    GS fa fb 0 n A B = ∑ j ∈ range n, PF fa 0 (A + j) * PF fb 0 (B + j) := by
  rw [GS]
  simp only [PF_zero]
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_range_succ']
    have h0 : ∑ j ∈ range n, (if A + (j + 1) = 0 then (1 : F) else 0) * (if B + (j + 1) = 0 then 1 else 0) = 0 :=
      sum_eq_zero fun j _ => by rw [if_neg (by omega), zero_mul]
    rw [h0, zero_add, Nat.add_zero, Nat.add_zero]
    by_cases hA : A = 0 <;> by_cases hB : B = 0 <;> simp [hA, hB]

theorem GS_eq (L : ℕ) : ∀ (fa fb : ℕ → Bool → F) (n A B : ℕ),
    GS fa fb L n A B = ∑ j ∈ range n, PF fa L (A + j) * PF fb L (B + j) := by
  induction L with
  | zero => exact GS_zero
  | succ L ih =>
    intro fa fb n A B
    rw [GS, ih, ih, sum_parity _ n, mul_sum, mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine sum_congr rfl fun j _ => ?_
      have e1 : (A + 2 * j) % 2 = A % 2 := by omega
      have e2 : (B + 2 * j) % 2 = B % 2 := by omega
      have e3 : (A + 2 * j) / 2 = A / 2 + j := by omega
      have e4 : (B + 2 * j) / 2 = B / 2 + j := by omega
      rw [PF_succ, PF_succ, e1, e2, e3, e4]
      ring
    · refine sum_congr rfl fun j _ => ?_
      have e1 : (A + (2 * j + 1)) % 2 = (A + 1) % 2 := by omega
      have e2 : (B + (2 * j + 1)) % 2 = (B + 1) % 2 := by omega
      have e3 : (A + (2 * j + 1)) / 2 = (A + 1) / 2 + j := by omega
      have e4 : (B + (2 * j + 1)) / 2 = (B + 1) / 2 + j := by omega
      rw [PF_succ, PF_succ, e1, e2, e3, e4]
      ring

/-! ## The automaton as gates -/

/-- A state `(n, A, B)`. -/
abbrev St := ℕ × ℕ × ℕ

/-- The next bit's states (`d = 0`, `d = 1`). -/
def ch0 (s : St) : St := ((s.1 + 1) / 2, s.2.1 / 2, s.2.2 / 2)
def ch1 (s : St) : St := (s.1 / 2, (s.2.1 + 1) / 2, (s.2.2 + 1) / 2)

/-- The states one bit up (without repeats). -/
def kids (S : List St) : List St := (S.flatMap fun s => [ch0 s, ch1 s]).dedup

theorem ch0_kids {S : List St} {s : St} (h : s ∈ S) : ch0 s ∈ kids S :=
  List.mem_dedup.2 (List.mem_flatMap.2 ⟨s, h, by simp⟩)

theorem ch1_kids {S : List St} {s : St} (h : s ∈ S) : ch1 s ∈ kids S :=
  List.mem_dedup.2 (List.mem_flatMap.2 ⟨s, h, by simp⟩)

/-- A state's form from the states' forms. -/
def look (S : List St) (vs : List LinT) (s : St) : LinT := vs.getD (S.idxOf s) []

theorem look_ev {S : List St} {vs : List LinT} {v : St → F} (h : vs.map (LinT.ev e) = S.map v) {s : St}
    (hs : s ∈ S) : (look S vs s).ev e = v s := by
  have hl : vs.length = S.length := by simpa using congrArg List.length h
  have hi : S.idxOf s < S.length := List.idxOf_lt_length_of_mem hs
  have := congrArg (fun l => l.getD (S.idxOf s) 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (hl ▸ hi),
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some, List.getElem_idxOf] at this
  rw [look, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ hi), Option.getD_some]
  exact this

/-- The four factor products of the lowest bit, indexed `2 bA + bB`. -/
def prs (qa qb : Bool → LinT) : GM (List LinT) :=
  GM.mapL (fun bb : Bool × Bool => mulF (qa bb.1) (qb bb.2)) [(false, false), (false, true), (true, false), (true, true)]

def prAt (ps : List LinT) (x y : Bool) : LinT := ps.getD (2 * x.toNat + y.toNat) []

/-- **The automaton's gates** (factor forms `qa l b`, `qb l b`; `L` bits; start states `S`): the
states' forms, in `S`'s order. -/
def autoG (qa qb : ℕ → Bool → LinT) : ℕ → List St → GM (List LinT)
  | 0, S => GM.ret (S.map fun s => if 0 < s.1 ∧ s.2.1 = 0 ∧ s.2.2 = 0 then C 1 else [])
  | L + 1, S =>
    (autoG (fun l => qa (l + 1)) (fun l => qb (l + 1)) L (kids S)).bind fun vs =>
    (prs (qa 0) (qb 0)).bind fun ps =>
    GM.mapL (fun s =>
      (mulF (prAt ps (decide (s.2.1 % 2 = 1)) (decide (s.2.2 % 2 = 1))) (look (kids S) vs (ch0 s))).bind fun t0 =>
      (mulF (prAt ps (decide ((s.2.1 + 1) % 2 = 1)) (decide ((s.2.2 + 1) % 2 = 1))) (look (kids S) vs (ch1 s))).map
        fun t1 => t0 ++ t1) S

variable {e : Env}

theorem ok_prs {qa qb : Bool → LinT} {fa fb : Bool → F} (ha : ∀ b, (qa b).ev e = fa b) (hb : ∀ b, (qb b).ev e = fb b) :
    GM.Ok e (prs qa qb) fun ps => ∀ x y, (prAt ps x y).ev e = fa x * fb y := by
  refine GM.ok_mono (GM.ok_mapL (E := LinT.ev e) (v := fun bb : Bool × Bool => fa bb.1 * fb bb.2) _ fun bb _ =>
    GM.ok_mono (ok_mulF _ _) fun o ho => by rw [ho, ha, hb]) fun ps hps x y => ?_
  have h4 : ps.length = 4 := by simpa using congrArg List.length hps
  match ps, h4 with
  | [p0, p1, p2, p3], _ =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hps
    cases x <;> cases y <;> simp [prAt, hps]

/-- **The automaton computes `GS`** at every start state. -/
theorem ok_autoG (h1 : e.one = 1) : ∀ (L : ℕ) (qa qb : ℕ → Bool → LinT) (fa fb : ℕ → Bool → F) (S : List St),
    (∀ l b, (qa l b).ev e = fa l b) → (∀ l b, (qb l b).ev e = fb l b) →
      GM.Ok e (autoG qa qb L S) fun vs => vs.map (LinT.ev e) = S.map fun s => GS fa fb L s.1 s.2.1 s.2.2
  | 0, qa, qb, fa, fb, S, _, _ => GM.ok_ret (by
    simp only [List.map_map]
    refine List.map_congr_left fun s _ => ?_
    simp only [Function.comp_apply, GS]
    split_ifs <;> simp [h1])
  | L + 1, qa, qb, fa, fb, S, ha, hb => by
    refine GM.ok_bind (ok_autoG h1 L _ _ (shF fa) (shF fb) (kids S) (fun l b => ha (l + 1) b)
      (fun l b => hb (l + 1) b)) fun vs hvs => GM.ok_bind (ok_prs (ha 0) (hb 0)) fun ps hps => ?_
    refine GM.ok_mapL _ fun s hs => GM.ok_bind (ok_mulF _ _) fun t0 ht0 =>
      GM.ok_map (ok_mulF _ _) fun t1 ht1 => ?_
    rw [ev_append, ht0, ht1, hps, hps, look_ev hvs (ch0_kids hs), look_ev hvs (ch1_kids hs), GS]
    rfl

end Tpl
end FR
