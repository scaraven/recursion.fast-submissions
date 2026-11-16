-- New for lvm2 E2F (slice S1, E2F-Q): `E2` twin instructions in QA1's template language (`LvmQSumcheckCore`),
-- the base the front gadgets are ported on.
import LvmQSumcheckCore
import LvmE2QFieldCorrect

/-!
# `E2` templates

An `E2` operand of a template is a pair of sources `(re, im)` (`S2`); `e2I f xs` is the twin pair of
instructions `e2 f false`, `e2 f true` on them (`LvmLoopIR`). On any fixed point of a template (`Fix`):

* **`e2I_val`**: the twin pair at position `n` holds the `E2` value of `f` at its operands' values;
* `mul2I a b d = a·b + d`, `lin2I k k' a b = a + k·b + k'` (`k ∈ K`, `k' ∈ E2`), `add2I`;
* **`horner2`**: a Horner chain `acc ↦ acc·x + c` in `E2` (the sumcheck round's evaluation at a challenge),
  `horner2_val`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- An `E2` operand: the sources of its two `K` coordinates. -/
abbrev S2 := Src × Src

/-- The value of an `E2` operand on a template's values. -/
def S2.val (xv : Src → FE) (vs : List FE) (s : S2) : FE2 := ⟨(s.1.val xv vs).c₀, (s.2.val xv vs).c₀⟩

/-- The `K` operands of `E2` operands (`re`, `im` each). -/
def s2Args (xs : List S2) : List Src := xs.flatMap fun p ↦ [p.1, p.2]

/-- **The twin pair** of `f` on `xs`. -/
def e2I (f : E2Fn) (xs : List S2) : List Ins :=
  [⟨.e2 f false, .K, s2Args xs⟩, ⟨.e2 f true, .K, s2Args xs⟩]

/-- The `E2` value a twin pair at position `n` holds: its two cells. -/
def twinVal (V : List FE) (n : Nat) : FE2 := ⟨(V.getD n 0).c₀, (V.getD (n + 1) 0).c₀⟩

/-- **A twin pair's value** on a fixed point. -/
theorem e2I_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {n : Nat} {f : E2Fn}
    {xs : List S2} (hseg : Seg ins n (e2I f xs)) (hlen : n + 2 ≤ ins.length) :
    twinVal V n = f.val fun o ↦ ((s2Args xs).getD o default |>.val xv V).c₀ := by
  have h0 := fix_at hF (n := n) (by omega) (i := ⟨.e2 f false, .K, s2Args xs⟩)
    (by have := hseg 0 (by simp [e2I]); simpa [e2I] using this) (by simp)
  have h1 := fix_at hF (n := n + 1) (by omega) (i := ⟨.e2 f true, .K, s2Args xs⟩)
    (by have := hseg 1 (by simp [e2I]); simpa [e2I] using this) (by simp)
  apply FE2.ext_coord
  · simp only [twinVal, FE2.coord_false]; rw [h0]; rfl
  · simp only [twinVal, FE2.coord_true]; rw [h1]; rfl

/-- `a·b + d` in `E2`. -/
def mul2I (a b d : S2) : List Ins := e2I .mul [a, b, d]

/-- `a + k·b + k'` in `E2` (`k ∈ K`, `k' ∈ E2`). -/
def lin2I (k : FK) (k' : FE2) (a b : S2) : List Ins := e2I (.lin k k'.re k'.im) [a, b]

/-- `a + b` in `E2`. -/
def add2I (a b : S2) : List Ins := lin2I 1 0 a b

theorem mul2I_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {n : Nat} {a b d : S2}
    (hseg : Seg ins n (mul2I a b d)) (hlen : n + 2 ≤ ins.length) :
    twinVal V n = a.val xv V * b.val xv V + d.val xv V :=
  e2I_val hF hseg hlen

theorem lin2I_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {n : Nat} {k : FK}
    {k' : FE2} {a b : S2} (hseg : Seg ins n (lin2I k k' a b)) (hlen : n + 2 ≤ ins.length) :
    twinVal V n = a.val xv V + FE2.ofK k * b.val xv V + k' :=
  e2I_val hF hseg hlen

/-- The twin pair at `n` as an operand of a later instruction. -/
def locS2 (n : Nat) : S2 := (.loc n, .loc (n + 1))

theorem locS2_val (xv : Src → FE) (V : List FE) (n : Nat) : (locS2 n).val xv V = twinVal V n := rfl

/-- **A Horner chain in `E2`** from position `n`: `acc ↦ acc·x + c` for each coefficient `c`, starting at `h`. -/
def horner2 (x : S2) : Nat → S2 → List S2 → List Ins
  | _, _, [] => []
  | n, h, c :: cs => mul2I h x c ++ horner2 x (n + 2) (locS2 n) cs

theorem horner2_length (x : S2) (n : Nat) (h : S2) (cs : List S2) :
    (horner2 x n h cs).length = 2 * cs.length := by
  induction cs generalizing n h with
  | nil => rfl
  | cons c cs ih => simp only [horner2, List.length_append, ih]; simp [mul2I, e2I]; omega

/-- A segment's prefix. -/
theorem seg_prefix {ins : List Ins} {n : Nat} {A B : List Ins} (h : Seg ins n (A ++ B)) : Seg ins n A := by
  intro i hi
  rw [h i (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
    ← List.getD_eq_getElem?_getD]

/-- Where a Horner chain's value is. -/
def hornerSrc2 (n : Nat) (h : S2) (cs : List S2) : S2 := if cs = [] then h else locS2 (n + 2 * cs.length - 2)

/-- **The Horner chain's value.** -/
theorem horner2_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) (x : S2) :
    ∀ (cs : List S2) (n : Nat) (h : S2), Seg ins n (horner2 x n h cs) → n + 2 * cs.length ≤ ins.length →
      (hornerSrc2 n h cs).val xv V = (cs.map (S2.val xv V)).foldl (fun acc c ↦ acc * x.val xv V + c) (h.val xv V)
  | [], _, _, _, _ => rfl
  | c :: cs, n, h, hseg, hlen => by
    have hm : (mul2I h x c).length = 2 := rfl
    have h0 := mul2I_val hF (n := n) (a := h) (b := x) (d := c) (seg_prefix hseg) (by simp at hlen; omega)
    have hs : Seg ins (n + 2) (horner2 x (n + 2) (locS2 n) cs) := by
      have := seg_sub hseg (mul2I h x c) (horner2 x (n + 2) (locS2 n) cs) rfl
      rwa [hm] at this
    have ih := horner2_val hF x cs (n + 2) (locS2 n) hs (by simp at hlen; omega)
    rw [locS2_val, h0] at ih
    rw [List.map_cons, List.foldl_cons, ← ih]
    simp only [hornerSrc2, List.length_cons]
    by_cases hc : cs = []
    · subst hc; simp [locS2_val, h0]
    · simp only [hc, if_false, reduceCtorEq]
      congr 2 <;> omega

end Lvm.Q1
